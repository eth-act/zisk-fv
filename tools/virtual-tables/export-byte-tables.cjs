#!/usr/bin/env node
// Execute the pinned PIL builder, observing the byte tables' fixed columns
// before virtual-table lowering discards the AIR. No row-building algorithm is
// duplicated here; this file only reads what the compiler produced.
//
// The two tables are far too large to retain row-by-row (BinaryTable alone is
// 2^22 + 2^20 + 2^18 = 5,505,024 rows), so the artifact is one SHA-256 per
// opcode block over the canonical row encoding. Blocks are consecutive runs of
// the OP fixed column, which is exactly how both PIL tables lay themselves out.
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');

// Column order is the `lookup_proves` tuple of each table, so the hashed
// encoding is the tuple the consumer AIRs actually look up.
const TABLES = {
    BinaryTable: {
        columns: ['POS_IND', 'OP', 'A', 'B', 'CIN', 'C', 'FLAGS'],
        pil: 'binary/pil/binary_table.pil',
        size: 'BINARY_TABLE_SIZE',
    },
    BinaryExtensionTable: {
        columns: ['OP', 'OFFSET', 'A', 'B', 'C0', 'C1', 'FLAGS'],
        pil: 'binary/pil/binary_extension_table.pil',
        size: 'BINARY_EXTENSION_TABLE_SIZE',
    },
};

function checkProductionCall(ziskRoot, air, sizeConst) {
    const production = fs.readFileSync(path.join(ziskRoot, 'pil/zisk.pil'), 'utf8')
        .replace(/\/\*[\s\S]*?\*\//g, '').replace(/\/\/[^\n]*/g, '');
    const calls = production.match(new RegExp(`\\bvirtual\\s+${air}\\s*\\([^;]*;`, 'g')) || [];
    const expected = new RegExp(`^virtual\\s+${air}\\s*\\(\\s*${sizeConst}\\s*\\)\\s*;$`);
    if (calls.length !== 1 || !expected.test(calls[0])) {
        throw new Error(`production ${air} invocation changed; update the extraction harness`);
    }
}

function exportTable(compilerRoot, ziskRoot, proofmanRoot, air) {
    const spec = TABLES[air];
    if (!spec) throw new Error(`unknown table ${air}`);
    checkProductionCall(ziskRoot, air, spec.size);

    const compile = require(path.join(compilerRoot, 'src/compiler.js'));
    const { F1Field } = require(path.join(compilerRoot, 'node_modules/ffjavascript'));
    const Context = require(path.join(compilerRoot, 'src/context.js'));
    const prime = 0xffffffff00000001n;

    let blocks;
    let rowCount;
    // A zero-multiplicity consumer lets the standard library finish the
    // isolated table. It provides no fixed column and alters none.
    const zeros = spec.columns.map(() => '0').join(', ');
    const busId = air === 'BinaryTable' ? 'BINARY_TABLE_ID' : 'BINARY_EXTENSION_TABLE_ID';
    const source = `require "std_direct.pil"
require "${spec.pil}"
airtemplate TableConsumer(const int N = 256) {
    lookup_assumes(${busId}, [${zeros}], sel: 0);
}
airgroup Zisk { virtual ${air}(${spec.size}); TableConsumer(); }
`;
    const result = compile(new F1Field(prime), source, null, {
        compileFromString: true,
        protoOut: false,
        includePaths: [
            path.join(ziskRoot, 'pil'), path.join(ziskRoot, 'state-machines'),
            path.join(proofmanRoot, 'pil2-components/lib/std/pil'),
        ],
        test: {
            onAirEnd(processor) {
                if (processor.currentAir.name !== air) return;
                if (blocks !== undefined) throw new Error(`duplicate ${air} AIR`);
                if (!processor.currentAir.virtual) throw new Error(`${air} is not virtual`);
                const labels = processor.fixeds.getNonTemporalLabelRanges();
                const expected = spec.columns.map(name => `${air}.${name}`).sort();
                if (JSON.stringify(labels.map(item => item.label).sort()) !== JSON.stringify(expected)
                    || labels.some(item => item.from !== item.to || item.multiarray)) {
                    throw new Error(`${air} fixed-column schema changed`);
                }
                rowCount = processor.currentAir.rows;
                blocks = [];
                let current = null;
                for (let index = 0; index < rowCount; index++) {
                    const cells = spec.columns.map(name => {
                        const value = Context.references.getItem(`${air}.${name}`, [index]).asInt();
                        const reduced = ((value % prime) + prime) % prime;
                        return (reduced > prime / 2n ? reduced - prime : reduced).toString();
                    });
                    const op = cells[spec.columns.indexOf('OP')];
                    if (current === null || current.op !== op) {
                        if (current !== null) {
                            current.sha256 = current.hash.digest('hex');
                            delete current.hash;
                        }
                        current = { op, start: index, rows: 0, hash: crypto.createHash('sha256') };
                        blocks.push(current);
                    }
                    current.hash.update(cells.join('\t') + '\n');
                    current.rows += 1;
                }
                if (current !== null) {
                    current.sha256 = current.hash.digest('hex');
                    delete current.hash;
                }
            },
        },
    });
    if (result !== true || blocks === undefined || blocks.length === 0) {
        throw new Error(`compiler did not successfully produce ${air} fixed rows`);
    }
    return { air, columns: spec.columns, rows: rowCount, blocks };
}

// One table per process. The PIL compiler keeps module-global state (the
// airgroup registry and `Context.references`), so a second `compile()` in the
// same process collides on the consumer AIR name and observes nothing.
if (require.main === module) {
    if (process.argv.length !== 7) {
        console.error('usage: export-byte-tables.cjs COMPILER_ROOT ZISK_ROOT PROOFMAN_ROOT AIR OUTPUT');
        process.exitCode = 2;
    } else {
        const [compilerRoot, ziskRoot, proofmanRoot] =
            process.argv.slice(2, 5).map(value => path.resolve(value));
        const air = process.argv[5];
        const output = path.resolve(process.argv[6]);
        try {
            const table = exportTable(compilerRoot, ziskRoot, proofmanRoot, air);
            fs.writeFileSync(output, JSON.stringify(table, null, 2) + '\n');
        } catch (error) { console.error(error.stack); process.exitCode = 1; }
    }
}

module.exports = { exportTable, TABLES };
