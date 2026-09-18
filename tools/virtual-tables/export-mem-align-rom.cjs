#!/usr/bin/env node
// Execute the pinned PIL builder, observing its fixed columns before virtual
// table lowering discards the AIR. No row-building algorithm is duplicated here.
const fs = require('node:fs');
const path = require('node:path');

const columns = ['PC', 'DELTA_PC', 'DELTA_ADDR', 'OFFSET', 'WIDTH', 'FLAGS'];

function exportRows(compilerRoot, ziskRoot, proofmanRoot, output) {
    const compile = require(path.join(compilerRoot, 'src/compiler.js'));
    const { F1Field } = require(path.join(compilerRoot, 'node_modules/ffjavascript'));
    const Context = require(path.join(compilerRoot, 'src/context.js'));
    const prime = 0xffffffff00000001n;
    const production = fs.readFileSync(path.join(ziskRoot, 'pil/zisk.pil'), 'utf8')
        .replace(/\/\*[\s\S]*?\*\//g, '').replace(/\/\/[^\n]*/g, '');
    const calls = production.match(/\bvirtual\s+MemAlignRom\s*\([^;]*;/g) || [];
    if (calls.length !== 1 || !/^virtual\s+MemAlignRom\s*\(\s*\)\s*;$/.test(calls[0])) {
        throw new Error('production MemAlignRom invocation changed; update the extraction harness');
    }
    let rows;
    const source = `require "std_direct.pil"
require "mem/pil/mem_align_rom.pil"
// Register a zero-multiplicity consumer so the standard library can finish
// the isolated table. This does not alter or provide any fixed column.
airtemplate RomConsumer(const int N = 256) {
    lookup_assumes(MEMORY_ALIGN_ROM_ID, [0, 0, 0, 0, 0, 0], sel: 0);
}
airgroup Zisk { virtual MemAlignRom(); RomConsumer(); }
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
                if (processor.currentAir.name !== 'MemAlignRom') return;
                if (rows !== undefined) throw new Error('duplicate MemAlignRom AIR');
                if (!processor.currentAir.virtual) throw new Error('MemAlignRom is not virtual');
                const labels = processor.fixeds.getNonTemporalLabelRanges();
                const expected = columns.map(name => `MemAlignRom.${name}`).sort();
                if (JSON.stringify(labels.map(item => item.label).sort()) !== JSON.stringify(expected)
                    || labels.some(item => item.from !== item.to || item.multiarray)) {
                    throw new Error('MemAlignRom fixed-column schema changed');
                }
                rows = Array.from({ length: processor.currentAir.rows }, (_, index) =>
                    columns.map(name => {
                        const value = Context.references.getItem(`MemAlignRom.${name}`, [index]).asInt();
                        // A canonical signed representative fits the extractor's i64 reader.
                        const reduced = ((value % prime) + prime) % prime;
                        return (reduced > prime / 2n ? reduced - prime : reduced).toString();
                    }).join('\t'));
            },
        },
    });
    if (result !== true || rows === undefined || rows.length === 0) {
        throw new Error('compiler did not successfully produce MemAlignRom fixed rows');
    }
    fs.writeFileSync(output, columns.join('\t') + '\n' + rows.join('\n') + '\n');
}

if (require.main === module) {
    if (process.argv.length !== 6) {
        console.error('usage: export-mem-align-rom.cjs COMPILER_ROOT ZISK_ROOT PROOFMAN_ROOT OUTPUT');
        process.exitCode = 2;
    } else {
        try { exportRows(...process.argv.slice(2).map(value => path.resolve(value))); }
        catch (error) { console.error(error.stack); process.exitCode = 1; }
    }
}

module.exports = { exportRows };
