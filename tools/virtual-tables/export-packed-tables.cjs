#!/usr/bin/env node
// Observe target-bus projections of the ACTUAL production packing. No packing
// algorithm or fixed-column builder is reimplemented. Every target physical
// cell is compared to the compiler's retained pre-lowering source column.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');

const TARGETS = new Set([88, 124, 125, 330, 331]);

function exportPacked(compilerRoot, ziskRoot, proofmanRoot, output) {
    const compile = require(path.join(compilerRoot, 'src/compiler.js'));
    const { F1Field } = require(path.join(compilerRoot, 'node_modules/ffjavascript'));
    const Context = require(path.join(compilerRoot, 'src/context.js'));
    const { array, alone, packedSchema, checkPackedLane } =
        require('./compiled-hints.cjs').compiledHints(compilerRoot);
    const FixedCol = require(path.join(compilerRoot, 'src/expression_items/fixed_col.js'));
    const WitnessCol = require(path.join(compilerRoot, 'src/expression_items/witness_col.js'));
    const prime = 0xffffffff00000001n;
    const sources = new Map();
    const airs = [];
    const placements = [];
    const ref = (name, indexes = []) => Context.references.getItem(name, indexes);
    const integer = expression => Number(expression.asInt());
    function canonical(value) {
        const reduced = ((value % prime) + prime) % prime;
        return (reduced > prime / 2n ? reduced - prime : reduced).toString();
    }
    function sourceSnapshot() {
        const count = integer(ref('airgroup.std.vt.num_tables'));
        for (let table = 0; table < count; table++) {
            const busId = integer(ref('airgroup.std.vt.opid', [table]));
            if (!TARGETS.has(busId)) continue;
            const width = integer(ref('airgroup.std.vt.width', [table]));
            const innerCount = integer(ref('airgroup.std.vt.num_table_ids', [table]));
            for (let inner = 0; inner < innerCount; inner++) {
                const tableId = integer(ref('airgroup.std.vt.table_ids', [table, inner]));
                if (sources.has(tableId)) continue;
                const rows = integer(ref('airgroup.std.vt.inner_height', [table, inner]));
                const columns = Array.from({ length: width }, (_, slot) =>
                    alone(ref('airgroup.std.vt.columns', [table, inner, slot]), FixedCol));
                if (columns.some(column => Number(column.getRowCount()) !== rows)) {
                    throw new Error(`source table ${tableId} has inconsistent physical domain`);
                }
                sources.set(tableId, { tableId, busId, rows, width, columns });
            }
        }
    }
    function observe(processor) {
        if (processor.currentAir.virtual) {
            sourceSnapshot();
            return;
        }
        if (!/^VirtualTable[01]$/.test(processor.currentAir.name)) return;
        const air = Number(processor.currentAir.name.slice('VirtualTable'.length));
        const rows = Number(processor.currentAir.rows);
        const hints = [...processor.hints];
        const metadata = hints.filter(hint => hint.name === 'virtual_table_data');
        if (metadata.length !== 1) throw new Error('missing/duplicate packed table metadata');
        const tableIds = array(metadata[0].data.table_ids).map(integer);
        const starts = array(metadata[0].data.acc_heights).map(integer);
        if (tableIds.length !== starts.length) throw new Error('packed metadata lengths differ');
        const routes = hints.filter(hint => hint.name === 'gsum_debug_data' &&
            hint.data.name_piop.asString() === 'Lookup' && hint.data.type_piop.asInt() === 1n);
        if (routes.length !== integer(metadata[0].data.num_muls) ||
            processor.witness.countByStage(1)[0] !== routes.length) {
            throw new Error('packed producer route/multiplicity count differs');
        }
        const expressions = routes.map(hint => array(hint.data.expressions));
        const schema = packedSchema(processor, expressions.map(columns => columns.length));
        const lanes = routes.map((hint, lane) => {
            const data = hint.data;
            const witness = alone(data.num_reps, WitnessCol);
            const uid = alone(data.busid, FixedCol);
            const columns = expressions[lane].map(expr => alone(expr, FixedCol));
            checkPackedLane(schema, lane, witness, uid, columns);
            return { uid, opids: array(data.opids).map(integer), columns };
        });
        const seen = new Map();
        for (let index = 0; index < tableIds.length; index++) {
            const source = sources.get(tableIds[index]);
            if (!source) continue; // This exporter makes no claim about unrelated buses' data.
            const start = starts[index];
            if (!Number.isSafeInteger(start) || start < 0 || start + source.rows > rows * lanes.length) {
                throw new Error(`source table ${source.tableId} is outside physical producer domain`);
            }
            if (placements.some(item => item.tableId === source.tableId)) throw new Error('source table appears in multiple physical placements');
            const digest = crypto.createHash('sha256');
            for (let index = 0; index < source.rows; index++) {
                const offset = start + index;
                const lane = Math.floor(offset / rows);
                const row = offset % rows;
                const physical = lanes[lane];
                if (physical.uid.getValue(row) !== BigInt(source.busId) ||
                    !physical.opids.includes(source.busId) ||
                    physical.columns.length < source.width) {
                    throw new Error(`packed UID/width mismatch for source table ${source.tableId} row ${index}`);
                }
                const cells = source.columns.map((column, slot) => {
                    const value = column.getValue(index);
                    if (physical.columns[slot].getValue(row) !== value) {
                        throw new Error(`packed tuple mismatch for source table ${source.tableId} row ${index} slot ${slot}`);
                    }
                    return canonical(value);
                });
                for (let slot = source.width; slot < physical.columns.length; slot++) {
                    if (physical.columns[slot].getValue(row) !== 0n) throw new Error('nonzero source tuple padding');
                }
                digest.update(cells.join('\t') + '\n');
            }
            placements.push({ tableId: source.tableId, busId: source.busId,
                width: source.width, rows: source.rows, air, start,
                sha256: digest.digest('hex') });
        }
        // Check the converse as well: no target UID cell may hide outside its
        // unique source interval, even if its multiplicity happens to be zero.
        for (let lane = 0; lane < lanes.length; lane++) {
            for (let row = 0; row < rows; row++) {
                const busId = Number(lanes[lane].uid.getValue(row));
                if (!TARGETS.has(busId)) continue;
                const offset = lane * rows + row;
                const owners = placements.filter(source => source.air === air &&
                    source.start <= offset && offset < source.start + source.rows);
                if (owners.length !== 1 || owners[0].busId !== busId) {
                    throw new Error(`unowned/colliding target UID ${busId} at ${air}/${lane}/${row}`);
                }
                seen.set(owners[0].tableId, (seen.get(owners[0].tableId) || 0) + 1);
            }
        }
        for (const source of placements.filter(source => source.air === air)) {
            if (seen.get(source.tableId) !== source.rows) throw new Error('target projection is not exhaustive');
        }
        airs.push({ air, rows, rawWidth: lanes.length, widths: lanes.map(lane => lane.columns.length) });
    }
    const result = compile(new F1Field(prime), path.join(ziskRoot, 'pil/zisk.pil'), null, {
        protoOut: false,
        inputDir: ziskRoot,
        includePaths: [path.join(ziskRoot, 'pil'), path.join(ziskRoot, 'state-machines'),
            path.join(ziskRoot, 'precompiles'),
            path.join(proofmanRoot, 'pil2-components/lib/std/pil')],
        test: { onAirEnd: observe },
    });
    if (result !== true || airs.length !== 2 || new Set(airs.map(air => air.air)).size !== 2 ||
        [...TARGETS].some(bus => !placements.some(source => source.busId === bus)) ||
        sources.size !== placements.length) {
        throw new Error('production packed source observation incomplete');
    }
    fs.writeFileSync(output, JSON.stringify({ version: 1, airs: airs.sort((a, b) => a.air - b.air),
        sources: placements.sort((a, b) => a.tableId - b.tableId) }, null, 2) + '\n');
}

if (require.main === module) {
    if (process.argv.length !== 6) {
        console.error('usage: export-packed-tables.cjs COMPILER_ROOT ZISK_ROOT PROOFMAN_ROOT OUTPUT');
        process.exitCode = 2;
    } else {
        try { exportPacked(...process.argv.slice(2).map(value => path.resolve(value))); }
        catch (error) { console.error(error.stack); process.exitCode = 1; }
    }
}
module.exports = { exportPacked };
