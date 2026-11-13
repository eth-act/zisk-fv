const path = require('node:path');

// Match the pinned compiler's proto_out.js::toHintField array expansion.
// Hint arrays may be Expression(ArrayOf), not native JavaScript arrays.
function compiledHints(compilerRoot) {
    const Expression = require(path.join(compilerRoot, 'src/expression.js'));
    const ExpressionReference = require(path.join(compilerRoot, 'src/expression_items/expression_reference.js'));
    const ArrayOf = require(path.join(compilerRoot, 'src/expression_items/array_of.js'));

    function referencedValue(value) {
        if (value instanceof ExpressionReference) {
            return value.instance.get(value.id).getValue();
        }
        return value;
    }

    function array(value) {
        value = referencedValue(value);
        if (Array.isArray(value)) return value;
        if (value instanceof Expression && value.isArray) {
            value = value.getAloneOperand();
        }
        if (!(value instanceof ArrayOf) || value.dim !== 1) {
            throw new Error('expected a one-dimensional compiled hint array');
        }
        return value.toArrays();
    }

    function alone(value, cls) {
        value = referencedValue(value);
        if (value instanceof Expression) value = value.eval().getAlone();
        if (!(value instanceof cls) || value.rowOffset) {
            throw new Error(`expected unshifted compiled ${cls.name}`);
        }
        return value;
    }

    // Source allocation order is UID lanes, flattened payload, and one
    // stage-1 multiplicity per lane. Use actual active global identities;
    // virtual AIR aliases do not necessarily exist as qualified references.
    function packedSchema(processor, widths) {
        const witnesses = [...processor.witness.keyValues()]
            .filter(([, definition]) => definition.stage === 1)
            .map(([id]) => id);
        const fixed = [...processor.fixeds.keyValues()]
            .filter(([, definition]) => !definition.temporal)
            .map(([id]) => id);
        const lanes = widths.length;
        if (witnesses.length !== lanes ||
            fixed.length !== lanes + widths.reduce((sum, width) => sum + width, 0)) {
            throw new Error('packed active witness/fixed allocation schema changed');
        }
        let offset = lanes;
        const columns = widths.map(width => {
            const ids = fixed.slice(offset, offset + width);
            offset += width;
            return ids;
        });
        return { witnesses, uids: fixed.slice(0, lanes), columns };
    }

    function checkPackedLane(schema, lane, witness, uid, columns) {
        if (witness.id !== schema.witnesses[lane] ||
            uid.id !== schema.uids[lane] ||
            columns.length !== schema.columns[lane].length ||
            columns.some((column, slot) => column.id !== schema.columns[lane][slot])) {
            throw new Error('packed producer operands differ from actual active lane identities');
        }
    }

    return { array, alone, packedSchema, checkPackedLane };
}

module.exports = { compiledHints };
