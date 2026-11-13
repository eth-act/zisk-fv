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

    return { array, alone };
}

module.exports = { compiledHints };
