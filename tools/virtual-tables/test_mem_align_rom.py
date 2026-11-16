"""Regression controls for the physical-row fidelity comparison."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("rom_check", Path(__file__).with_name("check.py"))
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class MemAlignRomComparison(unittest.TestCase):
    def test_all_columns_and_physical_indices(self):
        rows = [[1, 2, 3, 4, 5, 6], [0, 0, 0, 0, 0, 512]]
        self.assertEqual(checker.compare(rows, rows), [])
        for index in range(len(rows)):
            for column in range(6):
                mutant = [row.copy() for row in rows]
                mutant[index][column] += 1
                self.assertTrue(checker.compare(rows, mutant))
        self.assertTrue(checker.compare(rows, rows[::-1]))
        self.assertTrue(checker.compare(rows, rows[:-1]))
        self.assertTrue(checker.compare(rows, rows + [rows[-1]]))

    def test_field_representation_and_schema(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "MemAlignRom.tsv"
            path.write_text(checker.COLUMNS + "\n1\t-1\t0\t0\t1\t1\n")
            self.assertEqual(checker.exported_rows(path), [[1, checker.PRIME - 1, 0, 0, 1, 1]])
            for text in ("", "FLAGS\tPC\n0\t1\n", checker.COLUMNS + "\n1\t2\n"):
                path.write_text(text)
                with self.assertRaises(ValueError):
                    checker.exported_rows(path)


class PackedMetadataNumbers(unittest.TestCase):
    """Execute the actual metadata converter on typed JavaScript values."""

    def assert_numeric_behavior(self, program):
        module = Path(__file__).with_name("export-packed-tables.cjs")
        result = subprocess.run(
            ["node", "-e",
             "const assert = require('node:assert/strict');\n"
             "const { metadataInteger } = require(process.argv[1]);\n" + program,
             str(module)],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_safe_metadata_integer_roundtrip(self):
        self.assert_numeric_behavior("""
const limit = 2n ** 53n - 1n;
for (const value of [0n, 1n, 88n, 331n, limit, -limit]) {
    const number = metadataInteger(value);
    assert(Number.isSafeInteger(number));
    assert.equal(BigInt(number), value);
    assert.equal(BigInt(JSON.parse(JSON.stringify(number))), value);
}
for (const value of [0, 88, Number.MAX_SAFE_INTEGER, -Number.MAX_SAFE_INTEGER]) {
    assert.equal(metadataInteger(value), value);
}
const identities = new Map([
    [metadataInteger(limit), 'last-safe'],
    [metadataInteger(limit - 1n), 'previous-safe'],
]);
assert.equal(identities.size, 2);
""")

    def test_two_to_53_boundary_rejects_before_map_identity(self):
        self.assert_numeric_behavior("""
const boundary = 2n ** 53n;
assert.equal(BigInt(metadataInteger(boundary - 1n)), boundary - 1n);
const identities = new Map();
for (const value of [boundary, boundary + 1n, boundary + 2n,
                     -boundary, -boundary - 1n]) {
    assert.throws(() => identities.set(metadataInteger(value), value), {
        name: 'RangeError',
        message: /packed JSON metadata integer cannot be represented exactly/,
    });
}
assert.equal(identities.size, 0);
""")

    def test_distinct_large_field_table_ids_are_not_aliased(self):
        self.assert_numeric_behavior("""
const prime = 0xffffffff00000001n;
const ids = [prime - 1n, prime - 2n, 2n ** 53n + 1n, 2n ** 53n + 2n];
assert.equal(new Set(ids).size, ids.length);
const identities = new Map();
for (const id of ids) {
    assert(id >= 0n && id < prime); // Valid FGL values, unsupported JSON IDs.
    assert.throws(() => identities.set(metadataInteger(id), id), RangeError);
}
assert.equal(identities.size, 0);
""")

    def test_unsupported_numeric_representations_do_not_coerce(self):
        self.assert_numeric_behavior("""
for (const value of ['0', false, true, null, undefined, {}, []]) {
    assert.throws(() => metadataInteger(value), TypeError);
}
for (const value of [1.5, -1.5, NaN, Infinity, -Infinity, 2 ** 53]) {
    assert.throws(() => metadataInteger(value), RangeError);
}
""")
