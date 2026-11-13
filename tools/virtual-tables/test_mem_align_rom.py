"""Regression controls for the physical-row fidelity comparison."""
import importlib.util
from pathlib import Path
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
