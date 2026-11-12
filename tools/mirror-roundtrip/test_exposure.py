#!/usr/bin/env python3
"""Fail-closed generated-component manifest accounting regressions."""
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import exposure


class ManifestCreditTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.reach = exposure.load_reachability()
        self.model = self.root / "ZiskFv/AirsClean/BinaryAdd/Constraints.lean"
        self.model.parent.mkdir(parents=True)
        self.model.write_text("import Extraction.Components.BinaryAdd.Constraints\n"
                              "import Extraction.Components.BinaryAdd.Manifest\n")
        (self.root / "ZiskFv.lean").write_text("import ZiskFv.AirsClean.BinaryAdd.Constraints\n")
        components = self.root / "Components"
        self.manifest = components / "BinaryAdd/Manifest.lean"
        self.manifest.parent.mkdir(parents=True)
        registry = self.root / "components.toml"
        registry.write_text('[air.BinaryAdd]\nexpected = "consumed"\n')
        self.addCleanup(patch.stopall)
        patch.object(exposure, "ROOT", self.root).start()
        patch.object(exposure, "COMPONENT_DIR", components).start()
        patch.object(exposure, "COMPONENTS", registry).start()
        self.source = (
            "import Extraction.Components.BinaryAdd.Constraints\n"
            "def assertZeroConstraints : List Nat :=\n  [0]\n"
            "def busPushConstraints : List Nat :=\n  [4, 5, 6, 7, 8]\n"
            "theorem constraint_0_correspondence (c : C FGL FGL) (r offset : ℕ)\n"
            "    (env : Environment FGL) :\n"
            "    env (((main (sourceRow c r)).operations offset).constraints[0]!) = 0 ↔\n"
            "      BinaryAdd.extraction.constraint_0_every_row c r := by\n"
            "  simp [main, sourceRow, circuit_norm,\n"
            "    BinaryAdd.extraction.constraint_0_every_row, sub_eq_add_neg]\n"
        )

    def cover(self, source=None, start="ZiskFv"):
        self.manifest.write_text(self.source if source is None else source)
        return exposure.generated_component_cover(self.reach, start)["BinaryAdd"]

    def test_proved_entry_only_not_bus_hints(self):
        self.assertEqual(self.cover(), {0})

    def test_list_without_proof_covers_nothing(self):
        self.assertEqual(self.cover(self.source.split("theorem")[0]), set())

    def test_commented_proof_covers_nothing(self):
        self.assertEqual(self.cover(self.source.replace("theorem", "/- theorem") + "-/"), set())

    def test_wrong_raw_index_covers_nothing(self):
        self.assertEqual(self.cover(self.source.replace("constraint_0_every_row", "constraint_1_every_row")), set())

    def test_wrong_assertion_position_covers_nothing(self):
        self.assertEqual(self.cover(self.source.replace("constraints[0]", "constraints[1]")), set())

    def test_unimported_manifest_covers_nothing(self):
        self.model.write_text("import Extraction.Components.BinaryAdd.Constraints\n")
        self.assertEqual(self.cover(), set())

    def test_outside_root_closure_covers_nothing(self):
        self.assertEqual(self.cover(start="ZiskFv.Soundness"), set())

    def test_missing_manifest_covers_nothing(self):
        self.assertEqual(exposure.generated_component_cover(self.reach, "ZiskFv")["BinaryAdd"], set())


if __name__ == "__main__":
    unittest.main()
