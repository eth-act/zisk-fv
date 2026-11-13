#!/usr/bin/env python3
"""Consumer-visible accounting regressions over real kernel-checked declarations."""
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import exposure


class DeclarationCreditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix="exposure-dependencies-")
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.directory = Path(cls.tmp.name)
        cls.env = os.environ.copy()
        lean_path = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=exposure.ROOT, text=True).strip()
        cls.production_env = cls.env | {"LEAN_PATH": lean_path}
        cls.env["LEAN_PATH"] = str(cls.directory) + os.pathsep + lean_path
        cls.lean = subprocess.check_output(
            ["lake", "env", "which", "lean"], cwd=exposure.ROOT, text=True).strip()
        cls.reporter = exposure.ROOT / ".lake/build/bin/trust-gate"
        cls.compile("Extraction.Components.BinaryAdd.Constraints", """
namespace ZiskFv.AirsClean.BinaryAdd
def main (n : Nat) := n + 0
end ZiskFv.AirsClean.BinaryAdd
""")
        cls.compile("Base", """
import Extraction.Components.BinaryAdd.Constraints
namespace ZiskFv.ExposureRegression
structure CheckedLink where
  actual : Nat
  expected : Nat
  correspondence : actual = expected
def link0 : CheckedLink := ⟨2 + 3, 5, by decide⟩
def link1 : CheckedLink := ⟨3 * 4, 12, by decide⟩
instance : Inhabited CheckedLink := ⟨link0⟩
def family : List CheckedLink := [link0, link1]
def unconsumedAlias := family
theorem family_correspondence (i : Fin 2) :
    (family[i.val]!).actual = (family[i.val]!).expected := by
  exact (family[i.val]!).correspondence
end ZiskFv.ExposureRegression
namespace BinaryAdd.extraction
def constraint_0_every_row (n : Nat) := n = 0
def constraint_1_every_row (n : Nat) := n = 0
def constraint_2_every_row (n : Nat) := n = 1
end BinaryAdd.extraction
namespace Extraction.Components.BinaryAdd.Manifest
def sourceRow (n : Nat) := n
-- An unchecked list cannot map a generated main to these indices.
def assertZeroConstraints : List Nat := [0, 1, 2, 3]
end Extraction.Components.BinaryAdd.Manifest
""")
        cls.compile("Extra", """
import Base
namespace ZiskFv.ExposureRegression
def unusedImportedAlias := unconsumedAlias
end ZiskFv.ExposureRegression
""")
        cls.compile("Checked", """
import Base
namespace Extraction.Components.BinaryAdd.Manifest
theorem constraint_0_correspondence (n : Nat) :
    ZiskFv.AirsClean.BinaryAdd.main (sourceRow n) = 0 ↔
      BinaryAdd.extraction.constraint_0_every_row n := by
  simp [ZiskFv.AirsClean.BinaryAdd.main, sourceRow,
    BinaryAdd.extraction.constraint_0_every_row]
-- Even a proved equality cannot claim the wrong raw index.
theorem constraint_1_correspondence (n : Nat) :
    ZiskFv.AirsClean.BinaryAdd.main (sourceRow n) = 0 ↔
      BinaryAdd.extraction.constraint_0_every_row n := by
  exact constraint_0_correspondence n
-- A nonzero equality is not a generated assertZero correspondence.
theorem constraint_2_correspondence (n : Nat) :
    ZiskFv.AirsClean.BinaryAdd.main (sourceRow n) = 1 ↔
      BinaryAdd.extraction.constraint_2_every_row n := by
  simp [ZiskFv.AirsClean.BinaryAdd.main, sourceRow,
    BinaryAdd.extraction.constraint_2_every_row]
end Extraction.Components.BinaryAdd.Manifest
""")
        root = """
namespace ZiskFv.ExposureRegression
theorem root (a b : Nat) : a + b = b + a := Nat.add_comm a b
end ZiskFv.ExposureRegression
"""
        cls.compile("Baseline", "import Base\n" + root)
        cls.compile("Mention", """
import Extra
-- link0, link1, family_correspondence and constraint_0_correspondence.
namespace ZiskFv.ExposureRegression
def anotherUnusedAlias := unusedImportedAlias
end ZiskFv.ExposureRegression
""" + root)
        cls.compile("Family", """
import Base
namespace ZiskFv.ExposureRegression
theorem root (i : Fin 2) :
    (family[i.val]!).actual = (family[i.val]!).expected :=
  family_correspondence i
end ZiskFv.ExposureRegression
""")
        model_root = """
namespace ZiskFv.ExposureRegression
theorem root (n : Nat) : ZiskFv.AirsClean.BinaryAdd.main n = n := by
  simp [ZiskFv.AirsClean.BinaryAdd.main]
end ZiskFv.ExposureRegression
"""
        cls.compile("UncheckedModel", "import Base\n" + model_root)
        cls.compile("CheckedModel", "import Checked\n" + model_root)
        cls.compile("ConsumedProof", """
import Checked
namespace ZiskFv.ExposureRegression
theorem root (n : Nat) :
    ZiskFv.AirsClean.BinaryAdd.main
      (Extraction.Components.BinaryAdd.Manifest.sourceRow n) = 0 ↔
      BinaryAdd.extraction.constraint_0_every_row n :=
  Extraction.Components.BinaryAdd.Manifest.constraint_0_correspondence n
end ZiskFv.ExposureRegression
""")
        cls.reports = {name: cls.report(name) for name in (
            "Baseline", "Mention", "Family", "UncheckedModel", "CheckedModel", "ConsumedProof")}

    @classmethod
    def compile(cls, module, source):
        path = cls.directory / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        result = subprocess.run(
            [cls.lean, "-DwarningAsError=true", "-o", str(path.with_suffix(".olean")), str(path)],
            cwd=cls.directory, env=cls.env, capture_output=True, text=True)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    @classmethod
    def report(cls, module, *, production=False):
        result = subprocess.run(
            [str(cls.reporter), "report-dependencies", module], cwd=exposure.ROOT,
            env=cls.production_env if production else cls.env, capture_output=True, text=True)
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)
        return exposure.Dependencies(json.loads(result.stdout))

    def root(self, module):
        return self.reports[module].root("ZiskFv.ExposureRegression.root")

    def cover(self, module, *, model=False):
        return exposure.generated_component_cover(
            self.reports[module], self.root(module), model=model)["BinaryAdd"]

    def test_unused_import_comment_and_helper_alias_cannot_improve_root(self):
        self.assertEqual(self.root("Baseline"), self.root("Mention"))
        self.assertNotIn("ZiskFv.ExposureRegression.link0", self.root("Mention"))

    def test_real_proof_carrying_family_keeps_every_member(self):
        reached = self.root("Family")
        self.assertIn("ZiskFv.ExposureRegression.link0", reached)
        self.assertIn("ZiskFv.ExposureRegression.link1", reached)
        self.assertIn("ZiskFv.ExposureRegression.family_correspondence", reached)

    def test_unchecked_manifest_indices_never_credit_consumed_model(self):
        self.assertEqual(self.cover("UncheckedModel", model=True), set())

    def test_build_only_correspondence_is_not_theorem_consumption(self):
        self.assertEqual(self.cover("CheckedModel"), set())
        self.assertEqual(self.cover("CheckedModel", model=True), {0})
        self.assertIn("Extraction.Components.BinaryAdd.Manifest.constraint_0_correspondence",
                      self.reports["CheckedModel"].nodes)

    def test_consumed_checked_equality_credits_only_its_actual_index(self):
        self.assertEqual(self.cover("ConsumedProof"), {0})
        self.assertEqual(self.cover("ConsumedProof", model=True), {0})

    def test_production_binary_add_retains_only_four_checked_equalities(self):
        deps = self.report("Extraction.Components.BinaryAdd.Manifest", production=True)
        self.assertEqual(exposure.generated_component_cover(deps, set(deps.nodes))["BinaryAdd"],
                         {0, 1, 2, 3})

    def test_production_arith_family_keeps_all_thirteen_proof_carrying_links(self):
        deps = self.report("ZiskFv.AirsClean.ArithMul.RangeWiring", production=True)
        reached = deps.root("ZiskFv.AirsClean.ArithMul.arithRangeLinks_length")
        members = {f"Extraction.LookupWiring.link_Arith_{index}"
                   for index in [*range(49, 61), 63]}
        self.assertTrue(members <= reached)
        self.assertTrue(members <= deps.build_checks())

    def test_report_is_deterministic(self):
        again = self.report("Family")
        self.assertEqual(again.nodes, self.reports["Family"].nodes)
        self.assertEqual(again.correspondences, self.reports["Family"].correspondences)

    def test_missing_elaborated_root_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "missing elaborated root"):
            self.reports["Baseline"].root("ZiskFv.DoesNotExist")

    def test_missing_or_old_schema_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "dependency report"):
            exposure.Dependencies({})

    def test_stale_runtime_olean_cannot_survive_failed_refresh(self):
        # A real Lake project first produces a good runtime-imported olean.
        # Its subsequent proof failure must not reuse that old success.
        project = self.directory / "stale-runtime"
        project.mkdir()
        (project / "lean-toolchain").write_text(
            (exposure.ROOT / "lean-toolchain").read_text())
        source_dir = json.dumps(str(exposure.ROOT / "bin"))
        (project / "lakefile.toml").write_text(
            'name = "exposure-regression"\n'
            '[[lean_lib]]\nname = "ZiskFv"\n'
            f'[[lean_lib]]\nname = "TrustGate"\nsrcDir = {source_dir}\n'
            f'[[lean_exe]]\nname = "trust-gate"\nsrcDir = {source_dir}\n'
            'root = "TrustGate.Main"\nsupportInterpreter = true\n')
        source = project / "ZiskFv.lean"
        source.write_text(
            "namespace ZiskFv.Compliance\n"
            "theorem root_soundness (a b : Nat) : a + b = b + a := Nat.add_comm a b\n"
            "end ZiskFv.Compliance\n")
        baseline = exposure.load_dependencies(project)
        self.assertIn("ZiskFv.Compliance.root_soundness",
                      baseline.root("ZiskFv.Compliance.root_soundness"))
        self.assertTrue((project / ".lake/build/lib/lean/ZiskFv.olean").is_file())
        source.write_text(
            "namespace ZiskFv.Compliance\n"
            "theorem root_soundness (a b : Nat) : a + b = a := Nat.add_comm a b\n"
            "end ZiskFv.Compliance\n")
        with self.assertRaises(subprocess.CalledProcessError):
            exposure.load_dependencies(project)


if __name__ == "__main__":
    unittest.main()
