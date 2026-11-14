#!/usr/bin/env python3
"""Consumer-visible accounting regressions over real kernel-checked declarations."""
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import exposure


class ChannelRegistryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="exposure-channels-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.reach = exposure.load_reachability()
        channels = self.root / "ZiskFv/Channels"
        airs = self.root / "ZiskFv/AirsClean"
        channels.mkdir(parents=True)
        airs.mkdir()
        (self.root / "trust").mkdir()
        (channels / "MemoryBus.lean").write_text(
            'instance MemBusChannel : Channel FGL MemBusMessage where\n'
            '  name := "MemoryBus"\n')
        (airs / "FullEnsemble.lean").write_text(
            "def fullRv64imSoundEnsemble :=\n"
            "  ensemble.addFinishedChannel MemBusChannel.toRaw\n"
            "theorem fullRv64imSoundEnsemble_assumptionsConsistency := by trivial\n")
        (airs / "MultiBusWiring.lean").write_text(
            'MemBusChannel\nbusId = constant "10"\nbusId = constant "88"\n'
            'busId = constant "103"\nbusId = constant "107"\n')
        self.entry = (
            '[[constant]]\nname = "MemBusChannel"\nkind = "channel"\n'
            'value = 10\nmodel = "ZiskFv/Channels/MemoryBus.lean"\n')
        self.registry = self.root / "trust/constants.toml"
        self.registry.write_text(self.entry)

    def resolve(self):
        with patch.object(exposure, "ROOT", self.root):
            return exposure.provider_buses(self.reach)

    def test_registered_channel_ignores_other_buses_in_same_wiring(self):
        self.assertEqual(self.resolve(), {10})

    def test_stale_registered_owner_fails_closed(self):
        self.registry.write_text(self.entry.replace("MemoryBus.lean", "Other.lean"))
        with self.assertRaisesRegex(ValueError, "stale registry owner"):
            self.resolve()

    def test_duplicate_registered_channel_fails_closed(self):
        self.registry.write_text(self.entry + self.entry)
        with self.assertRaisesRegex(ValueError, "duplicate registered channel"):
            self.resolve()

    def test_unregistered_ambiguous_channel_still_fails_closed(self):
        self.registry.write_text("")
        with self.assertRaisesRegex(ValueError, "ambiguous bus IDs"):
            self.resolve()


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
structure Operations where
  constraints : List Nat
structure Circuit (Output : Type) where
  operations : Nat → Operations
  result : Output
namespace Expression
def eval (_env : Unit) (value : Nat) := value
end Expression
namespace Extraction
class Circuit (F ExtF : Type) (C : Type → Type → Type) where
  main : C F ExtF → Nat → Nat
end Extraction
namespace ZiskFv.AirsClean.BinaryAdd
def main (n : Nat) : Circuit Unit :=
  { operations := fun _ => ⟨[n + 0]⟩, result := () }
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
variable {C : Type → Type → Type} [Extraction.Circuit Nat Nat C]
def constraint_0_every_row (c : C Nat Nat) (r : Nat) :=
  Extraction.Circuit.main c r = 0
def constraint_1_every_row (c : C Nat Nat) (r : Nat) :=
  Extraction.Circuit.main c r = 0
def constraint_2_every_row (c : C Nat Nat) (r : Nat) :=
  Extraction.Circuit.main c r = 1
def constraint_3_every_row (c : C Nat Nat) (r : Nat) :=
  Extraction.Circuit.main c r - 1 = 0
def constraint_4_every_row (c : C Nat Nat) (r : Nat) :=
  Extraction.Circuit.main c r + 0 = Extraction.Circuit.main c r
def constraint_5_every_row (c : C Nat Nat) (r : Nat) :=
  Extraction.Circuit.main c r = 1
end BinaryAdd.extraction
namespace Extraction.Components.BinaryAdd.Manifest
variable {C : Type → Type → Type} [Extraction.Circuit Nat Nat C]
def sourceRow (c : C Nat Nat) (r : Nat) := Extraction.Circuit.main c r
-- An unchecked list cannot map a generated main to these indices.
def assertZeroConstraints : List Nat := [0, 1, 2, 3, 4, 5]
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
open ZiskFv.AirsClean.BinaryAdd
variable {C : Type → Type → Type} [Extraction.Circuit Nat Nat C]
theorem constraint_0_correspondence (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) = 0 ↔
      BinaryAdd.extraction.constraint_0_every_row c r := by
  simp [Expression.eval, main, sourceRow, BinaryAdd.extraction.constraint_0_every_row]
-- Even a proved equality cannot claim the wrong raw index.
theorem constraint_1_correspondence (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) = 0 ↔
      BinaryAdd.extraction.constraint_0_every_row c r :=
  constraint_0_correspondence c r offset env
-- A nonzero equality is not a generated assertZero correspondence.
theorem constraint_2_correspondence (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) = 1 ↔
      BinaryAdd.extraction.constraint_2_every_row c r := by
  simp [Expression.eval, main, sourceRow, BinaryAdd.extraction.constraint_2_every_row]
-- A dead mention of main is unrelated to the assertion selected by the model.
theorem constraint_3_correspondence (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    (let _unused := (main (sourceRow c r)).operations offset
     Expression.eval env (sourceRow c r - 1)) = 0 ↔
      BinaryAdd.extraction.constraint_3_every_row c r := by
  rfl
-- The fallback value of getElem! is not an assertion, even for a provable identity.
theorem constraint_4_correspondence (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[9]!) = 0 ↔
      BinaryAdd.extraction.constraint_4_every_row c r := by
  simp [Expression.eval, main, BinaryAdd.extraction.constraint_4_every_row]
-- A caller-supplied correspondence promise is not a checked correspondence.
theorem constraint_5_correspondence (c : C Nat Nat) (r offset : Nat) (env : Unit)
    (h : Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) = 0 ↔
      BinaryAdd.extraction.constraint_5_every_row c r) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) = 0 ↔
      BinaryAdd.extraction.constraint_5_every_row c r := h
end Extraction.Components.BinaryAdd.Manifest
namespace ZiskFv.ExposureRegression
open ZiskFv.AirsClean.BinaryAdd Extraction.Components.BinaryAdd.Manifest
abbrev DemoSource (_ _ : Type) := Nat
instance : Extraction.Circuit Nat Nat DemoSource where
  main c _ := c
-- The bad correspondence really admits a row that the generated assertion rejects.
theorem unrelated_lhs_accepts_rejected_assertion :
    BinaryAdd.extraction.constraint_3_every_row (C := DemoSource) 1 0 ∧
    Expression.eval () (((main (sourceRow (C := DemoSource) 1 0)).operations 0).constraints[0]!) ≠ 0 := by
  change (1 - 1 = 0) ∧ (1 + 0 ≠ 0)
  decide
end ZiskFv.ExposureRegression
""")
        root = """
namespace ZiskFv.ExposureRegression
theorem root (a b : Nat) : a + b = b + a := Nat.add_comm a b
end ZiskFv.ExposureRegression
"""
        cls.compile("Baseline", root)
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
open ZiskFv.AirsClean.BinaryAdd Extraction.Components.BinaryAdd.Manifest
variable {C : Type → Type → Type} [Extraction.Circuit Nat Nat C]
theorem root (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) =
      Extraction.Circuit.main c r := by
  simp [Expression.eval, main, sourceRow]
end ZiskFv.ExposureRegression
"""
        cls.compile("UncheckedModel", "import Base\n" + model_root)
        cls.compile("CheckedModel", "import Checked\n" + model_root)
        cls.compile("ConsumedProof", """
import Checked
namespace ZiskFv.ExposureRegression
open ZiskFv.AirsClean.BinaryAdd Extraction.Components.BinaryAdd.Manifest
variable {C : Type → Type → Type} [Extraction.Circuit Nat Nat C]
theorem root (c : C Nat Nat) (r offset : Nat) (env : Unit) :
    Expression.eval env (((main (sourceRow c r)).operations offset).constraints[0]!) = 0 ↔
      BinaryAdd.extraction.constraint_0_every_row c r :=
  constraint_0_correspondence c r offset env
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

    def test_unrelated_lhs_mentions_do_not_replace_an_assertion_correspondence(self):
        deps = self.reports["CheckedModel"]
        name = "Extraction.Components.BinaryAdd.Manifest.constraint_3_correspondence"
        self.assertEqual(
            deps.nodes["ZiskFv.ExposureRegression.unrelated_lhs_accepts_rejected_assertion"]["kind"],
            "theorem")
        # The old names-plus-Eq-zero matcher would credit this *compiled*
        # theorem: all its requested references are present in the type.
        self.assertEqual(deps.nodes[name]["kind"], "theorem")
        self.assertTrue({
            "ZiskFv.AirsClean.BinaryAdd.main",
            "Extraction.Components.BinaryAdd.Manifest.sourceRow",
            "BinaryAdd.extraction.constraint_3_every_row",
        } <= set(deps.nodes[name]["type"]))
        self.assertNotIn(3, exposure.generated_component_cover(deps, set(deps.nodes))["BinaryAdd"])

    def test_out_of_range_default_is_not_a_generated_assertion(self):
        deps = self.reports["CheckedModel"]
        self.assertIn("Extraction.Components.BinaryAdd.Manifest.constraint_4_correspondence",
                      deps.nodes)
        self.assertNotIn(4, exposure.generated_component_cover(deps, set(deps.nodes))["BinaryAdd"])

    def test_extra_correspondence_hypothesis_cannot_grant_credit(self):
        deps = self.reports["CheckedModel"]
        self.assertIn("Extraction.Components.BinaryAdd.Manifest.constraint_5_correspondence",
                      deps.nodes)
        self.assertNotIn(5, exposure.generated_component_cover(deps, set(deps.nodes))["BinaryAdd"])

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
