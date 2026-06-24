/-!
RV completeness interface.

This file lives in the normal `zisk-fv` Lean build. It deliberately does not
import the Aeneas-generated production transpiler: that code is generated in a
separate, reproducible workspace by `scripts/aeneas-production-extract.sh`.

The purpose here is to keep the final theorem shape checked in the main repo:
for every Sail-executable raw instruction, if the raw word is not in a known
ZisK gap, the extracted production ZisK decoder/lowering/circuit surface covers
it. The generated Aeneas harness instantiates the ZisK-side predicates.
-/

namespace ZiskFv.Completeness.Rv

/-- Raw 32-bit instruction word. Kept as `BitVec 32` to match Sail decoding. -/
abbrev RawInstruction := BitVec 32

/- ⚠ ASPIRATIONAL KERNEL — everything below (`Stage` / `Pipeline` / `Interface`
   and its composition lemmas) is the intended *eventual* completeness-composition
   machinery. No concrete `Interface` is ever instantiated, and the live endpoints
   in `ZiskFv.Completeness` (`root_completeness_sail`, `eventual_zisk_coverage`,
   `eventual_root_completeness`) do not use it. (`RawInstruction` above IS live —
   it is used by `Shapes` and the Sail containment proof.)
   See `ZiskFv/Completeness/Rv64im/ASPIRATIONAL.md`. -/

/-- One stage of the extracted ZisK production path: `reached` says production
ZisK gets this far on a raw word; `knownGap` is the explicitly recorded, honest
carve-out that excuses non-coverage at this stage (e.g. FENCE). -/
structure Stage where
  reached : RawInstruction → Prop
  knownGap : RawInstruction → Prop

/-- The extracted ZisK production coverage pipeline. Field order is pipeline
order: a supported `decode` lowers to an opcode (`lower`) and lands in the
covered opcode set (`opcode`); a lowered word materializes a circuit `row`.
Only the `decode` and `row` stages carry recorded gaps today. -/
structure Pipeline where
  decode : Stage
  lower : RawInstruction → Prop
  row : Stage
  opcode : RawInstruction → Prop

/-- Abstract RV-completeness interface between Sail and extracted production
ZisK, grouped by responsibility. The predicates are abstract because their
concrete implementations live in different generated Lean worlds today: Sail in
the main Lean 4.28 build, Aeneas in its generated Lean workspace.

* `sail` — the spec side: which raw words the Sail model executes (the domain
  the completeness claim covers).
* `zisk` — the ZisK production coverage pipeline (decode → lower / row / opcode)
  with its honest known-gap carve-outs.
* `soundness` — the static per-row contract handed to the opcode soundness
  theorems. -/
structure Interface where
  sail : RawInstruction → Prop
  zisk : Pipeline
  soundness : RawInstruction → Prop

namespace Interface

def knownGap (iface : Interface) (raw : RawInstruction) : Prop :=
  iface.zisk.decode.knownGap raw ∨ iface.zisk.row.knownGap raw

def ziskCircuitCovered (iface : Interface) (raw : RawInstruction) : Prop :=
  iface.zisk.decode.reached raw ∧
  iface.zisk.lower raw ∧
  iface.zisk.row.reached raw ∧
  iface.zisk.opcode raw

def ziskCircuitCoveredWithSoundnessInput
    (iface : Interface) (raw : RawInstruction) : Prop :=
  iface.ziskCircuitCovered raw ∧ iface.soundness raw

/-- ZisK-internal stage proved in the generated Aeneas harness:
decoder-supported raw words have a lowering opcode. -/
def LoweringComplete (iface : Interface) : Prop :=
  ∀ raw, iface.zisk.decode.reached raw → iface.zisk.lower raw

/-- ZisK-internal stage proved in the generated Aeneas harness:
decoder-supported raw words land in the currently covered opcode surface. -/
def OpcodeCoverageComplete (iface : Interface) : Prop :=
  ∀ raw, iface.zisk.decode.reached raw → iface.zisk.opcode raw

/-- Row materialization strengthening target. The generated Aeneas harness has
representative and edge-grid checks today; the universal proof remains open. -/
def RowMaterializationComplete (iface : Interface) : Prop :=
  ∀ raw, iface.zisk.lower raw → iface.zisk.row.reached raw

/-- Row materialization after excluding known materialization gaps. This is
the proof shape used by the extraction harness today: once decode/lowering are
established, a row can be supplied either by a direct family proof or by the
fact that the `row` stage's `knownGap` has ruled out the rejected production
case. -/
def RowMaterializationCompleteAvoidingKnownBugs (iface : Interface) : Prop :=
  ∀ raw, iface.zisk.decode.reached raw →
    ¬ iface.zisk.row.knownGap raw →
      iface.zisk.row.reached raw

/-- Boundary obligation for the Sail bridge: after excluding known ZisK gaps,
Sail-executable raw words must be accepted by the production ZisK decoder. -/
def AvoidKnownBugs (iface : Interface) : Prop :=
  ∀ raw, iface.sail raw → ¬ iface.knownGap raw →
    iface.zisk.decode.reached raw

def ShapeAvoidKnownBugs
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.sail raw → ¬ iface.knownGap raw →
    iface.zisk.decode.reached raw

/-- Boundary obligation after excluding only known decode gaps. This is the
acceptance-focused RV completeness boundary: row materialization is handled by
the ZisK-side row theorem rather than by weakening the Sail acceptance domain. -/
def ShapeAvoidKnownDecodeBugs
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.sail raw → ¬ iface.zisk.decode.knownGap raw →
    iface.zisk.decode.reached raw

def CompletenessAvoidingKnownBugs (iface : Interface) : Prop :=
  ∀ raw, iface.sail raw → ¬ iface.knownGap raw →
    iface.ziskCircuitCovered raw

def CompletenessAvoidingKnownDecodeBugs (iface : Interface) : Prop :=
  ∀ raw, iface.sail raw → ¬ iface.zisk.decode.knownGap raw →
    iface.ziskCircuitCovered raw

def ShapeCompletenessAvoidingKnownBugs
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.sail raw → ¬ iface.knownGap raw →
    iface.ziskCircuitCovered raw

def ShapeCompletenessAvoidingKnownDecodeBugs
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.sail raw → ¬ iface.zisk.decode.knownGap raw →
    iface.ziskCircuitCovered raw

/-- Sail-side domain bridge: every Sail-executable raw instruction is in the
shape currently being proved against the extracted ZisK production path. For
RV64IM this is intended to be discharged from Sail's decoder. -/
def SailExecutableContainedIn
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, iface.sail raw → shape raw

/-- Shape-local Sail validity: every raw word in this shape is executable by
the Sail-side predicate. This is useful for deriving direct known-good circuit
coverage from an avoid-known-bugs decoder bridge. -/
def ShapeSailExecutable
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.sail raw

/-- Direct shape coverage. This is the checked-in counterpart of the generated
finite-grid Aeneas checks: for every raw word in a generated shape family, the
extracted ZisK decoder/lowering/materialization/opcode path covers the word
and the word is not one of the explicitly recorded ZisK gaps. -/
def ShapeCircuitCoveredKnownGood
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.ziskCircuitCovered raw ∧ ¬ iface.knownGap raw

def ShapeNoKnownGap
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → ¬ iface.knownGap raw

/-- Shape-local row materialization. This is the proof obligation used when a
family can be closed before the full universal row-builder theorem is
available. -/
def ShapeRowMaterializationComplete
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.zisk.lower raw → iface.zisk.row.reached raw

def SoundnessInputComplete (iface : Interface) : Prop :=
  ∀ raw, iface.zisk.lower raw → iface.soundness raw

def ShapeSoundnessInputComplete
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.zisk.lower raw → iface.soundness raw

def CompletenessWithSoundnessInputAvoidingKnownDecodeBugs
    (iface : Interface) : Prop :=
  ∀ raw, iface.sail raw → ¬ iface.zisk.decode.knownGap raw →
    iface.ziskCircuitCoveredWithSoundnessInput raw

def ShapeCompletenessWithSoundnessInputAvoidingKnownDecodeBugs
    (iface : Interface) (shape : RawInstruction → Prop) : Prop :=
  ∀ raw, shape raw → iface.sail raw → ¬ iface.zisk.decode.knownGap raw →
    iface.ziskCircuitCoveredWithSoundnessInput raw

/-- Main abstract composition theorem for the current plan.

The non-abstract generated Aeneas counterpart is
`rv_completeness_avoiding_known_bugs` in the optional
`AENEAS_CHECK_RV_COMPLETENESS=1` workspace. -/
theorem completeness_avoiding_known_bugs
    (iface : Interface)
    (h_avoid : AvoidKnownBugs iface)
    (h_lower : LoweringComplete iface)
    (h_rows : RowMaterializationComplete iface)
    (h_opcode : OpcodeCoverageComplete iface) :
    CompletenessAvoidingKnownBugs iface := by
  intro raw h_sail h_not_gap
  have h_supported := h_avoid raw h_sail h_not_gap
  have h_lowerable := h_lower raw h_supported
  exact ⟨h_supported, h_lowerable, h_rows raw h_lowerable,
    h_opcode raw h_supported⟩

/-- Acceptance-focused abstract composition theorem. The only excluded Sail
raw words are known decode gaps; row materialization must be proved universally
for all lowerable raw words. -/
theorem completeness_avoiding_known_decode_bugs
    (iface : Interface)
    (shape : RawInstruction → Prop)
    (h_sail_subset : SailExecutableContainedIn iface shape)
    (h_avoid : ShapeAvoidKnownDecodeBugs iface shape)
    (h_lower : LoweringComplete iface)
    (h_rows : RowMaterializationComplete iface)
    (h_opcode : OpcodeCoverageComplete iface) :
    CompletenessAvoidingKnownDecodeBugs iface := by
  intro raw h_sail h_not_decode_gap
  have h_shape := h_sail_subset raw h_sail
  have h_supported := h_avoid raw h_shape h_sail h_not_decode_gap
  have h_lowerable := h_lower raw h_supported
  exact ⟨h_supported, h_lowerable, h_rows raw h_lowerable,
    h_opcode raw h_supported⟩

/-- Main abstract composition theorem for the generated Aeneas proof shape:
known decode gaps are excluded before decode support, and known row gaps are
excluded before row materialization. -/
theorem completeness_avoiding_known_bugs_of_row_gap
    (iface : Interface)
    (h_avoid : AvoidKnownBugs iface)
    (h_lower : LoweringComplete iface)
    (h_rows : RowMaterializationCompleteAvoidingKnownBugs iface)
    (h_opcode : OpcodeCoverageComplete iface) :
    CompletenessAvoidingKnownBugs iface := by
  intro raw h_sail h_not_gap
  have h_supported := h_avoid raw h_sail h_not_gap
  have h_lowerable := h_lower raw h_supported
  have h_not_row_gap : ¬ iface.zisk.row.knownGap raw := by
    intro h_row_gap
    exact h_not_gap (.inr h_row_gap)
  exact ⟨h_supported, h_lowerable,
    h_rows raw h_supported h_not_row_gap,
    h_opcode raw h_supported⟩

theorem shape_completeness_avoiding_known_bugs
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_complete : CompletenessAvoidingKnownBugs iface) :
    ShapeCompletenessAvoidingKnownBugs iface shape := by
  intro raw _h_shape h_sail h_not_gap
  exact h_complete raw h_sail h_not_gap

theorem shape_avoid_known_bugs
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_avoid : AvoidKnownBugs iface) :
    ShapeAvoidKnownBugs iface shape := by
  intro raw _h_shape h_sail h_not_gap
  exact h_avoid raw h_sail h_not_gap

theorem shape_completeness_avoiding_known_decode_bugs
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_complete : CompletenessAvoidingKnownDecodeBugs iface) :
    ShapeCompletenessAvoidingKnownDecodeBugs iface shape := by
  intro raw _h_shape h_sail h_not_decode_gap
  exact h_complete raw h_sail h_not_decode_gap

theorem shape_completeness_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_complete : ShapeCompletenessAvoidingKnownBugs iface shape_big) :
    ShapeCompletenessAvoidingKnownBugs iface shape_small := by
  intro raw h_shape h_sail h_not_gap
  exact h_complete raw (h_subset raw h_shape) h_sail h_not_gap

theorem shape_completeness_of_circuit_covered_known_good
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_covered : ShapeCircuitCoveredKnownGood iface shape) :
    ShapeCompletenessAvoidingKnownBugs iface shape := by
  intro raw h_shape _h_sail _h_not_gap
  exact (h_covered raw h_shape).left

theorem shape_no_known_gap_of_circuit_covered_known_good
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_covered : ShapeCircuitCoveredKnownGood iface shape) :
    ShapeNoKnownGap iface shape := by
  intro raw h_shape
  exact (h_covered raw h_shape).right

theorem shape_avoid_known_bugs_of_circuit_covered_known_good
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_covered : ShapeCircuitCoveredKnownGood iface shape) :
    ShapeAvoidKnownBugs iface shape := by
  intro raw h_shape _h_sail _h_not_gap
  exact (h_covered raw h_shape).left.left

theorem shape_row_materialization_of_circuit_covered_known_good
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_covered : ShapeCircuitCoveredKnownGood iface shape) :
    ShapeRowMaterializationComplete iface shape := by
  intro raw h_shape _h_lowerable
  exact (h_covered raw h_shape).left.right.right.left

theorem shape_circuit_covered_known_good_of_shape_avoid_and_rows
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_no_gap : ShapeNoKnownGap iface shape)
    (h_sail : ShapeSailExecutable iface shape)
    (h_avoid : ShapeAvoidKnownBugs iface shape)
    (h_lower : LoweringComplete iface)
    (h_rows : ShapeRowMaterializationComplete iface shape)
    (h_opcode : OpcodeCoverageComplete iface) :
    ShapeCircuitCoveredKnownGood iface shape := by
  intro raw h_shape
  have h_not_gap := h_no_gap raw h_shape
  have h_supported := h_avoid raw h_shape (h_sail raw h_shape) h_not_gap
  exact
    ⟨⟨h_supported, h_lower raw h_supported,
        h_rows raw h_shape (h_lower raw h_supported),
        h_opcode raw h_supported⟩,
      h_not_gap⟩

theorem completeness_of_shape_completeness
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_sail_subset : SailExecutableContainedIn iface shape)
    (h_complete : ShapeCompletenessAvoidingKnownBugs iface shape) :
    CompletenessAvoidingKnownBugs iface := by
  intro raw h_sail h_not_gap
  exact h_complete raw (h_sail_subset raw h_sail) h_sail h_not_gap

theorem completeness_of_circuit_covered_known_good
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_sail_subset : SailExecutableContainedIn iface shape)
    (h_covered : ShapeCircuitCoveredKnownGood iface shape) :
    CompletenessAvoidingKnownBugs iface :=
  completeness_of_shape_completeness
    iface
    shape
    h_sail_subset
    (shape_completeness_of_circuit_covered_known_good iface shape h_covered)

theorem shape_circuit_covered_known_good_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_covered : ShapeCircuitCoveredKnownGood iface shape_big) :
    ShapeCircuitCoveredKnownGood iface shape_small := by
  intro raw h_shape
  exact h_covered raw (h_subset raw h_shape)

theorem sail_executable_contained_in_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_sail_subset : SailExecutableContainedIn iface shape_small) :
    SailExecutableContainedIn iface shape_big := by
  intro raw h_sail
  exact h_subset raw (h_sail_subset raw h_sail)

theorem shape_sail_executable_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_sail : ShapeSailExecutable iface shape_big) :
    ShapeSailExecutable iface shape_small := by
  intro raw h_shape
  exact h_sail raw (h_subset raw h_shape)

theorem shape_avoid_known_bugs_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_avoid : ShapeAvoidKnownBugs iface shape_big) :
    ShapeAvoidKnownBugs iface shape_small := by
  intro raw h_shape h_sail h_not_gap
  exact h_avoid raw (h_subset raw h_shape) h_sail h_not_gap

theorem shape_no_known_gap_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_no_gap : ShapeNoKnownGap iface shape_big) :
    ShapeNoKnownGap iface shape_small := by
  intro raw h_shape
  exact h_no_gap raw (h_subset raw h_shape)

theorem shape_row_materialization_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_rows : ShapeRowMaterializationComplete iface shape_big) :
    ShapeRowMaterializationComplete iface shape_small := by
  intro raw h_shape h_lowerable
  exact h_rows raw (h_subset raw h_shape) h_lowerable

theorem shape_soundness_input_mono
    (iface : Interface)
    {shape_small shape_big : RawInstruction → Prop}
    (h_subset : ∀ raw, shape_small raw → shape_big raw)
    (h_soundness : ShapeSoundnessInputComplete iface shape_big) :
    ShapeSoundnessInputComplete iface shape_small := by
  intro raw h_shape h_lowerable
  exact h_soundness raw (h_subset raw h_shape) h_lowerable

theorem shape_completeness_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeCompletenessAvoidingKnownBugs iface shape_left)
    (h_right : ShapeCompletenessAvoidingKnownBugs iface shape_right) :
    ShapeCompletenessAvoidingKnownBugs
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape h_sail h_not_gap
  · exact h_right raw h_right_shape h_sail h_not_gap

theorem shape_circuit_covered_known_good_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeCircuitCoveredKnownGood iface shape_left)
    (h_right : ShapeCircuitCoveredKnownGood iface shape_right) :
    ShapeCircuitCoveredKnownGood
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape
  · exact h_right raw h_right_shape

theorem sail_executable_contained_in_or_left
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_sail_subset : SailExecutableContainedIn iface shape_left) :
    SailExecutableContainedIn
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_sail
  exact .inl (h_sail_subset raw h_sail)

theorem sail_executable_contained_in_or_right
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_sail_subset : SailExecutableContainedIn iface shape_right) :
    SailExecutableContainedIn
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_sail
  exact .inr (h_sail_subset raw h_sail)

theorem shape_sail_executable_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeSailExecutable iface shape_left)
    (h_right : ShapeSailExecutable iface shape_right) :
    ShapeSailExecutable
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape
  · exact h_right raw h_right_shape

theorem shape_avoid_known_bugs_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeAvoidKnownBugs iface shape_left)
    (h_right : ShapeAvoidKnownBugs iface shape_right) :
    ShapeAvoidKnownBugs
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape h_sail h_not_gap
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape h_sail h_not_gap
  · exact h_right raw h_right_shape h_sail h_not_gap

theorem shape_no_known_gap_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeNoKnownGap iface shape_left)
    (h_right : ShapeNoKnownGap iface shape_right) :
    ShapeNoKnownGap
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape
  · exact h_right raw h_right_shape

theorem shape_row_materialization_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeRowMaterializationComplete iface shape_left)
    (h_right : ShapeRowMaterializationComplete iface shape_right) :
    ShapeRowMaterializationComplete
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape h_lowerable
  · exact h_right raw h_right_shape h_lowerable

theorem shape_soundness_input_or
    (iface : Interface)
    {shape_left shape_right : RawInstruction → Prop}
    (h_left : ShapeSoundnessInputComplete iface shape_left)
    (h_right : ShapeSoundnessInputComplete iface shape_right) :
    ShapeSoundnessInputComplete
      iface
      (fun raw => shape_left raw ∨ shape_right raw) := by
  intro raw h_shape h_lowerable
  rcases h_shape with h_left_shape | h_right_shape
  · exact h_left raw h_left_shape h_lowerable
  · exact h_right raw h_right_shape h_lowerable

/-- Shape-local composition theorem. This is the main staging theorem for
families whose production decoder/lowering/opcode coverage is known, but where
row materialization has only been closed for that family rather than
universally. -/
theorem shape_completeness_avoiding_known_bugs_of_shape_rows
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_avoid : AvoidKnownBugs iface)
    (h_lower : LoweringComplete iface)
    (h_rows : ShapeRowMaterializationComplete iface shape)
    (h_opcode : OpcodeCoverageComplete iface) :
    ShapeCompletenessAvoidingKnownBugs iface shape := by
  intro raw h_shape h_sail h_not_gap
  have h_supported := h_avoid raw h_sail h_not_gap
  have h_lowerable := h_lower raw h_supported
  exact ⟨h_supported, h_lowerable, h_rows raw h_shape h_lowerable,
    h_opcode raw h_supported⟩

theorem shape_completeness_avoiding_known_bugs_of_row_gap
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_avoid : AvoidKnownBugs iface)
    (h_lower : LoweringComplete iface)
    (h_rows : RowMaterializationCompleteAvoidingKnownBugs iface)
    (h_opcode : OpcodeCoverageComplete iface) :
    ShapeCompletenessAvoidingKnownBugs iface shape := by
  exact
    shape_completeness_avoiding_known_bugs
      iface
      shape
      (completeness_avoiding_known_bugs_of_row_gap
        iface
        h_avoid
        h_lower
        h_rows
        h_opcode)

theorem shape_completeness_avoiding_known_bugs_of_shape_avoid_and_rows
    (iface : Interface) (shape : RawInstruction → Prop)
    (h_avoid : ShapeAvoidKnownBugs iface shape)
    (h_lower : LoweringComplete iface)
    (h_rows : ShapeRowMaterializationComplete iface shape)
    (h_opcode : OpcodeCoverageComplete iface) :
    ShapeCompletenessAvoidingKnownBugs iface shape := by
  intro raw h_shape h_sail h_not_gap
  have h_supported := h_avoid raw h_shape h_sail h_not_gap
  have h_lowerable := h_lower raw h_supported
  exact ⟨h_supported, h_lowerable, h_rows raw h_shape h_lowerable,
    h_opcode raw h_supported⟩

end Interface

end ZiskFv.Completeness.Rv
