import Extraction.Binary
import ZiskFv.AirsClean.Binary.Bridge
/-!
# Machine-checked weld for the Binary constraint mirror

Binary's maintained v1 and Clean views remain checked against the generated
`Extraction.Binary` F-only constraints. The seven welds below are bidirectional
and universally quantified over the source circuit, so they neither strengthen
the validator nor introduce a caller-supplied premise.

BinaryAdd is intentionally absent: its reviewed `Row` and `Constraints` modules
are now emitted into `Extraction.Components.BinaryAdd` and re-exported directly.
The former BinaryAdd weld clauses were removed only after that generated component
became the model source.

The weld does not claim coverage of Binary's challenge-mixing constraints. Its
seven F-only constraints read stage-1 columns `{0, 32, 33, 34, 35, 36, 37, 38}`;
the remaining columns are pinned separately by the generated lookup wiring.

No axiom, sorry, `native_decide`, or other trust marker is used.
-/

universe u

namespace ZiskFv.AirsClean.BinaryMirrorWeld

open Goldilocks

/-! ## Binary -/

namespace Binary

open ZiskFv.Airs.Binary (Valid_Binary core_every_row boolean_mode32 boolean_carry_7
  boolean_result_is_a boolean_use_first_byte boolean_c_is_signed
  b_op_or_sext_def_holds mode32_and_c_is_signed_def_holds)

variable {C : Type → Type → Sort u} {F ExtF : Type} [Field F] [Field ExtF]
  [Extraction.Circuit F ExtF C]

/-- The Binary AIR's witness row, read out of an arbitrary `Extraction.Circuit`.

    The column indices are transcribed from the extractor's own column-name
    header at `build/extraction/Extraction/Binary.lean:13-57`:

    * stage 1: `0` `b_op`, `1`–`8` `free_in_a[0..7]`, `9`–`16` `free_in_b[0..7]`,
      `17`–`24` `free_in_c[0..7]`, `25`–`32` `carry[0..7]`, `33` `mode32`,
      `34` `result_is_a`, `35` `use_first_byte`, `36` `c_is_signed`,
      `37` `b_op_or_sext`, `38` `mode32_and_c_is_signed`;
    * stage 2: `0` `gsum`, `1`–`4` `im_cluster`.

    This is the only handwritten datum the Binary weld introduces. It has no
    default arm: all 44 fields are genuine cell reads, so no weld below can be
    resting on a `0` stub. -/
@[reducible]
def validOfCircuit (c : C F ExtF) : Valid_Binary F ExtF where
  b_op := fun r => Extraction.Circuit.main c (id := 1) (column := 0) (row := r) (rotation := 0)
  free_in_a_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 1) (row := r) (rotation := 0)
  free_in_a_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 2) (row := r) (rotation := 0)
  free_in_a_2 := fun r => Extraction.Circuit.main c (id := 1) (column := 3) (row := r) (rotation := 0)
  free_in_a_3 := fun r => Extraction.Circuit.main c (id := 1) (column := 4) (row := r) (rotation := 0)
  free_in_a_4 := fun r => Extraction.Circuit.main c (id := 1) (column := 5) (row := r) (rotation := 0)
  free_in_a_5 := fun r => Extraction.Circuit.main c (id := 1) (column := 6) (row := r) (rotation := 0)
  free_in_a_6 := fun r => Extraction.Circuit.main c (id := 1) (column := 7) (row := r) (rotation := 0)
  free_in_a_7 := fun r => Extraction.Circuit.main c (id := 1) (column := 8) (row := r) (rotation := 0)
  free_in_b_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 9) (row := r) (rotation := 0)
  free_in_b_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 10) (row := r) (rotation := 0)
  free_in_b_2 := fun r => Extraction.Circuit.main c (id := 1) (column := 11) (row := r) (rotation := 0)
  free_in_b_3 := fun r => Extraction.Circuit.main c (id := 1) (column := 12) (row := r) (rotation := 0)
  free_in_b_4 := fun r => Extraction.Circuit.main c (id := 1) (column := 13) (row := r) (rotation := 0)
  free_in_b_5 := fun r => Extraction.Circuit.main c (id := 1) (column := 14) (row := r) (rotation := 0)
  free_in_b_6 := fun r => Extraction.Circuit.main c (id := 1) (column := 15) (row := r) (rotation := 0)
  free_in_b_7 := fun r => Extraction.Circuit.main c (id := 1) (column := 16) (row := r) (rotation := 0)
  free_in_c_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 17) (row := r) (rotation := 0)
  free_in_c_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 18) (row := r) (rotation := 0)
  free_in_c_2 := fun r => Extraction.Circuit.main c (id := 1) (column := 19) (row := r) (rotation := 0)
  free_in_c_3 := fun r => Extraction.Circuit.main c (id := 1) (column := 20) (row := r) (rotation := 0)
  free_in_c_4 := fun r => Extraction.Circuit.main c (id := 1) (column := 21) (row := r) (rotation := 0)
  free_in_c_5 := fun r => Extraction.Circuit.main c (id := 1) (column := 22) (row := r) (rotation := 0)
  free_in_c_6 := fun r => Extraction.Circuit.main c (id := 1) (column := 23) (row := r) (rotation := 0)
  free_in_c_7 := fun r => Extraction.Circuit.main c (id := 1) (column := 24) (row := r) (rotation := 0)
  carry_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 25) (row := r) (rotation := 0)
  carry_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 26) (row := r) (rotation := 0)
  carry_2 := fun r => Extraction.Circuit.main c (id := 1) (column := 27) (row := r) (rotation := 0)
  carry_3 := fun r => Extraction.Circuit.main c (id := 1) (column := 28) (row := r) (rotation := 0)
  carry_4 := fun r => Extraction.Circuit.main c (id := 1) (column := 29) (row := r) (rotation := 0)
  carry_5 := fun r => Extraction.Circuit.main c (id := 1) (column := 30) (row := r) (rotation := 0)
  carry_6 := fun r => Extraction.Circuit.main c (id := 1) (column := 31) (row := r) (rotation := 0)
  carry_7 := fun r => Extraction.Circuit.main c (id := 1) (column := 32) (row := r) (rotation := 0)
  mode32 := fun r => Extraction.Circuit.main c (id := 1) (column := 33) (row := r) (rotation := 0)
  result_is_a := fun r => Extraction.Circuit.main c (id := 1) (column := 34) (row := r) (rotation := 0)
  use_first_byte := fun r => Extraction.Circuit.main c (id := 1) (column := 35) (row := r) (rotation := 0)
  c_is_signed := fun r => Extraction.Circuit.main c (id := 1) (column := 36) (row := r) (rotation := 0)
  b_op_or_sext := fun r => Extraction.Circuit.main c (id := 1) (column := 37) (row := r) (rotation := 0)
  mode32_and_c_is_signed := fun r =>
    Extraction.Circuit.main c (id := 1) (column := 38) (row := r) (rotation := 0)
  gsum := fun r => Extraction.Circuit.main c (id := 2) (column := 0) (row := r) (rotation := 0)
  im_0 := fun r => Extraction.Circuit.main c (id := 2) (column := 1) (row := r) (rotation := 0)
  im_1 := fun r => Extraction.Circuit.main c (id := 2) (column := 2) (row := r) (rotation := 0)
  im_2 := fun r => Extraction.Circuit.main c (id := 2) (column := 3) (row := r) (rotation := 0)
  im_3 := fun r => Extraction.Circuit.main c (id := 2) (column := 4) (row := r) (rotation := 0)

/-! ### The seven F-only constraints, one weld each

Each of these is `Iff.rfl`: the v1 mirror predicate and the generated polynomial
are the same term once the column map is unfolded. They are spelled out one by
one so the identity is readable as source against source; `core_every_row_weld`
below states the same thing for the bundle. -/

/-- `binary.pil:82 mode32*(1-mode32)`. -/
theorem boolean_mode32_weld (c : C F ExtF) (r : ℕ) :
    boolean_mode32 (validOfCircuit c) r
      ↔ Binary.extraction.constraint_0_every_row c r :=
  Iff.rfl

/-- `binary.pil:83 carry[7]*(1-carry[7])`. -/
theorem boolean_carry_7_weld (c : C F ExtF) (r : ℕ) :
    boolean_carry_7 (validOfCircuit c) r
      ↔ Binary.extraction.constraint_1_every_row c r :=
  Iff.rfl

/-- `binary.pil:84 result_is_a*(1-result_is_a)`. -/
theorem boolean_result_is_a_weld (c : C F ExtF) (r : ℕ) :
    boolean_result_is_a (validOfCircuit c) r
      ↔ Binary.extraction.constraint_2_every_row c r :=
  Iff.rfl

/-- `binary.pil:85 use_first_byte*(1-use_first_byte)`. -/
theorem boolean_use_first_byte_weld (c : C F ExtF) (r : ℕ) :
    boolean_use_first_byte (validOfCircuit c) r
      ↔ Binary.extraction.constraint_3_every_row c r :=
  Iff.rfl

/-- `binary.pil:86 c_is_signed*(1-c_is_signed)`. -/
theorem boolean_c_is_signed_weld (c : C F ExtF) (r : ℕ) :
    boolean_c_is_signed (validOfCircuit c) r
      ↔ Binary.extraction.constraint_4_every_row c r :=
  Iff.rfl

/-- `binary.pil:111 b_op_or_sext-((mode32*((c_is_signed+512)-b_op))+b_op)` — the
    only welded Binary constraint with a nontrivial coefficient (`512`). -/
theorem b_op_or_sext_def_weld (c : C F ExtF) (r : ℕ) :
    b_op_or_sext_def_holds (validOfCircuit c) r
      ↔ Binary.extraction.constraint_5_every_row c r :=
  Iff.rfl

/-- `binary.pil:112 mode32_and_c_is_signed-(mode32*c_is_signed)`. -/
theorem mode32_and_c_is_signed_def_weld (c : C F ExtF) (r : ℕ) :
    mode32_and_c_is_signed_def_holds (validOfCircuit c) r
      ↔ Binary.extraction.constraint_6_every_row c r :=
  Iff.rfl

/-- The v1 mirror's whole F-only bundle, welded: `core_every_row` holds *iff*
    the AIR's seven F-only generated constraints do, conjunct for conjunct and
    in the generated order `0`–`6`. Reordering the bundle, or adding or dropping
    a conjunct, breaks this. -/
theorem core_every_row_weld (c : C F ExtF) (r : ℕ) :
    core_every_row (validOfCircuit c) r
      ↔ (Binary.extraction.constraint_0_every_row c r
          ∧ Binary.extraction.constraint_1_every_row c r
          ∧ Binary.extraction.constraint_2_every_row c r
          ∧ Binary.extraction.constraint_3_every_row c r
          ∧ Binary.extraction.constraint_4_every_row c r
          ∧ Binary.extraction.constraint_5_every_row c r
          ∧ Binary.extraction.constraint_6_every_row c r) :=
  Iff.rfl

/-- The v2 Clean mirror's `Spec`, welded to the same seven constraints through
    the live `rowAt` projection of `ZiskFv/AirsClean/Binary/Bridge.lean`.

    `Binary.Spec` is what the Clean Component publishes
    (`ZiskFv/AirsClean/Binary/Circuit.lean`, `Spec := fun row _ _ => Spec row`),
    and its `soundness` field derives it from the component's own `assertZero`
    list. Because this is an `Iff`, `Spec` is exactly the generated conjunction —
    it cannot be quietly weakened to a subset of the AIR's constraints. -/
theorem spec_weld {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]
    (c : C FGL FGL) (r : ℕ) :
    ZiskFv.AirsClean.Binary.Spec (ZiskFv.AirsClean.Binary.rowAt (validOfCircuit c) r)
      ↔ (Binary.extraction.constraint_0_every_row c r
          ∧ Binary.extraction.constraint_1_every_row c r
          ∧ Binary.extraction.constraint_2_every_row c r
          ∧ Binary.extraction.constraint_3_every_row c r
          ∧ Binary.extraction.constraint_4_every_row c r
          ∧ Binary.extraction.constraint_5_every_row c r
          ∧ Binary.extraction.constraint_6_every_row c r) :=
  Iff.rfl

/-- From the *live assertion list* to the generated constraints.

    `StaticLookupSoundness` is Clean `ConstraintsHold.Soundness` over the
    operation list of `mainWithStaticBinaryTable`, which begins with the real
    Binary component's `main`. So this says: whenever the Binary component's own
    constraints hold at a row read out of the extraction circuit `c` at trace
    row `r`, all seven of the AIR's F-only generated constraints hold there.
    Nothing between the two sides is transcribed prose — a drift in an
    `assertZero` expression, not merely in the `Spec`, fails this build. -/
theorem extracted_of_static_lookup {C : Type → Type → Sort u}
    [Extraction.Circuit FGL FGL C] (c : C FGL FGL) (r offset : ℕ)
    (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness (validOfCircuit c)) :
    Binary.extraction.constraint_0_every_row c r
      ∧ Binary.extraction.constraint_1_every_row c r
      ∧ Binary.extraction.constraint_2_every_row c r
      ∧ Binary.extraction.constraint_3_every_row c r
      ∧ Binary.extraction.constraint_4_every_row c r
      ∧ Binary.extraction.constraint_5_every_row c r
      ∧ Binary.extraction.constraint_6_every_row c r :=
  (core_every_row_weld c r).mp
    (ZiskFv.AirsClean.Binary.core_every_row_of_static_lookup
      (validOfCircuit c) r offset env h_static)

end Binary

end ZiskFv.AirsClean.BinaryMirrorWeld
