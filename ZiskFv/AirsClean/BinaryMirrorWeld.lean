import Extraction.Binary
import Extraction.BinaryAdd
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge

/-!
# Machine-checked weld: the Binary-family constraint mirrors ↔ the generated extraction

The Binary AIR family has *two* live handwritten mirrors of the same generated
constraints, and until this module neither was checked against the generated
form by anything but a comment:

* the v1 named-column mirror `ZiskFv/Airs/Binary/Binary.lean` and
  `ZiskFv/Airs/Binary/BinaryAdd.lean` (`Valid_Binary`, `Valid_BinaryAdd`,
  `core_every_row`), each predicate carrying a `mirrors constraint_N_every_row`
  comment;
* the v2 Clean mirror `ZiskFv/AirsClean/Binary/{Spec,Constraints}.lean` and
  `ZiskFv/AirsClean/BinaryAdd/{Spec,Constraints}.lean`, whose `Constraints.lean`
  docstrings cite `binary.pil` / `binary_add.pil` line numbers.

A mistyped column index or a dropped coefficient in either mirror compiles fine
and silently proves soundness of a circuit that is not ZisK's. The theorems
below replace those comments with compiled identities.

## Coverage — stated without rounding up

The family emits 31 generated constraints. **11 of them are welded here**; the
other 20 are outside the F-only slice and are not `assertZero` constraints of
any mirror:

| AIR | generated | F-only | welded |
| --- | --- | --- | --- |
| `Binary` | 14 (`constraint_0` … `constraint_13`) | 7 (`0`–`6`) | 7 |
| `BinaryAdd` | 9 (`constraint_0` … `constraint_8`) | 4 (`0`–`3`) | 4 |
| `BinaryExtension` | 8 (`constraint_0` … `constraint_7`) | 0 | 0 |

The split is not a judgement call: the extractor emits F-only constraints with a
two-field signature `{F ExtF : Type} [Field F] [Field ExtF]
[Extraction.Circuit F ExtF C]`, and challenge-mixing ones with the single-field
signature `{F : Type} [Extraction.Circuit F F C]` under the comment
`-- Mixed witness/challenge constraint emitted for single-field circuits.`
The v1-mirror welds below are stated at a circuit with `F` and `ExtF` *separate*
universally quantified type variables, so those welds are themselves the check
that the eleven constraints they name are in the F-only class. (The v2-mirror
welds specialise to `F = ExtF = FGL`, because the Clean row types
`BinaryRow FGL` / `BinaryAddRow FGL` and their `Spec`s are `FGL`-specific; they
name the same eleven constraints.)

`BinaryExtension` contributes nothing: all eight of its generated constraints
carry the single-field signature (`build/extraction/Extraction/BinaryExtension.lean`
lines 52, 58, 64, 70, 76, 82, 88, 94), and its mirrors correspondingly assert
nothing — `ZiskFv/AirsClean/BinaryExtension/Spec.lean` sets `Spec := True` and
`ZiskFv/Airs/Binary/BinaryExtension.lean` declares accessors with no constraint
predicates. That is a correct agreement with zero coverage gain; it is recorded
here rather than dressed up as eight welds.

## How the weld avoids the `Extraction.Circuit`-instance hazard

The usual way to instantiate a generated constraint at a mirror row type is to
declare an `Extraction.Circuit` instance over that row and read columns out of
it. That shape has a hole: a handwritten column map is pinned (by review or by a
gate), but nothing pins the instance's `main` field to that map, so rebinding
`main` leaves the welds talking about a different circuit.

This module never declares an `Extraction.Circuit` instance. It goes the other
way: `validOfCircuit` reads a `Valid_Binary` / `Valid_BinaryAdd` *out of an
arbitrary circuit* `c : C F ExtF`, and every weld is universally quantified over
`C`, `F`, `ExtF`, `c` and the trace row `r`. There is consequently

* no instance to rebind,
* no `preprocessed` / `challenge` / `exposed` stub a weld could rest on,
* no `| _ => 0` default arm in the column map (all 44 + 13 arms are genuine
  cell reads), and
* no companion "the instance is pinned" theorem to remember to write.

## What the welds do and do not certify

* `core_every_row_weld` and `spec_weld` are `Iff`s, so each mirror asserts
  neither less nor more than the corresponding run of generated constraints.
* `extracted_of_static_lookup` and `binaryAdd_spec_of_extracted` tie the
  generated constraints to the mirrors' *live* proof surface, not to transcribed
  prose: the first consumes `StaticLookupSoundness`, i.e. Clean
  `ConstraintsHold.Soundness` over the operation list of the real Binary
  component `main`, and the second routes through
  `spec_of_core_every_row_via_component`, which goes through the Clean
  Component's own `soundness` field.
* They do **not** certify the column map itself. `validOfCircuit` is
  handwritten, so a *compensating* pair of slips — the mirror and the map wrong
  in the same direction — would still be `rfl`. Every column the welded
  constraints read is pinned relative to the others (swapping two of them breaks
  the weld), but the absolute layout is checked only against the extractor's
  column-name header, quoted at each `validOfCircuit` below.
* Coverage of Binary's *columns* is much narrower than coverage of its
  constraints. Its seven F-only constraints read only stage-1 columns
  `{0, 32, 33, 34, 35, 36, 37, 38}`. Columns `1`–`31` — every `free_in_a/b/c`
  byte and `carry[0..6]` — appear only in `constraint_7` … `constraint_13`,
  which mix `Extraction.Circuit.challenge`; those are exactly the columns
  `opBusMessageExpr` and the eight `lookupMessageK` tuples of
  `ZiskFv/AirsClean/Binary/Constraints.lean` read. Binary's highest-risk
  transcription surface therefore stays comment-asserted after this module.
  `BinaryAdd` has no such gap: its four constraints read all ten of its stage-1
  columns, so its whole stage-1 map is pinned by the welds.

## Evidence that this catches what it claims to catch

The failure mode this module exists for is a *self-consistent* slip: the mirror
stack agreeing with itself and disagreeing with the pilout. That was reproduced.
Rewriting the `512` of `binary.pil:111` to `511` at all seven handwritten sites
that carry it — `ZiskFv/Airs/Binary/Binary.lean`,
`ZiskFv/AirsClean/Binary/{Spec,Constraints,Soundness,Circuit,Bridge}.lean` (twice
in `Circuit.lean`) — leaves the *entire rest of the build green*, including the
component's own soundness and completeness proofs, and fails only here, at
`b_op_or_sext_def_weld` and `core_every_row_weld`. Mutating a single site
instead fails inside `Binary/Bridge.lean`, i.e. the existing proofs already pin
the mirror to itself; what they cannot pin is the mirror to the extraction.

Two caveats on the error messages a future slip will produce. The v1 welds are
stated over an abstract field, so nothing is ever numerically reduced and a slip
reports as a clean `Type mismatch`. `spec_weld` and `constraints_at_weld` are at
`FGL = Fin 18446744069414584321`, where `Iff.rfl` tries to evaluate numerals and
a slip surfaces as `maximum recursion depth has been reached` instead — a
failure, but an uninformative one; read the v1 weld's message.

## Trust note

No `axiom`, `sorry`, `native_decide` or other trust marker is added. Every weld
is `Iff.rfl` except `constraints_at_weld`, which additionally crosses the
`a - b` / `a + -b` normal-form gap by `simp only [..., sub_eq_add_neg]` over the
`Iff.rfl` weld; see the note there.
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

/-! ## BinaryAdd -/

namespace BinaryAdd

open ZiskFv.Airs.BinaryAdd (Valid_BinaryAdd core_every_row boolean_cout_0 boolean_cout_1
  carry_chain_0 carry_chain_1)

variable {C : Type → Type → Sort u} {F ExtF : Type} [Field F] [Field ExtF]
  [Extraction.Circuit F ExtF C]

/-- The BinaryAdd AIR's witness row, read out of an arbitrary
    `Extraction.Circuit`.

    Column indices transcribed from the extractor's column-name header at
    `build/extraction/Extraction/BinaryAdd.lean:13-26`: stage 1
    `0` `a[0]`, `1` `a[1]`, `2` `b[0]`, `3` `b[1]`, `4`–`7` `c_chunks[0..3]`,
    `8` `cout[0]`, `9` `cout[1]`; stage 2 `0` `gsum`, `1`–`2` `im_cluster`.

    Unlike Binary's, this map is fully pinned by the welds below: BinaryAdd's
    four F-only constraints read all ten stage-1 columns. -/
@[reducible]
def validOfCircuit (c : C F ExtF) : Valid_BinaryAdd F ExtF where
  a_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 0) (row := r) (rotation := 0)
  a_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 1) (row := r) (rotation := 0)
  b_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 2) (row := r) (rotation := 0)
  b_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 3) (row := r) (rotation := 0)
  c_chunks_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 4) (row := r) (rotation := 0)
  c_chunks_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 5) (row := r) (rotation := 0)
  c_chunks_2 := fun r => Extraction.Circuit.main c (id := 1) (column := 6) (row := r) (rotation := 0)
  c_chunks_3 := fun r => Extraction.Circuit.main c (id := 1) (column := 7) (row := r) (rotation := 0)
  cout_0 := fun r => Extraction.Circuit.main c (id := 1) (column := 8) (row := r) (rotation := 0)
  cout_1 := fun r => Extraction.Circuit.main c (id := 1) (column := 9) (row := r) (rotation := 0)
  gsum := fun r => Extraction.Circuit.main c (id := 2) (column := 0) (row := r) (rotation := 0)
  im_0 := fun r => Extraction.Circuit.main c (id := 2) (column := 1) (row := r) (rotation := 0)
  im_1 := fun r => Extraction.Circuit.main c (id := 2) (column := 2) (row := r) (rotation := 0)

/-- `binary_add.pil:14 cout[0]*(1-cout[0])`. -/
theorem boolean_cout_0_weld (c : C F ExtF) (r : ℕ) :
    boolean_cout_0 (validOfCircuit c) r
      ↔ BinaryAdd.extraction.constraint_0_every_row c r :=
  Iff.rfl

/-- `binary_add.pil:19 (a[0]+b[0])-(((cout[0]*4294967296)+(c_chunks[1]*65536))+c_chunks[0])`
    — the low-lane carry chain, with the `2^32` and `2^16` weights. -/
theorem carry_chain_0_weld (c : C F ExtF) (r : ℕ) :
    carry_chain_0 (validOfCircuit c) r
      ↔ BinaryAdd.extraction.constraint_1_every_row c r :=
  Iff.rfl

/-- `binary_add.pil:14 cout[1]*(1-cout[1])`. -/
theorem boolean_cout_1_weld (c : C F ExtF) (r : ℕ) :
    boolean_cout_1 (validOfCircuit c) r
      ↔ BinaryAdd.extraction.constraint_2_every_row c r :=
  Iff.rfl

/-- `binary_add.pil:19 ((a[1]+b[1])+cout[0])-(((cout[1]*4294967296)+(c_chunks[3]*65536))+c_chunks[2])`
    — the high-lane carry chain, folding `cout[0]` in as carry-in. -/
theorem carry_chain_1_weld (c : C F ExtF) (r : ℕ) :
    carry_chain_1 (validOfCircuit c) r
      ↔ BinaryAdd.extraction.constraint_3_every_row c r :=
  Iff.rfl

/-- The v1 mirror's whole F-only bundle, welded, in the generated order
    `0`–`3` (note that the generated order interleaves the two booleanity
    constraints with the two carry-chain constraints). -/
theorem core_every_row_weld (c : C F ExtF) (r : ℕ) :
    core_every_row (validOfCircuit c) r
      ↔ (BinaryAdd.extraction.constraint_0_every_row c r
          ∧ BinaryAdd.extraction.constraint_1_every_row c r
          ∧ BinaryAdd.extraction.constraint_2_every_row c r
          ∧ BinaryAdd.extraction.constraint_3_every_row c r) :=
  Iff.rfl

/-! ### The v2 Clean mirror

`ZiskFv/AirsClean/BinaryAdd/Spec.lean`'s `Spec` is *semantic*
(`cPacked = (packed32 a + packed32 b) % 2^64`), not a restatement of the four
raw constraints, so there is no `Iff.rfl` weld for it. The raw four appear
instead as the hypotheses of `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`'s
`constraints_at`, in the `a + -b = 0` shape Clean's assertion list normalizes
to. `constraints_at_weld` pins that shape to the generated polynomials, and
`binaryAdd_spec_of_extracted` cashes it into the semantic `Spec` through the
Clean Component's own soundness proof. -/

/-- The `a + -b` normal form of `constraints_at` is the generated `a - b` form.

    `Iff.rfl` does *not* close this: Clean's assertion list normalizes to
    `a + -b = 0` while the extractor emits `a - b = 0`, and those are not
    definitionally equal. All of the `rfl`-level content is carried by
    `core_every_row_weld`, which this rewrites by; the `simp only` that follows
    is allowed exactly one lemma beyond unfolding, `sub_eq_add_neg`, so no
    algebraic normalization can absorb a transcription slip. Dropping
    `sub_eq_add_neg` from that list leaves the goal open with the two normal
    forms side by side, which is the check that this step is load-bearing rather
    than decorative. -/
theorem constraints_at_weld {C : Type → Type → Sort u} [Extraction.Circuit FGL FGL C]
    (c : C FGL FGL) (r : ℕ) :
    ZiskFv.AirsClean.BinaryAdd.constraints_at (validOfCircuit c) r
      ↔ (BinaryAdd.extraction.constraint_0_every_row c r
          ∧ BinaryAdd.extraction.constraint_1_every_row c r
          ∧ BinaryAdd.extraction.constraint_2_every_row c r
          ∧ BinaryAdd.extraction.constraint_3_every_row c r) := by
  rw [← core_every_row_weld c r]
  simp only [ZiskFv.AirsClean.BinaryAdd.constraints_at, core_every_row,
    boolean_cout_0, carry_chain_0, boolean_cout_1, carry_chain_1, sub_eq_add_neg]

/-- Generated constraints plus the AIR's column range facts give the v2 mirror's
    *semantic* Spec — 64-bit addition of the packed operands — routed through
    `spec_of_core_every_row_via_component`, i.e. through the Clean Component's
    own `soundness` field.

    The range hypotheses are the same ones the existing consumers supply; this
    theorem adds no assumption that was not already required to conclude
    `BinaryAdd.Spec`. What it removes is the comment: the four constraints
    feeding that conclusion are now the extractor's, not a transcription. -/
theorem binaryAdd_spec_of_extracted {C : Type → Type → Sort u}
    [Extraction.Circuit FGL FGL C] (c : C FGL FGL) (r : ℕ)
    (h_a_range : ZiskFv.Airs.BinaryAdd.a_chunks_in_range (validOfCircuit c) r)
    (h_b_range : ZiskFv.Airs.BinaryAdd.b_chunks_in_range (validOfCircuit c) r)
    (h_c_range : ZiskFv.Airs.BinaryAdd.c_chunks_in_range (validOfCircuit c) r)
    (h : BinaryAdd.extraction.constraint_0_every_row c r
          ∧ BinaryAdd.extraction.constraint_1_every_row c r
          ∧ BinaryAdd.extraction.constraint_2_every_row c r
          ∧ BinaryAdd.extraction.constraint_3_every_row c r) :
    ZiskFv.AirsClean.BinaryAdd.Spec
      (ZiskFv.AirsClean.BinaryAdd.rowAt (validOfCircuit c) r) :=
  ZiskFv.AirsClean.BinaryAdd.spec_of_core_every_row_via_component
    (validOfCircuit c) r ((core_every_row_weld c r).mpr h) h_a_range h_b_range h_c_range

end BinaryAdd

end ZiskFv.AirsClean.BinaryMirrorWeld
