import Extraction.Arith
import ZiskFv.AirsClean.ArithCompleteConstraints

/-!
# Machine-checked weld: Arith constraint mirror ↔ generated extraction

`ZiskFv/AirsClean/ArithCompleteConstraints.lean` asserts a handwritten mirror of
the Arith AIR's local constraints and cites the generated
`Extraction.Arith.constraint_N_every_row` definitions in comments only. Comments
are not checked by anything, so a transcription slip in the mirror would be
invisible to the build.

This module replaces the comment citation with compiled identities covering all
49 of the AIR's F-only constraints, `constraint_0_every_row` …
`constraint_48_every_row` (eth-act/zisk-fv#296). Every one is `rfl`-level except
`constraint_36`, the single member of the set whose mirror is not term-identical
to the extraction.

## How the weld works

`Extraction.Arith.constraint_N_every_row` is stated against the abstract
`Extraction.Circuit` interface: its body only ever mentions
`Extraction.Circuit.main c (id := 1) (column := k) (row := r) (rotation := 0)`.
`ExtractedArithRow` below is an `Extraction.Circuit` instance whose stage-1
column `k` reads field `k` of an `ArithMulRow`, using the column layout printed
by the extractor at `build/extraction/Extraction/Arith.lean:13-57`. Instantiating
a generated constraint at that circuit therefore turns it into a polynomial over
`ArithMulRow` fields, and the weld theorems say that polynomial is *definitionally*
the one the mirror asserts.

## What the weld does and does not certify

* It certifies, by `Iff.rfl`, that the welded mirror polynomials are the generated
  polynomials — same columns, same coefficients, same shape.
* Coverage is the whole F-only set: the 49 generated constraints
  `constraint_0_every_row` … `constraint_48_every_row` each appear on the right of
  a weld below. The other 16 generated constraints read stage-2 columns and the
  challenge lane and are not `assertZero` constraints of the Clean component at
  all; they are out of scope here.
* For 37 of the 49 — `0`–`5`, `9`–`30`, `39`–`45`, `47`–`48` — the tie is to the
  *live* assertion list, not to transcribed prose: `divModeSpec_weld`,
  `divBoundarySpec_weld`, `divInverseSumSpec_weld`, `divScopeSpec_weld` and
  `divWModeSpec_weld` are `Iff`s against the mirror predicates that the
  already-proved `sharedDivBlockSpec_of_soundness` extracts from
  `sharedMainComplete`'s own `assertZero`s, and `extracted_of_sharedMainComplete`
  composes the two. A slip that is self-consistent across the `Spec` predicate,
  the `assertZero` expression and that projection proof — the exact failure this
  module exists to catch — breaks the weld and nothing else.
* For the remaining 12 (`6`–`8`, `31`–`38` via `spec_carryChain_weld`, `46` via
  `c46Spec_weld`) the weld is against `Spec` and `C46Spec`, the mirror predicates
  the ArithMul component publishes. This module does **not** re-derive those two
  from the component's `assertZero` list; that link lives in the component's own
  soundness proof.
* The five `Iff` welds pin their mirror predicates exactly — the predicate holds
  *iff* the corresponding run of generated constraints does — so for those 37 the
  mirror asserts neither less nor more than the AIR. `spec_carryChain_weld` is an
  implication only, so it does not forbid `Spec` asserting more than the AIR does.
* It does **not** certify the column layout itself: `mainValue` is handwritten.
  That map is pinned separately by `trust/scripts/check-arith-column-map.py`,
  against the extractor's own column-name header as recorded in
  `trust/generated/arith-stage1-columns.txt`. Without that gate a *compensating*
  pair of slips (mirror and map wrong in the same direction) would still be `rfl`.
  That gate reads `mainValue` and nothing else, so `extractedArithRowCircuit_pinned`
  below ties the instance the welds actually resolve to the map the gate actually
  pins; see the section comment there for the hole it closes.
* It does **not** rest on `mainValue`'s `0` answers outside the modeled lanes,
  nor on the `preprocessed`/`challenge`/`exposed` stubs. That is checked by
  `fOnlyConstraints_readOnlyModeledLanes` and `weldedConstraints_probeBridge`,
  not assumed; see "Which lanes a welded constraint is allowed to read".

## Trust note

No axiom, `sorry`, `native_decide`, or other trust marker is added. Every weld
below is `Iff.rfl` except `constraint_36_of_spec`, which is `linear_combination`
over a `rfl`-pinned restatement of the generated polynomial (see there).
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

/-- An `Extraction.Circuit` whose stage-1 columns are the fields of a single
    `ArithMulRow`. Only used to instantiate the generated `Arith` constraint
    predicates at the mirror's row type. -/
structure ExtractedArithRow (F ExtF : Type) where
  row : ArithMulRow FGL

/-- Arith AIR stage-1 column layout, transcribed from the generated header
    `build/extraction/Extraction/Arith.lean:13-57` (`stage 1 col N: <name>`).

    This is the *only* handwritten datum the weld introduces; it is checked
    against that same generated header (recorded in
    `trust/generated/arith-stage1-columns.txt`) by
    `trust/scripts/check-arith-column-map.py`.
    Stage 2 (`gsum`, `im_*`) is not modeled: the generated constraints that read
    stage-2 columns (`constraint_49..64`) mix in `Extraction.Circuit.challenge`
    and are represented in the Clean component by channel `push`/`lookup`
    operations, not by `assertZero`. -/
@[reducible]
def mainValue (c : ExtractedArithRow FGL FGL) (id column _row _rotation : ℕ) : FGL :=
  if id = 1 then
    match column with
    | 0 => c.row.carries.carry_0
    | 1 => c.row.carries.carry_1
    | 2 => c.row.carries.carry_2
    | 3 => c.row.carries.carry_3
    | 4 => c.row.carries.carry_4
    | 5 => c.row.carries.carry_5
    | 6 => c.row.carries.carry_6
    | 7 => c.row.chunks.a_0
    | 8 => c.row.chunks.a_1
    | 9 => c.row.chunks.a_2
    | 10 => c.row.chunks.a_3
    | 11 => c.row.chunks.b_0
    | 12 => c.row.chunks.b_1
    | 13 => c.row.chunks.b_2
    | 14 => c.row.chunks.b_3
    | 15 => c.row.chunks.c_0
    | 16 => c.row.chunks.c_1
    | 17 => c.row.chunks.c_2
    | 18 => c.row.chunks.c_3
    | 19 => c.row.chunks.d_0
    | 20 => c.row.chunks.d_1
    | 21 => c.row.chunks.d_2
    | 22 => c.row.chunks.d_3
    | 23 => c.row.flags.na
    | 24 => c.row.flags.nb
    | 25 => c.row.flags.nr
    | 26 => c.row.flags.np
    | 27 => c.row.flags.sext
    | 28 => c.row.flags.m32
    | 29 => c.row.flags.div
    | 30 => c.row.carries.fab
    | 31 => c.row.carries.na_fb
    | 32 => c.row.carries.nb_fa
    | 33 => c.row.flags.main_div
    | 34 => c.row.flags.main_mul
    | 35 => c.row.flags.signed
    | 36 => c.row.flags.div_by_zero
    | 37 => c.row.flags.div_overflow
    | 38 => c.row.carries.inv_sum_all_bs
    | 39 => c.row.flags.op
    | 40 => c.row.flags.bus_res1
    | 41 => c.row.flags.multiplicity
    | 42 => c.row.flags.range_ab
    | 43 => c.row.flags.range_cd
    | _ => 0
  else
    0

instance extractedArithRowCircuit : Extraction.Circuit FGL FGL ExtractedArithRow where
  main := mainValue
  preprocessed := fun _ _ _ _ => 0
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

@[reducible]
def extractedArithRow (row : ArithMulRow FGL) : ExtractedArithRow FGL FGL := ⟨row⟩

/-! ## Welds

Each theorem in this section is `Iff.rfl`: the mirror's polynomial and the
generated polynomial are the same term after unfolding the column map. Three
constraints are spelled out longhand first, so the identity is readable as
source against source; the predicate-level welds that follow cover the whole
F-only set without restating every polynomial.
-/

/-- `arith/pil/arith.pil:212 div*(1-div)` — the plain boolean shape.

    Mirror: the seventh conjunct of `DivModeSpec`
    (`ZiskFv/AirsClean/ArithMul/Spec.lean`), asserted by `sharedMainComplete`. -/
theorem constraint_39_weld (row : ArithMulRow FGL) :
    (row.flags.div * (1 - row.flags.div) = 0)
      ↔ Arith.extraction.constraint_39_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-- `arith/pil/arith.pil:71 div_by_zero*(a[2]-((1-m32)*65535))` — a boundary pin
    with the `m32` width factor.

    Mirror: the seventh conjunct of `DivBoundarySpec`. -/
theorem constraint_15_weld (row : ArithMulRow FGL) :
    (row.flags.div_by_zero * (row.chunks.a_2 - (1 - row.flags.m32) * 65535) = 0)
      ↔ Arith.extraction.constraint_15_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-- `arith/pil/arith.pil:92 (div-div_by_zero)*(1-(inv_sum_all_bs*(((b[0]+b[1])+b[2])+b[3])))`
    — the nonzero-divisor detector.

    Mirror: `DivInverseSumSpec` in full. -/
theorem constraint_25_weld (row : ArithMulRow FGL) :
    ((row.flags.div - row.flags.div_by_zero) *
        (1 - row.carries.inv_sum_all_bs *
          (((row.chunks.b_0 + row.chunks.b_1) + row.chunks.b_2) + row.chunks.b_3)) = 0)
      ↔ Arith.extraction.constraint_25_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-! ### The mirror `Spec` predicates, welded

The three statements above are spelled out so the weld reads as a source-to-source
identity. These restate them against the actual predicates the ArithMul component
publishes, so the weld breaks if either the `Spec` or the generated file drifts. -/

theorem divInverseSumSpec_weld (row : ArithMulRow FGL) :
    DivInverseSumSpec row
      ↔ Arith.extraction.constraint_25_every_row (extractedArithRow row) 0 :=
  Iff.rfl

theorem divModeSpec_div_boolean_weld (row : ArithMulRow FGL) :
    DivModeSpec row → Arith.extraction.constraint_39_every_row (extractedArithRow row) 0 :=
  fun h => h.2.2.2.2.2.2.1

theorem divBoundarySpec_a2_weld (row : ArithMulRow FGL) :
    DivBoundarySpec row → Arith.extraction.constraint_15_every_row (extractedArithRow row) 0 :=
  fun h => h.2.2.2.2.2.2.1

/-! ### The rest of the shared Div block

`divInverseSumSpec_weld` above welds the mirror's one-conjunct
`DivInverseSumSpec`. These weld the other four components of
`SharedDivBlockSpec` wholesale: each `Iff.rfl` says the mirror predicate is,
conjunct for conjunct and in order, the corresponding run of generated
constraints. Between them they cover 37 of the AIR's 49 F-only constraints —
`0`–`5`, `9`–`30`, `39`–`45`, `47`–`48` — and `sharedDivBlockSpec_of_soundness`
already derives all of `SharedDivBlockSpec` from the live `sharedMainComplete`
assertion list, so these are welds of asserted constraints, not of transcribed
prose. The remaining 12 (`6`–`8`, `31`–`38`, `46`) are asserted through `main`
and are welded below. -/

/-- `arith/pil/arith.pil:50-55,212-218` — the thirteen mode/sign boolean pins. -/
theorem divModeSpec_weld (row : ArithMulRow FGL) :
    DivModeSpec row ↔
      Arith.extraction.constraint_0_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_1_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_2_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_3_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_4_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_5_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_39_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_40_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_41_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_42_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_43_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_44_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_45_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-- `arith/pil/arith.pil:64,69-72,75-78,81-84` — the sixteen div-by-zero and
    div-overflow chunk boundary pins. -/
theorem divBoundarySpec_weld (row : ArithMulRow FGL) :
    DivBoundarySpec row ↔
      Arith.extraction.constraint_9_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_10_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_11_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_12_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_13_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_14_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_15_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_16_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_17_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_18_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_19_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_20_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_21_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_22_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_23_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_24_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-- `arith/pil/arith.pil:95,98-99,101-102` — the five flag-scoping products. -/
theorem divScopeSpec_weld (row : ArithMulRow FGL) :
    DivScopeSpec row ↔
      Arith.extraction.constraint_26_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_27_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_28_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_29_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_30_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-- `arith/pil/arith.pil:264-265` — the two `m32` (W-mode) high-half pins. -/
theorem divWModeSpec_weld (row : ArithMulRow FGL) :
    DivWModeSpec row ↔
      Arith.extraction.constraint_47_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_48_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-- `arith/pil/arith.pil:262` — the `bus_res1` output mux. -/
theorem c46Spec_weld (row : ArithMulRow FGL) :
    C46Spec row ↔ Arith.extraction.constraint_46_every_row (extractedArithRow row) 0 :=
  Iff.rfl

/-! ### The one constraint that is not a verbatim transcription

`constraint_36` (`arith/pil/arith.pil:207`, the `carry[4] -> carry[5]` link of the
MUL carry chain) is the single member of the Arith AIR's F-only constraint set
whose mirror is not term-identical to the generated polynomial: the mirror
(`ZiskFv/AirsClean/ArithMul/Spec.lean`, the ninth conjunct of `Spec`;
`ZiskFv/AirsClean/ArithMul/Constraints.lean`, the matching `assertZero`) writes

    ... + b_1 * na_fb * (1 - m32) + a_1 * nb_fa * (1 - m32) + ...

whereas `build/extraction/Extraction/Arith.lean` emits those two addends in the
opposite order. The difference is commutativity of `+`, so it is semantically
inert — but it is exactly the kind of divergence a comment-only citation hides,
and it is why the weld for this constraint is `linear_combination` rather than
`rfl`. Do not "fix" it by reordering `Constraints.lean`: that `main` definition is
consumed by `linear_combination` proofs in `ZiskFv/AirsClean/ArithMul/Circuit.lean`.

`gen36` restates the generated polynomial in the generated order; `gen36_pin`
checks that restatement against the extraction by `Iff.rfl`, so no algebraic
normalization is allowed to hide a transcription slip — `linear_combination` is
then used only to cross the commuted addend pair. -/

/-- `constraint_36_every_row`'s polynomial, written in the order the extractor
    emits it. Pinned to the generated definition by `gen36_pin`. -/
@[reducible]
def gen36 (row : ArithMulRow FGL) : Prop :=
  row.carries.fab * row.chunks.a_3 * row.chunks.b_2
    + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
    + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
    + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
    - row.chunks.d_1 * (1 - row.flags.div)
    + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
    + row.carries.carry_4
    - row.carries.carry_5 * 65536 = 0

theorem gen36_pin (row : ArithMulRow FGL) :
    gen36 row ↔ Arith.extraction.constraint_36_every_row (extractedArithRow row) 0 :=
  Iff.rfl

theorem constraint_36_of_spec (row : ArithMulRow FGL) :
    Spec row → Arith.extraction.constraint_36_every_row (extractedArithRow row) 0 := by
  intro h
  refine (gen36_pin row).mp ?_
  show _ = (0 : FGL)
  -- The type ascription is the mirror's `Spec` conjunct, spelled out: it differs
  -- from `gen36` only in the order of the `na_fb`/`nb_fa` addends.
  linear_combination (h.2.2.2.2.2.2.2.2.1 :
    row.carries.fab * row.chunks.a_3 * row.chunks.b_2
      + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
      + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
      + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
      - row.chunks.d_1 * (1 - row.flags.div)
      + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
      + row.carries.carry_4
      - row.carries.carry_5 * 65536 = 0)

/-! ### The carry chain, welded

`Spec` (`ZiskFv/AirsClean/ArithMul/Spec.lean`) is the mirror of the eleven
constraints the ArithMul component asserts through `main`: the three sign-product
definitions `6`-`8` and the eight-limb carry chain `31`-`38`. Ten of the eleven
are `rfl`-level — each conjunct below is a bare projection out of `Spec`, so it
typechecks only because the mirror conjunct and the generated polynomial are the
same term. The eleventh is `constraint_36`, handled just above. -/
theorem spec_carryChain_weld (row : ArithMulRow FGL) :
    Spec row →
      Arith.extraction.constraint_6_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_7_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_8_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_31_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_32_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_33_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_34_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_35_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_36_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_37_every_row (extractedArithRow row) 0
      ∧ Arith.extraction.constraint_38_every_row (extractedArithRow row) 0 :=
  fun h => ⟨
    h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, constraint_36_of_spec row h, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

/-! ### From the live assertion list

`sharedDivBlockSpec_of_soundness` (`ZiskFv/AirsClean/ArithCompleteConstraints.lean`)
already projects `SharedDivBlockSpec` out of the `sharedMainComplete` operation
list. Composing it with the welds above gives the generated constraints directly
from the mirror circuit's own assertions, which is what makes a drift in the
`assertZero` expressions — not just in the `Spec` — a build failure. -/

theorem extracted_of_sharedMainComplete
    (offset : ℕ) (env : Environment FGL) (row : Var ArithMulRow FGL)
    (h : ConstraintsHold.Soundness env ((sharedMainComplete row).operations offset)) :
    (Arith.extraction.constraint_0_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_1_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_2_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_3_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_4_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_5_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_39_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_40_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_41_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_42_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_43_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_44_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_45_every_row (extractedArithRow (eval env row)) 0)
      ∧ (Arith.extraction.constraint_9_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_10_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_11_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_12_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_13_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_14_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_15_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_16_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_17_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_18_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_19_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_20_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_21_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_22_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_23_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_24_every_row (extractedArithRow (eval env row)) 0)
      ∧ (Arith.extraction.constraint_25_every_row (extractedArithRow (eval env row)) 0)
      ∧ (Arith.extraction.constraint_26_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_27_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_28_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_29_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_30_every_row (extractedArithRow (eval env row)) 0)
      ∧ (Arith.extraction.constraint_47_every_row (extractedArithRow (eval env row)) 0
       ∧ Arith.extraction.constraint_48_every_row (extractedArithRow (eval env row)) 0) := by
  have hspec := sharedDivBlockSpec_of_soundness offset env row h
  exact ⟨(divModeSpec_weld _).mp hspec.1, (divBoundarySpec_weld _).mp hspec.2.1,
    (divInverseSumSpec_weld _).mp hspec.2.2.1, (divScopeSpec_weld _).mp hspec.2.2.2.1,
    (divWModeSpec_weld _).mp hspec.2.2.2.2⟩

/-! ## Which lanes a welded constraint is allowed to read

`mainValue` is total, so it has to answer somewhere it is not modeling: it
returns `0` for every stage-2 read (`id ≠ 1`) and for every stage-1 column
`≥ 44`, and, ignoring its `row` and `rotation` arguments, it returns the same
cell at every trace row and every rotation. `extractedArithRowCircuit` stubs the
`preprocessed`, `challenge` and `exposed` lanes to `0` outright. Those answers
are only harmless if no welded constraint can observe them; if one could, the
weld would be certifying a polynomial the AIR does not assert. This section
checks that instead of asserting it.

`ArithProbe` is the *free* `Extraction.Circuit`: every lane is an unconstrained
function field. Instantiating a generated constraint there turns each cell read
into an application of a variable, so a `rfl`-level identity between a probe
circuit and its restriction is a statement about which cells the generated body
mentions — not about their values. -/

/-- The free `Extraction.Circuit` over `FGL`: each lane is a function field. -/
structure ArithProbe (F ExtF : Type) where
  mainCell : ℕ → ℕ → ℕ → ℕ → FGL
  preprocessedCell : ℕ → ℕ → ℕ → FGL
  challengeCell : ℕ → FGL
  exposedCell : ℕ → FGL

instance arithProbeCircuit : Extraction.Circuit FGL FGL ArithProbe where
  main c := c.mainCell
  preprocessed c := c.preprocessedCell
  challenge c := c.challengeCell
  exposed c := c.exposedCell

/-- `c` cut down to the lanes `extractedArithRowCircuit` actually models: stage 1,
    columns `< 44`, rotation `0`, the single trace row `r`; `0` everywhere else,
    including all of `preprocessed`, `challenge` and `exposed`. -/
@[reducible]
def restrictToModeledLanes (c : ArithProbe FGL FGL) (r : ℕ) : ArithProbe FGL FGL where
  mainCell := fun id column _row rotation =>
    if id = 1 ∧ column < 44 ∧ rotation = 0 then c.mainCell id column r rotation else 0
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- `P c r` is unchanged by zeroing every lane `extractedArithRowCircuit` stubs.

    Unfolded: `P c r` may mention `c.mainCell 1 k r 0` for `k < 44` and nothing
    else. A read of a stage-2 column, of stage-1 column `≥ 44`, of a rotation
    other than `0`, of a trace row other than `r`, or of `preprocessed`,
    `challenge` or `exposed` would leave a free `c.<lane> …` on the left of the
    `Iff` with no counterpart on the right, and `Iff.rfl` would not typecheck. -/
@[reducible]
def ReadsOnlyModeledLanes (P : ArithProbe FGL FGL → ℕ → Prop) : Prop :=
  ∀ (c : ArithProbe FGL FGL) (r : ℕ), P c r ↔ P (restrictToModeledLanes c r) r

/-- Each of the Arith AIR's 49 F-only constraints reads only the lanes
    `extractedArithRowCircuit` models.

    The property is not vacuous: `ReadsOnlyModeledLanes` asserted of
    `constraint_63_every_row` (which reads `challenge` and `preprocessed`) or of
    `constraint_64_every_row` (which reads `preprocessed` and `exposed`) fails to
    elaborate, with `Iff.rfl` rejected against the stated `Iff`. Those two are
    among the 16 generated constraints outside the F-only set
    (`constraint_49_every_row` … `constraint_64_every_row`), which read stage-2
    columns (`id := 2`) and the challenge lane; they are represented in the Clean
    component by channel `push`/`lookup` operations rather than `assertZero`, and
    nothing in this module welds them. -/
theorem fOnlyConstraints_readOnlyModeledLanes :
    ReadsOnlyModeledLanes Arith.extraction.constraint_0_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_1_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_2_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_3_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_4_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_5_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_6_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_7_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_8_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_9_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_10_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_11_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_12_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_13_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_14_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_15_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_16_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_17_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_18_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_19_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_20_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_21_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_22_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_23_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_24_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_25_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_26_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_27_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_28_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_29_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_30_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_31_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_32_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_33_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_34_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_35_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_36_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_37_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_38_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_39_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_40_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_41_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_42_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_43_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_44_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_45_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_46_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_47_every_row
    ∧
    ReadsOnlyModeledLanes Arith.extraction.constraint_48_every_row :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- `extractedArithRow row` re-expressed in the free circuit: `mainValue` in the
    stage-1 lane, `0` in every stub lane. -/
@[reducible]
def probeOfRow (row : ArithMulRow FGL) : ArithProbe FGL FGL where
  mainCell := mainValue (extractedArithRow row)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- The bridge from `extractedArithRowCircuit`, at which every weld above is
    stated, into the free circuit. Composed with
    `fOnlyConstraints_readOnlyModeledLanes` it gives: none of the four welded
    constraints can observe a stubbed lane, so the `0` defaults in `mainValue`
    and the `preprocessed`/`challenge`/`exposed` stubs cannot be what makes a
    weld true. -/
theorem weldedConstraints_probeBridge (row : ArithMulRow FGL) (r : ℕ) :
    (Arith.extraction.constraint_15_every_row (extractedArithRow row) r
        ↔ Arith.extraction.constraint_15_every_row (probeOfRow row) r)
      ∧ (Arith.extraction.constraint_25_every_row (extractedArithRow row) r
        ↔ Arith.extraction.constraint_25_every_row (probeOfRow row) r)
      ∧ (Arith.extraction.constraint_36_every_row (extractedArithRow row) r
        ↔ Arith.extraction.constraint_36_every_row (probeOfRow row) r)
      ∧ (Arith.extraction.constraint_39_every_row (extractedArithRow row) r
        ↔ Arith.extraction.constraint_39_every_row (probeOfRow row) r) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## The instance is pinned to the pinned column map

`trust/scripts/check-arith-column-map.py` pins the 44 arms of `mainValue` to the
extractor's stage-1 column layout — and reads nothing but `mainValue`. Rebinding
`extractedArithRowCircuit`'s `main` field to some other function would leave that
gate green while every weld above silently spoke about a different column map:
a gate that appears to check something it does not.

`extractedArithRowCircuit_pinned` removes that freedom inside the build. It is
stated through `inferInstance`, so it fails to compile both if any field of the
instance drifts and if instance resolution for
`Extraction.Circuit FGL FGL ExtractedArithRow` starts finding a different
instance. It is deliberately the last declaration in the module: every weld above
resolves that class against the instances declared before it, so an instance
introduced anywhere above — including one shadowing `extractedArithRowCircuit` —
is also the one this theorem resolves and checks. -/
theorem extractedArithRowCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedArithRow) =
      { main := mainValue
        preprocessed := fun _ _ _ _ => 0
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

end ZiskFv.AirsClean.ArithMul
