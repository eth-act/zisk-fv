import Extraction.Arith
import ZiskFv.AirsClean.ArithCompleteConstraints

/-!
# Machine-checked weld: Arith constraint mirror ↔ generated extraction

`ZiskFv/AirsClean/ArithCompleteConstraints.lean` asserts a handwritten mirror of
the Arith AIR's local constraints and cites the generated
`Extraction.Arith.constraint_N_every_row` definitions in comments only. Comments
are not checked by anything, so a transcription slip in the mirror would be
invisible to the build.

This module replaces the comment citation with a `rfl`-level identity for a
representative slice of the constraint set (eth-act/zisk-fv#296): the plain
boolean `constraint_39`, the `m32`-weighted boundary pin `constraint_15`, the
nonzero-divisor detector `constraint_25`, and the one member of the F-only
constraint set that is *not* a verbatim transcription, `constraint_36`.

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
  polynomials — same columns, same coefficients, same shape. Combined with the
  already-proved `sharedDivBlockSpec_of_soundness`,
  `extracted_of_sharedMainComplete` below derives the generated constraints from
  the live `sharedMainComplete` assertion list, so a drift in either the `Spec`
  predicate or the `assertZero` expression breaks the build.
* It covers three of the Arith AIR's 49 F-only constraints (plus `constraint_36`),
  not all of them. Nothing here forces the mirror to be *complete* with respect to
  the AIR, nor forbids an assertion the AIR does not make; those are separate
  obligations.
* It does **not** certify the column layout itself: `mainValue` is handwritten.
  That map is pinned separately by `trust/scripts/check-arith-column-map.py`,
  against the extractor's own column-name header as recorded in
  `trust/generated/arith-stage1-columns.txt`. Without that gate a *compensating*
  pair of slips (mirror and map wrong in the same direction) would still be `rfl`.

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
generated polynomial are the same term after unfolding the column map.
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

/-! ### From the live assertion list

`sharedDivBlockSpec_of_soundness` (`ZiskFv/AirsClean/ArithCompleteConstraints.lean`)
already projects `SharedDivBlockSpec` out of the `sharedMainComplete` operation
list. Composing it with the welds above gives the generated constraints directly
from the mirror circuit's own assertions, which is what makes a drift in the
`assertZero` expressions — not just in the `Spec` — a build failure. -/

theorem extracted_of_sharedMainComplete
    (offset : ℕ) (env : Environment FGL) (row : Var ArithMulRow FGL)
    (h : ConstraintsHold.Soundness env ((sharedMainComplete row).operations offset)) :
    Arith.extraction.constraint_15_every_row (extractedArithRow (eval env row)) 0
      ∧ Arith.extraction.constraint_25_every_row (extractedArithRow (eval env row)) 0
      ∧ Arith.extraction.constraint_39_every_row (extractedArithRow (eval env row)) 0 := by
  have hspec := sharedDivBlockSpec_of_soundness offset env row h
  exact ⟨divBoundarySpec_a2_weld _ hspec.2.1,
    divInverseSumSpec_weld _ |>.mp hspec.2.2.1,
    divModeSpec_div_boolean_weld _ hspec.1⟩

end ZiskFv.AirsClean.ArithMul
