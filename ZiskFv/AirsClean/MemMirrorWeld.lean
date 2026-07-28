import Extraction.Mem
import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.AirsClean.Mem.Bridge

/-!
# Machine-checked weld: Mem constraint mirrors ↔ generated extraction

The Mem AIR has **three** hand-written mirrors of the same generated constraint
set, and until this module their correspondence to
`build/extraction/Extraction/Mem.lean` was asserted only by comments:

* `ZiskFv/Airs/Mem.lean` — `segment_every_row` (generated `0..23`) and
  `permutation_every_row` (generated `24..33`), stated over `Valid_Mem`,
  `SegmentColumns`, `PermutationColumns`;
* `ZiskFv/AirsClean/Mem/Constraints.lean` — `segmentGeneratedConstraintAssertions`
  and `permutationGeneratedConstraintAssertions`, the same 34 as a Clean
  `assertZero` source (already tied to the previous item in both directions by
  `ZiskFv/AirsClean/Mem/Bridge.lean`);
* `ZiskFv/AirsClean/Mem/Constraints.lean` — `main`, and its mirror predicate
  `ZiskFv/AirsClean/Mem/Spec.lean` `Spec`: the nine single-row stage-1-only
  constraints, generated `{3,4,5,6,7,8,18,21,23}`. This is the mirror that flows
  into `fullRv64imEnsemble` through `componentWithDualMemBus`.

A comment is not checked by anything, so a mistyped column index or a dropped
factor in any of the three would compile and silently prove soundness of a
circuit that is not ZisK's. This module replaces the comment citations with
compiled identities covering all 34 generated constraints.

## How the weld works

`Mem.extraction.constraint_N_every_row` is stated against the abstract
`Extraction.Circuit` interface: its body only ever mentions
`Extraction.Circuit.main c (id := i) (column := k) (row := r) (rotation := 0)`,
`Extraction.Circuit.preprocessed`, `Extraction.Circuit.challenge` and
`Extraction.Circuit.exposed`. Two `Extraction.Circuit` instances are declared
below whose lanes read the mirrors' own columns, using the layout printed by the
extractor at `build/extraction/Extraction/Mem.lean:13-25`. Instantiating a
generated constraint at such a circuit turns it into a polynomial over the
mirror's fields, and the weld theorems say that polynomial is *definitionally*
the one the mirror asserts.

Unlike the Arith AIR, Mem's generated constraints are not all single-row:
`9,10,11,12,33` read trace row `row + 1` and `15,16,19,20,22,26` read
`row - 1`. `ExtractedMemTrace.mainValue` therefore threads its `row` argument
through to the `Valid_Mem` column functions rather than ignoring it.

## What the weld does and does not certify

* Coverage is the whole generated set: `constraint_0_every_row` …
  `constraint_33_every_row`, all 34, each appearing on the right of a weld
  below. Every weld is `Iff.rfl` — no `simp`, no `linear_combination`. No Mem
  mirror needed a commuted-addend exception of the kind `Arith.constraint_36`
  needed.
* `spec_weld` and `segment_weld`/`permutation_weld` are `Iff`s, so the mirrors
  assert neither less nor more than the AIR does.
* `extracted_of_componentWithDualMemBus_constraints` composes `spec_weld` with
  the already-proved `spec_of_componentWithDualMemBus_constraints`, so those
  nine generated constraints follow from the *live* `assertZero` list of the
  component that the ensemble actually contains — not from transcribed prose. A
  slip that is self-consistent across `Spec`, the `assertZero` expression in
  `main` and that projection proof is the exact failure this module exists to
  catch.
* `extracted_of_segmentConstraintAssertions` /
  `extracted_of_permutationConstraintAssertions` do the same for all 34 against
  the Clean assertion sources in `ZiskFv/AirsClean/Mem/Constraints.lean`.
* `segment_weld`/`permutation_weld` are universally quantified over *arbitrary*
  `SegmentColumns`, `PermutationColumns`, `Valid_Mem` and trace row. The
  auto-generated `Extraction.MemGeneratedConstraintBridge` already relates the
  same 34 to `segment_every_row`/`permutation_every_row`, but only at the single
  instantiation `MemOfProverData witness table`; the welds here are the
  ∀-general statement, and are `rfl` rather than `simpa only [...]`.
* The two derived surfaces in `ZiskFv/Airs/Mem.lean` — `core_every_row` (the
  nine local equations, consumed by the memory-bus proofs) and
  `segmentResidualEveryRow` (the other fifteen) — are covered transitively and
  deliberately get no weld of their own: `core_every_row_of_segment_every_row`
  and `segmentResidualEveryRow_of_segment_every_row` are positional projections
  out of `segment_every_row`, so a drift in either fails to typecheck there.
* It does **not** certify the column layout itself: the four lane maps are
  handwritten from the extractor header. A *compensating* pair of slips (mirror
  and map wrong in the same direction) would still be `rfl`. A column-map gate
  of the kind proposed for Arith on the unmerged `arith-mirror-weld` branch
  would close this; there is no Mem analogue, so this is an open hole, not a
  covered one. `extractedMemRowCircuit_pinned` and
  `extractedMemTraceCircuit_pinned` below are what such a gate would need to
  hook onto.
* It does **not** rest on the `0` answers the lane maps give outside the
  modeled lanes. That is checked by `allConstraints_readOnlyModeledLanes`, not
  assumed; see "Which lanes a welded constraint is allowed to read".

## Mutation evidence

Fourteen mutations were run against this module and reverted; the exact errors
are recorded at the declarations they break.

**A correction, because the first version of this section was wrong.** It
claimed that a self-consistent slip across two hand-written mirrors (generated
constraint 28's `(1 - is_last_segment)` -> `(1 - is_first_segment)` in both
`ZiskFv/Airs/Mem.lean` and `ZiskFv/AirsClean/Mem/Constraints.lean`) is caught by
`permutation_weld` below and by nothing else in the build. **That is false.**

Adversarial review reproduced the mutation and found
`Extraction.MemGeneratedConstraintBridge` rejects it too, at `:266` and `:515`,
with this module absent from that target's import closure. That bridge is
auto-generated, binds `Extraction.Mem.constraint_0..33` to the ProverData-backed
source, and is a **`defaultTargets` entry in `lakefile.toml`** — so it has been
gating those mirrors all along.

The wrong conclusion came from measuring with the targeted
`lake build ZiskFv.AirsClean.MemMirrorWeld` (8203 jobs), which excludes that
bridge (job 8986 of 9119 in the default build). "Not in my target's import
closure" was reported as "provably cannot see it". Any mutation conclusion drawn
from a targeted build carries the same risk; measure against the default build.

**Honest increment of this module**, given that: the `segment_weld` and
`permutation_weld` families largely duplicate the pre-existing generated bridge.
What is genuinely new is Part A — `spec_weld` and
`extracted_of_componentWithDualMemBus_constraints`, over the `Spec`/`main` mirror
that the generated bridge does not cover — plus `∀`-generality over the single
`proverData` instantiation the bridge is stated at, and the lane-restriction and
instance-pinning results.

The other thirteen mutate this module's four lane maps, its weld statements, its
`Extraction.Circuit` instances and its lane restriction; all thirteen break the
build. Most surface as `error: Type mismatch / Iff.rfl has type ?m ↔ ?m but is
expected to have type …`; two (`traceExposedValue` index 9 and
`traceChallengeValue` index 0) additionally exhaust `maxRecDepth` on the longhand
`constraint_28_weld`, and one (the challenge-lane negative control) surfaces as a
deterministic `whnf` heartbeat timeout on `allConstraints_readOnlyModeledLanes`.
Those are failure modes of the *rejected* defeq check — the unmutated module
elaborates in about 4s at default `maxRecDepth` and default heartbeats — but they
are worth knowing when a real drift is being diagnosed.

## Trust note

No axiom, `sorry`, `native_decide`, or other trust marker is added. Every
declaration is `Iff.rfl`, `rfl`, or a composition of already-proved theorems.
-/

namespace ZiskFv.AirsClean.MemMirrorWeld

open Goldilocks
open ZiskFv.AirsClean.Mem (MemRow Spec componentWithDualMemBus
  spec_of_componentWithDualMemBus_constraints SegmentConstraintAssertionWitness
  PermutationConstraintAssertionWitness segment_every_row_of_constraint_assertions
  permutation_every_row_of_constraint_assertions)
open ZiskFv.Airs.Mem (Valid_Mem SegmentColumns PermutationColumns segment_every_row
  permutation_every_row)

/-! ## Part A — the single-row mirror that reaches the ensemble

`ZiskFv/AirsClean/Mem/Constraints.lean`'s `main` emits nine `assertZero`s over a
`Var MemRow FGL`, and `ZiskFv/AirsClean/Mem/Spec.lean`'s `Spec` mirrors them as
nine conjuncts. `MemRow`'s thirteen fields are stage-1 columns `0..12` of the
extractor header, so a circuit reading field `k` at column `k` turns the nine
generated single-row constraints into exactly those polynomials. -/

/-- An `Extraction.Circuit` whose stage-1 columns are the fields of a single
    `MemRow`. Only used to instantiate the generated `Mem` constraint predicates
    at the Clean mirror's row type. -/
structure ExtractedMemRow (F ExtF : Type) where
  row : MemRow FGL

/-- Mem AIR stage-1 column layout, transcribed from the generated header
    `build/extraction/Extraction/Mem.lean:13-25` (`stage 1 col N: <name>`). The
    extractor calls columns 10 and 11 `l_increment`/`h_increment`; `MemRow`
    calls them `increment_0`/`increment_1`.

    The nine constraints welded in this section read only columns
    `2,3,5,6,7,8,12`, always at `id = 1`, `rotation = 0` and the constraint's own
    `row`; `rowAndRotation_irrelevant_forRowWelds` below records that the
    ignored `_row`/`_rotation` arguments are not what makes the welds hold.

    This map is handwritten. Nothing in the build checks it against the
    extractor header — see the module docstring. -/
@[reducible]
def rowMainValue (c : ExtractedMemRow FGL FGL) (id column _row _rotation : ℕ) : FGL :=
  if id = 1 then
    match column with
    | 0 => c.row.addr
    | 1 => c.row.step
    | 2 => c.row.sel
    | 3 => c.row.addr_changes
    | 4 => c.row.step_dual
    | 5 => c.row.sel_dual
    | 6 => c.row.value_0
    | 7 => c.row.value_1
    | 8 => c.row.wr
    | 9 => c.row.previous_step
    | 10 => c.row.increment_0
    | 11 => c.row.increment_1
    | 12 => c.row.read_same_addr
    | _ => 0
  else
    0

instance extractedMemRowCircuit : Extraction.Circuit FGL FGL ExtractedMemRow where
  main := rowMainValue
  preprocessed := fun _ _ _ _ => 0
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

@[reducible]
def extractedMemRow (row : MemRow FGL) : ExtractedMemRow FGL FGL := ⟨row⟩

/-- `mem/pil/mem.pil:125 sel_dual*(1-sel_dual)` — the plain boolean shape.

    Mirror: the first conjunct of `Spec`, the first `assertZero` of `main`.

    Mutation-tested: changing the `| 5 =>` arm of `rowMainValue` from
    `c.row.sel_dual` to `c.row.sel` makes this fail with, verbatim,
    `error: Type mismatch / Iff.rfl / has type / ?m.26 ↔ ?m.26 / but is expected
    to have type / row.sel_dual * (1 - row.sel_dual) = 0 ↔
    Mem.extraction.constraint_3_every_row (extractedMemRow row) 0`, and takes
    `spec_weld` down with it. -/
theorem constraint_3_weld (row : MemRow FGL) :
    (row.sel_dual * (1 - row.sel_dual) = 0)
      ↔ Mem.extraction.constraint_3_every_row (extractedMemRow row) 0 :=
  Iff.rfl

/-- `mem/pil/mem.pil:390 read_same_addr-((1-addr_changes)*(1-wr))` — the
    `read_same_addr` definitional identity, a three-column shape with a
    subtraction.

    Mirror: the seventh conjunct of `Spec`, the seventh `assertZero` of `main`. -/
theorem constraint_18_weld (row : MemRow FGL) :
    (row.read_same_addr - (1 - row.addr_changes) * (1 - row.wr) = 0)
      ↔ Mem.extraction.constraint_18_every_row (extractedMemRow row) 0 :=
  Iff.rfl

/-- `mem/pil/mem.pil:426 (addr_changes*(1-wr))*value[0]` — the gated
    value-clearing product. Its sibling `constraint_23` differs only in reading
    column 7 instead of column 6, which is what makes `spec_weld`'s ordering of
    the last two conjuncts load-bearing.

    Mirror: the eighth conjunct of `Spec`, the eighth `assertZero` of `main`. -/
theorem constraint_21_weld (row : MemRow FGL) :
    ((row.addr_changes * (1 - row.wr)) * row.value_0 = 0)
      ↔ Mem.extraction.constraint_21_every_row (extractedMemRow row) 0 :=
  Iff.rfl

/-- The whole of `Spec`, conjunct for conjunct and in order, is the nine
    generated single-row constraints `{3,4,5,6,7,8,18,21,23}`.

    This is an `Iff`, so `Spec` asserts neither less nor more than those nine. -/
theorem spec_weld (row : MemRow FGL) :
    Spec row ↔
      Mem.extraction.constraint_3_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_4_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_5_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_6_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_7_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_8_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_18_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_21_every_row (extractedMemRow row) 0
      ∧ Mem.extraction.constraint_23_every_row (extractedMemRow row) 0 :=
  Iff.rfl

/-! ### From the live assertion list

`spec_weld` pins the mirror *predicate*. `spec_of_componentWithDualMemBus_constraints`
(`ZiskFv/AirsClean/Mem/Circuit.lean`) already projects `Spec` out of the
`componentWithDualMemBus` operation list — the component that
`ZiskFv/AirsClean/FullEnsemble` composes into `fullRv64imEnsemble`. Composing the
two gives the generated constraints directly from the live component's own
`assertZero`s, which is what makes a drift in `main`'s expressions — not just in
`Spec` — a build failure. -/
theorem extracted_of_componentWithDualMemBus_constraints
    (env : Environment FGL)
    (h_holds : componentWithDualMemBus.operations.ConstraintsHold env) :
    Mem.extraction.constraint_3_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_4_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_5_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_6_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_7_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_8_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_18_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_21_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0
      ∧ Mem.extraction.constraint_23_every_row
        (extractedMemRow (eval env componentWithDualMemBus.rowInputVar)) 0 :=
  (spec_weld _).mp (spec_of_componentWithDualMemBus_constraints env h_holds)

/-! ## Part B — the trace-level mirrors, all 34

`ZiskFv/Airs/Mem.lean`'s `segment_every_row` and `permutation_every_row` are the
mirrors that carry the cross-row, preprocessed, exposed and challenge lanes.
Between them they claim to be the whole generated set. `ExtractedMemTrace` maps
all four lanes at once so that claim can be checked. -/

/-- An `Extraction.Circuit` over the trace-level mirror's own columns: the
    stage-1/stage-2 witness columns of a `Valid_Mem`, the preprocessed `l1`
    selectors, the two permutation challenges, and the fifteen segment publics
    plus six direct-accumulator inverses in the exposed lane. -/
structure ExtractedMemTrace (F ExtF : Type) where
  seg : SegmentColumns FGL
  perm : PermutationColumns FGL
  v : Valid_Mem FGL FGL

/-- Stage-1 columns `0..12` and stage-2 columns `0..2`, transcribed from
    `build/extraction/Extraction/Mem.lean:13-25`. The extractor prints both
    stage-2 columns 1 and 2 as `im_cluster`; the mirror names them `im_0`/`im_1`
    and `Extraction.MemGeneratedConstraintBridge.mainValue` makes the same
    choice.

    The `row` argument is threaded through, not discarded: generated `9,10,11,12`
    and `33` read `row + 1` and `15,16,19,20,22,26` read `row - 1`. -/
@[reducible]
def traceMainValue (c : ExtractedMemTrace FGL FGL) (id column row _rotation : ℕ) : FGL :=
  if id = 1 then
    match column with
    | 0 => c.v.addr row
    | 1 => c.v.step row
    | 2 => c.v.sel row
    | 3 => c.v.addr_changes row
    | 4 => c.v.step_dual row
    | 5 => c.v.sel_dual row
    | 6 => c.v.value_0 row
    | 7 => c.v.value_1 row
    | 8 => c.v.wr row
    | 9 => c.v.previous_step row
    | 10 => c.v.increment_0 row
    | 11 => c.v.increment_1 row
    | 12 => c.v.read_same_addr row
    | _ => 0
  else if id = 2 then
    match column with
    | 0 => c.v.gsum row
    | 1 => c.v.im_0 row
    | 2 => c.v.im_1 row
    | _ => 0
  else
    0

/-- The two preprocessed selector columns: the segment-boundary `l1` used by
    generated `15,19,20,22,26` and the permutation `l1` used by generated `33`. -/
@[reducible]
def tracePreprocessedValue
    (c : ExtractedMemTrace FGL FGL) (column row _rotation : ℕ) : FGL :=
  match column with
  | 0 => c.seg.segment_l1 row
  | 1 => c.perm.l1 row
  | _ => 0

/-- The two `std_` permutation challenges read by generated `24..33`. -/
@[reducible]
def traceChallengeValue (c : ExtractedMemTrace FGL FGL) (index : ℕ) : FGL :=
  match index with
  | 0 => c.perm.std_alpha
  | 1 => c.perm.std_gamma
  | _ => 0

/-- The exposed lane: `SegmentColumns`' fifteen public values at indices `0..14`
    and `PermutationColumns`' six direct-accumulator inverses at `15..20`. -/
@[reducible]
def traceExposedValue (c : ExtractedMemTrace FGL FGL) (index : ℕ) : FGL :=
  match index with
  | 0 => c.seg.segment_id
  | 1 => c.seg.is_first_segment
  | 2 => c.seg.is_last_segment
  | 3 => c.seg.previous_segment_value_0
  | 4 => c.seg.previous_segment_value_1
  | 5 => c.seg.previous_segment_step
  | 6 => c.seg.previous_segment_addr
  | 7 => c.seg.segment_last_value_0
  | 8 => c.seg.segment_last_value_1
  | 9 => c.seg.segment_last_step
  | 10 => c.seg.segment_last_addr
  | 11 => c.seg.distance_base_0
  | 12 => c.seg.distance_base_1
  | 13 => c.seg.distance_end_0
  | 14 => c.seg.distance_end_1
  | 15 => c.perm.im_direct_0
  | 16 => c.perm.im_direct_1
  | 17 => c.perm.im_direct_2
  | 18 => c.perm.im_direct_3
  | 19 => c.perm.im_direct_4
  | 20 => c.perm.im_direct_5
  | _ => 0

instance extractedMemTraceCircuit : Extraction.Circuit FGL FGL ExtractedMemTrace where
  main := traceMainValue
  preprocessed := tracePreprocessedValue
  challenge := traceChallengeValue
  exposed := traceExposedValue

@[reducible]
def extractedMemTrace (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) : ExtractedMemTrace FGL FGL := ⟨seg, perm, v⟩

/-- `mem/pil/mem.pil:103 Mem.is_first_segment*(1-Mem.is_first_segment)` — an
    exposed-lane-only constraint, welded longhand so the exposed map is readable
    as source against source.

    Mirror: the first conjunct of `segment_every_row`. -/
theorem constraint_0_weld (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    (seg.is_first_segment * (1 - seg.is_first_segment) = 0)
      ↔ Mem.extraction.constraint_0_every_row (extractedMemTrace seg perm v) r :=
  Iff.rfl

/-- `mem/pil/mem.pil:369 'l1*(addr-segment_last_addr)` — a `row + 1`
    preprocessed-gated constraint, welded longhand so the row direction is
    readable as source against source. Compare `constraint_19_weld`, which reads
    `row - 1`.

    Mirror: the twelfth conjunct of `segment_every_row`. -/
theorem constraint_11_weld (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    (seg.segment_l1 (r + 1) * (v.addr r - seg.segment_last_addr) = 0)
      ↔ Mem.extraction.constraint_11_every_row (extractedMemTrace seg perm v) r :=
  Iff.rfl

/-- `mem/pil/mem.pil:401 (1-addr_changes)*(addr-'addr)` — a `row - 1`
    constraint, where `ZiskFv.Airs.Mem.segment_previous_addr` is the mirror's
    name for the `segment_l1`-blended previous address.

    Mirror: the twentieth conjunct of `segment_every_row`. -/
theorem constraint_19_weld (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    ((1 - v.addr_changes r) *
        (v.addr r - ZiskFv.Airs.Mem.segment_previous_addr seg v r) = 0)
      ↔ Mem.extraction.constraint_19_every_row (extractedMemTrace seg perm v) r :=
  Iff.rfl

/-- `mem/pil/mem.pil:283` — a challenge-reading accumulator constraint, welded
    longhand so the challenge map is readable as source against source.
    `ZiskFv.Airs.Mem.direct_gsum_1` is the mirror's name for the
    `std_alpha`/`std_gamma` combination.

    Mirror: the fifth conjunct of `permutation_every_row`. -/
theorem constraint_28_weld (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    (perm.im_direct_1 * ZiskFv.Airs.Mem.direct_gsum_1 seg perm
        - (1 - seg.is_last_segment) = 0)
      ↔ Mem.extraction.constraint_28_every_row (extractedMemTrace seg perm v) r :=
  Iff.rfl

/-- `segment_every_row` is, conjunct for conjunct and in order, generated
    `0..23`.

    Quantified over arbitrary `SegmentColumns`, `Valid_Mem` and trace row, so
    this strictly generalizes the `MemOfProverData`-instantiated correspondence
    in the auto-generated `Extraction.MemGeneratedConstraintBridge`. -/
theorem segment_weld (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    segment_every_row seg v r ↔
      Mem.extraction.constraint_0_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_1_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_2_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_3_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_4_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_5_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_6_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_7_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_8_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_9_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_10_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_11_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_12_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_13_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_14_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_15_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_16_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_17_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_18_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_19_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_20_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_21_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_22_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_23_every_row (extractedMemTrace seg perm v) r :=
  Iff.rfl

/-- `permutation_every_row` is, conjunct for conjunct and in order, generated
    `24..33` — the challenge-reading half of the AIR.

    Under the "F-only slice" convention used for Arith these ten would be out of
    scope, because there the stage-2/challenge constraints are represented by
    channel `push`/`lookup` operations rather than `assertZero`. Mem is
    different: `ZiskFv/Airs/Mem.lean` models the challenge lane explicitly as
    `PermutationColumns.std_alpha`/`std_gamma`, so the ten are ordinary
    polynomial identities over named columns and weld like the rest. -/
theorem permutation_weld (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    permutation_every_row seg perm v r ↔
      Mem.extraction.constraint_24_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_25_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_26_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_27_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_28_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_29_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_30_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_31_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_32_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_33_every_row (extractedMemTrace seg perm v) r :=
  Iff.rfl

/-! ### From the Clean assertion sources

`ZiskFv/AirsClean/Mem/Constraints.lean` restates the same 34 as two Clean
`assertZero` circuits, and `ZiskFv/AirsClean/Mem/Bridge.lean` already projects
the `ZiskFv/Airs/Mem.lean` mirrors out of them. Composing with the welds above
ties the generated constraints to those `assertZero` expressions too, so all
three Mem mirrors are now pinned to the extraction rather than to each other. -/

theorem extracted_of_segmentConstraintAssertions
    {seg : SegmentColumns FGL} {v : Valid_Mem FGL FGL} {r : ℕ}
    (perm : PermutationColumns FGL)
    (w : SegmentConstraintAssertionWitness seg v r) :
    Mem.extraction.constraint_0_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_1_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_2_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_3_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_4_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_5_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_6_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_7_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_8_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_9_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_10_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_11_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_12_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_13_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_14_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_15_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_16_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_17_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_18_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_19_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_20_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_21_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_22_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_23_every_row (extractedMemTrace seg perm v) r :=
  (segment_weld seg perm v r).mp (segment_every_row_of_constraint_assertions w)

theorem extracted_of_permutationConstraintAssertions
    {seg : SegmentColumns FGL} {perm : PermutationColumns FGL}
    {v : Valid_Mem FGL FGL} {r : ℕ}
    (w : PermutationConstraintAssertionWitness seg perm v r) :
    Mem.extraction.constraint_24_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_25_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_26_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_27_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_28_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_29_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_30_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_31_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_32_every_row (extractedMemTrace seg perm v) r
      ∧ Mem.extraction.constraint_33_every_row (extractedMemTrace seg perm v) r :=
  (permutation_weld seg perm v r).mp (permutation_every_row_of_constraint_assertions w)

/-! ## Which lanes a welded constraint is allowed to read

The four lane maps are total, so they have to answer somewhere they are not
modeling: `traceMainValue` returns `0` for every `id ∉ {1,2}` and every column
past the layout, the other three return `0` past their last index, and all four
ignore `rotation`. `extractedMemRowCircuit` goes further and stubs
`preprocessed`, `challenge` and `exposed` to `0` outright, and ignores the
constraint's `row`. Those answers are only harmless if no welded constraint can
observe them; if one could, the weld would be certifying a polynomial the AIR
does not assert. This section checks that instead of asserting it.

`MemProbe` is the *free* `Extraction.Circuit`: every lane is an unconstrained
function field. Instantiating a generated constraint there turns each cell read
into an application of a variable, so a `rfl`-level identity between a probe
circuit and its restriction is a statement about which cells the generated body
mentions — not about their values. -/

/-- The free `Extraction.Circuit` over `FGL`: each lane is a function field. -/
structure MemProbe (F ExtF : Type) where
  mainCell : ℕ → ℕ → ℕ → ℕ → FGL
  preprocessedCell : ℕ → ℕ → ℕ → FGL
  challengeCell : ℕ → FGL
  exposedCell : ℕ → FGL

instance memProbeCircuit : Extraction.Circuit FGL FGL MemProbe where
  main c := c.mainCell
  preprocessed c := c.preprocessedCell
  challenge c := c.challengeCell
  exposed c := c.exposedCell

/-- `c` cut down to the lanes `extractedMemTraceCircuit` actually models: stage 1
    columns `< 13`, stage 2 columns `< 3`, rotation `0`, preprocessed columns
    `< 2`, challenge indices `< 2`, exposed indices `< 21`; `0` everywhere else.

    Note what is *not* restricted: the trace row. `traceMainValue` threads it
    through, and generated `9,10,11,12,15,16,19,20,22,26,33` genuinely read
    rows other than the constraint's own. -/
@[reducible]
def restrictToModeledLanes (c : MemProbe FGL FGL) : MemProbe FGL FGL where
  mainCell := fun id column row rotation =>
    if ((id = 1 ∧ column < 13) ∨ (id = 2 ∧ column < 3)) ∧ rotation = 0 then
      c.mainCell id column row rotation
    else 0
  preprocessedCell := fun column row rotation =>
    if column < 2 ∧ rotation = 0 then c.preprocessedCell column row rotation else 0
  challengeCell := fun index => if index < 2 then c.challengeCell index else 0
  exposedCell := fun index => if index < 21 then c.exposedCell index else 0

/-- `P c r` is unchanged by zeroing every lane the trace column map does not
    model.

    Unfolded: `P c r` may mention `c.mainCell 1 k _ 0` for `k < 13`,
    `c.mainCell 2 k _ 0` for `k < 3`, `c.preprocessedCell k _ 0` for `k < 2`,
    `c.challengeCell k` for `k < 2` and `c.exposedCell k` for `k < 21`, and
    nothing else. A read outside those ranges, or at a nonzero rotation, would
    leave a free `c.<lane> …` on the left of the `Iff` with no counterpart on the
    right, and `Iff.rfl` would not typecheck. -/
@[reducible]
def ReadsOnlyModeledLanes (P : MemProbe FGL FGL → ℕ → Prop) : Prop :=
  ∀ (c : MemProbe FGL FGL) (r : ℕ), P c r ↔ P (restrictToModeledLanes c) r

/-- All 34 generated Mem constraints read only the lanes the trace column map
    models.

    The property is not vacuous. Each of these four weakenings of
    `restrictToModeledLanes` was applied and reverted, and each makes this
    theorem fail to elaborate — reported error verbatim:

    * `exposedCell` cut at `< 20` instead of `< 21`:
      `Iff.rfl … expected to have type constraint_33_every_row x✝¹ x✝ ↔
      constraint_33_every_row (restrictToModeledLanes x✝¹) x✝` (index 20 is
      `im_direct_5`);
    * `preprocessedCell` cut at `< 1` instead of `< 2`: the same error on
      `constraint_33_every_row`, which reads the permutation `l1`;
    * `mainCell`'s stage-1 branch cut at `< 12` instead of `< 13`: the same
      error on `constraint_22_every_row`, a `read_same_addr` reader;
    * `challengeCell` cut at `< 1` instead of `< 2`:
      `(deterministic) timeout at whnf, maximum number of heartbeats (200000)
      has been reached` on this declaration — a rejected defeq check that is too
      deep to report cleanly rather than an accepted one.

    So each of the four bounds is doing work, and the `0` defaults outside them
    are not what makes any weld above hold. -/
theorem allConstraints_readOnlyModeledLanes :
    ReadsOnlyModeledLanes Mem.extraction.constraint_0_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_1_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_2_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_3_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_4_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_5_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_6_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_7_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_8_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_9_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_10_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_11_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_12_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_13_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_14_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_15_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_16_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_17_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_18_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_19_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_20_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_21_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_22_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_23_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_24_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_25_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_26_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_27_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_28_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_29_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_30_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_31_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_32_every_row
    ∧ ReadsOnlyModeledLanes Mem.extraction.constraint_33_every_row :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
   fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- `extractedMemTrace seg perm v` re-expressed in the free circuit. Composed
    with `allConstraints_readOnlyModeledLanes` this says: the `0` defaults of the
    four trace lane maps cannot be what makes `segment_weld` or
    `permutation_weld` hold, because no generated constraint can observe them. -/
@[reducible]
def probeOfTrace (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) : MemProbe FGL FGL where
  mainCell := traceMainValue (extractedMemTrace seg perm v)
  preprocessedCell := tracePreprocessedValue (extractedMemTrace seg perm v)
  challengeCell := traceChallengeValue (extractedMemTrace seg perm v)
  exposedCell := traceExposedValue (extractedMemTrace seg perm v)

theorem traceWelds_probeBridge (seg : SegmentColumns FGL) (perm : PermutationColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    (Mem.extraction.constraint_0_every_row (extractedMemTrace seg perm v) r
        ↔ Mem.extraction.constraint_0_every_row (probeOfTrace seg perm v) r)
      ∧ (Mem.extraction.constraint_11_every_row (extractedMemTrace seg perm v) r
        ↔ Mem.extraction.constraint_11_every_row (probeOfTrace seg perm v) r)
      ∧ (Mem.extraction.constraint_19_every_row (extractedMemTrace seg perm v) r
        ↔ Mem.extraction.constraint_19_every_row (probeOfTrace seg perm v) r)
      ∧ (Mem.extraction.constraint_28_every_row (extractedMemTrace seg perm v) r
        ↔ Mem.extraction.constraint_28_every_row (probeOfTrace seg perm v) r)
      ∧ (Mem.extraction.constraint_33_every_row (extractedMemTrace seg perm v) r
        ↔ Mem.extraction.constraint_33_every_row (probeOfTrace seg perm v) r) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- `extractedMemRow row` re-expressed in the free circuit: `rowMainValue` in the
    stage-1 lane, `0` in every stub lane. -/
@[reducible]
def probeOfRow (row : MemRow FGL) : MemProbe FGL FGL where
  mainCell := rowMainValue (extractedMemRow row)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- The bridge from `extractedMemRowCircuit`, at which Part A's welds are stated,
    into the free circuit. Composed with `allConstraints_readOnlyModeledLanes` it
    gives: none of the nine single-row constraints can observe a stubbed lane, so
    the `preprocessed`/`challenge`/`exposed` stubs and the discarded
    `row`/`rotation` arguments cannot be what makes a Part A weld true. -/
theorem rowWelds_probeBridge (row : MemRow FGL) (r : ℕ) :
    (Mem.extraction.constraint_3_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_3_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_4_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_4_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_5_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_5_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_6_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_6_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_7_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_7_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_8_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_8_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_18_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_18_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_21_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_21_every_row (probeOfRow row) r)
      ∧ (Mem.extraction.constraint_23_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_23_every_row (probeOfRow row) r) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- The nine single-row constraints do not depend on `rowMainValue`'s discarded
    `_row`/`_rotation` arguments: they hold at one trace row iff they hold at
    every other. This is what licenses stating Part A's welds at `row := 0`.

    It is specific to these nine. The same statement for `constraint_11` at the
    trace circuit — which reads `row + 1` — was tried and rejected:
    `Iff.rfl … but is expected to have type
    Mem.extraction.constraint_11_every_row (extractedMemTrace seg perm v) r ↔
    Mem.extraction.constraint_11_every_row (extractedMemTrace seg perm v) r'`.
    Part B is stated at a universally quantified `r` for exactly that reason. -/
theorem rowWelds_rowIrrelevant (row : MemRow FGL) (r r' : ℕ) :
    (Mem.extraction.constraint_3_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_3_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_4_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_4_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_5_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_5_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_6_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_6_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_7_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_7_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_8_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_8_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_18_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_18_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_21_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_21_every_row (extractedMemRow row) r')
      ∧ (Mem.extraction.constraint_23_every_row (extractedMemRow row) r
        ↔ Mem.extraction.constraint_23_every_row (extractedMemRow row) r') :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## The instances are pinned to the pinned column maps

Every weld above resolves `Extraction.Circuit.main`/`preprocessed`/`challenge`/
`exposed` *through* an instance, so rebinding a field to a function that is not
definitionally the intended map already breaks every weld that reads that lane —
that much is checked by the welds themselves. Two residual freedoms are not:

* a second `Extraction.Circuit FGL FGL ExtractedMemRow` (or `…MemTrace`)
  instance shadowing the one declared here, so that the welds silently resolve
  against a different map;
* a future column-map gate (the Mem analogue of
  `trust/scripts/check-arith-column-map.py`) reading the *text* of
  `rowMainValue`/`traceMainValue` while the instance binds something else —
  the hazard review of eth-act/zisk-fv#300 found in the Arith weld.

The two theorems below remove both inside the build. Each is stated through
`inferInstance`, so it fails to compile if any field of the instance drifts *and*
if instance resolution starts finding a different instance. They are deliberately
the last declarations in the module: every weld above resolves the class against
the instances declared before them, so an instance introduced anywhere above —
including one shadowing these — is also the one these theorems resolve and check.

Both halves were mutation-tested and reverted.

* Rebinding `extractedMemRowCircuit`'s `main` to `fun _ _ _ _ _ => 0` breaks
  seven declarations, `extractedMemRowCircuit_pinned` among them — so a rebind
  to a function that is not definitionally `rowMainValue` is caught by the welds
  themselves, not only here.
* Declaring a second `Extraction.Circuit FGL FGL ExtractedMemRow` instance
  immediately before these theorems — after every weld — leaves **every weld
  above green** and is caught here alone:
  `error: Not a definitional equality: the left-hand side / inferInstance / is
  not definitionally equal to the right-hand side / { main := rowMainValue,
  preprocessed := fun x x_1 x_2 x_3 => 0, challenge := fun x x_1 => 0,
  exposed := fun x x_1 => 0 }`. That is the residual freedom these two
  declarations exist for, and it is not redundant with anything above.
-/

theorem extractedMemRowCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedMemRow) =
      { main := rowMainValue
        preprocessed := fun _ _ _ _ => 0
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

theorem extractedMemTraceCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL ExtractedMemTrace) =
      { main := traceMainValue
        preprocessed := tracePreprocessedValue
        challenge := traceChallengeValue
        exposed := traceExposedValue } :=
  rfl

end ZiskFv.AirsClean.MemMirrorWeld
