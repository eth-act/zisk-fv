import Extraction.MemAlign
import ZiskFv.Airs.MemAlign
import ZiskFv.AirsClean.MemAlign.Circuit

/-!
# Machine-checked weld: MemAlign constraint mirrors ↔ generated extraction

ZisK's `MemAlign` AIR has two handwritten mirrors in this repository, and until
this module neither was tied to the extractor's output by anything a compiler
checks:

* `ZiskFv/Airs/MemAlign.lean` — `Valid_MemAlign`, 25 named `every_row`
  constraint definitions bundled by `core_every_row`, citing the generated
  `constraint_N_every_row` numbers in a docstring;
* `ZiskFv/AirsClean/MemAlign/` — the Clean component, whose F-only surface is
  split into the per-row `Spec` (16 clauses), `transitionRows` (9) and
  `cyclicSuccessorTransitionRows` (9 clauses, 8 of which have a generated F-only
  counterpart; see that weld for the ninth), citing the same numbers in comments.

A comment is not checked by anything, so a mistyped coefficient or a swapped
column in either mirror would compile and would silently prove soundness of a
circuit that is not ZisK's.  This module replaces those citations with compiled
`Iff`s.

## Coverage: 33 of the AIR's 40 generated constraints

`build/extraction/Extraction/MemAlign.lean` defines
`constraint_0_every_row` … `constraint_39_every_row`.  Exactly 33 of them —
`constraint_0` … `constraint_32` — are F-only: they read only
`Extraction.Circuit.main c (id := 1)` and, in the single case of
`constraint_16`, `Extraction.Circuit.preprocessed c (column := 0)`.  Every one
of those 33 appears on the right of a weld below.

The other seven, `constraint_33` … `constraint_39`, read the stage-2 columns
(`main (id := 2)`) and `Extraction.Circuit.challenge`; `constraint_38` and
`constraint_39` additionally read `preprocessed (column := 1)` and
`Extraction.Circuit.exposed`.  They are the `std_sum` global-sum bookkeeping and
are represented in the Clean component by channel emissions, not by `assertZero`.
Nothing here welds them, and no weld below is stated at a circuit that could
model them: the bridges answer `0` on the challenge and exposed lanes, and
`memAlignConstraints_readOnlyModeledLanes` proves — rather than assumes — that
no welded constraint can observe those answers.

## The two bridges

`MemAlign.extraction.constraint_N_every_row` is stated against the abstract
`Extraction.Circuit` interface.  A bridge is an instance of that class whose
stage-1 column `k` is field `k` of a mirror row, using the layout printed by the
extractor at `build/extraction/Extraction/MemAlign.lean:14-42`.  Instantiating a
generated constraint at a bridge turns it into a polynomial over mirror fields,
and each weld says that polynomial is *definitionally* the mirror's.

Both bridges share one column map, `stage1Column`, so there is a single
handwritten datum to audit rather than two that can drift apart.

* `MemAlignColumnTrace` wraps a `Valid_MemAlign`, whose accessors are already
  `ℕ → F`.  Its welds hold at a **general** `row : ℕ`, so they pin the
  row-indexing (`row`, `row - 1`) as well as the polynomial.
* `MemAlignRowWindow` holds three adjacent `MemAlignRow`s and is read at
  generated row index `1`, where `row - 1 = 0` and `row + 1 = 2`.  A three-row
  window is what the Clean component's cross-row predicates need, since
  `constraint_0`…`constraint_15` reach both backwards and forwards.

## Binding: what a rebinding can and cannot get past this module

The welds resolve `Extraction.Circuit.main`/`preprocessed` through the bridge
instances, so rebinding an instance field breaks them.  A column-map gate,
however, would read only `stage1Column`; rebinding
`memAlignColumnTraceCircuit.main` to some *other* map would leave such a gate
green while the welds spoke about a different circuit.
`memAlignColumnTraceCircuit_pinned` and `memAlignRowWindowCircuit_pinned`, the
last two declarations in this module, remove that freedom inside the build: they
are stated through `inferInstance`, so they fail both if a field drifts and if
class resolution starts finding a different instance.

On the mirror side the same question is: is the weld tied to the predicate the
component actually *uses*?  For the Clean component it is.
`component_spec_weld`, `component_transition_weld` and
`component_cyclicSuccessorTransition_weld` are stated at
`MemAlign.component.Spec`, `.transition` and `.cyclicSuccessorTransition` —
the `Air.Flat.Component` fields themselves, not at a same-named definition — so
rebinding `component.transition := somethingElse` is a build failure.
`extracted_of_mainSoundness` reaches the 16 generated per-row constraints from
`main`'s own `assertZero` list rather than from `Spec`; see the note there for
what that composition does and does not add over
`MemAlign.circuit.soundness`.

## What this module does NOT certify

1. **`stage1Column` itself.**  The column map is handwritten from the generated
   header.  A *compensating* pair of slips (map and mirror wrong in the same
   direction) would still be `rfl`.  Pinning the map against the extractor's own
   column-name header is a gate's job, not a weld's; this module keeps the map
   in one named definition so that gate has a single target.
2. **`constraint_16`'s lane class.**  The AIR declares `L1` as a *fixed* column
   (`zisk/state-machines/mem/pil/mem_align.pil:120`, `col fixed L1 = [1,0...]`),
   and the extractor emits the read as
   `Extraction.Circuit.preprocessed c (column := 0)`.  Both mirrors model it as
   an ordinary witness field, `Valid_MemAlign.preL1` / `MemAlignRow.preL1`, and
   the bridges close the gap by mapping `preprocessed (column := 0)` to that
   field.  The polynomial matches; the *provenance* does not.  A prover that
   controls `preL1` can set it to `0` on the boot row and evade `pc = 0`, which
   a fixed column would not permit.  This is pre-existing mirror behaviour, not
   introduced here, but `boot_pc_zero_weld` and `component_spec_weld` must not
   be read as certifying that `constraint_16` is faithfully modelled.
3. **The skippable-`sel_prove` defect's multiplicity.**
   `ZISK-DEFECT-MEMALIGN-SKIPPABLE-PROVE` (`trust/defects.md`) lives in the
   memory-bus selector `sel_prove - (sel_up_to_down + sel_down_to_up)`
   (`ZiskFv/AirsClean/MemAlign/Constraints.lean`).  Its generated home is
   `constraint_37`, a challenge-lane constraint, so no weld here can pin it.
4. **Anything about `MemAlignRow.delta_pc` beyond one visible conjunct.**  See
   the note on `cyclicSuccessorTransitionRows_weld`.

## Relation to the narrow-load defect

`ZISK-DEFECT-MEMALIGN-NARROW-LOAD-LANE-SOUNDNESS` (`trust/defects.md`) is an
*absence*: the local constraint surface reconstructs both value lanes and
contains no selected-narrow-width zero-padding condition.  `component_spec_weld`
is an `Iff`, so it machine-checks that the mirror asserts neither less nor more
than the AIR on that surface.  That is positive evidence for the defect, and it
means a future "fix" that adds a zero-padding conjunct to `Spec` without a
corresponding change in the AIR would break this module rather than pass
silently.

## Trust note

No axiom, `opaque`, `sorry`, `native_decide` or other trust marker is added.
Every weld is `Iff.rfl`; `extracted_of_mainSoundness` composes an `Iff.rfl` weld
with a structural projection out of the `assertZero` list.
-/

namespace ZiskFv.AirsClean.MemAlignMirrorWeld

open Goldilocks
open ZiskFv.AirsClean.MemAlign

/-! ## The MemAlign column layout

The one handwritten datum this module introduces, transcribed from the generated
header `build/extraction/Extraction/MemAlign.lean:14-42`
(`stage 1 col N: <name>`), with `reg[i]`/`sel[i]`/`value[i]` spelled
`reg_i`/`sel_i`/`value_i` as both mirrors spell them.

Stage 2 (`gsum`, `im_cluster`, `im_single`) is deliberately absent: the
generated constraints that read it (`constraint_33`…`constraint_39`) also mix in
`Extraction.Circuit.challenge` and correspond to channel emissions in the Clean
component, not to `assertZero`. -/
@[reducible]
def stage1Column (row : MemAlignRow FGL) : ℕ → FGL
  | 0 => row.addr
  | 1 => row.offset
  | 2 => row.width
  | 3 => row.wr
  | 4 => row.pc
  | 5 => row.reset
  | 6 => row.sel_up_to_down
  | 7 => row.sel_down_to_up
  | 8 => row.reg_0
  | 9 => row.reg_1
  | 10 => row.reg_2
  | 11 => row.reg_3
  | 12 => row.reg_4
  | 13 => row.reg_5
  | 14 => row.reg_6
  | 15 => row.reg_7
  | 16 => row.sel_0
  | 17 => row.sel_1
  | 18 => row.sel_2
  | 19 => row.sel_3
  | 20 => row.sel_4
  | 21 => row.sel_5
  | 22 => row.sel_6
  | 23 => row.sel_7
  | 24 => row.step
  | 25 => row.delta_addr
  | 26 => row.sel_prove
  | 27 => row.value_0
  | 28 => row.value_1
  | _ => 0

/-- The AIR's preprocessed lane, as far as the F-only constraint set reaches it.
    `constraint_16` reads `preprocessed (column := 0)`, the fixed column
    `MemAlign.L1`; `constraint_38`/`constraint_39` read
    `preprocessed (column := 1)` (`__L1__`) but are challenge-lane constraints
    and are not welded, so column `1` stays unmodeled and answers `0`.

    Mapping column `0` to the witness field `preL1` is the lane-class gap
    recorded as point 2 of the module header. -/
@[reducible]
def preprocessedColumn (row : MemAlignRow FGL) : ℕ → FGL
  | 0 => row.preL1
  | _ => 0

/-! ## Bridge A — the `Valid_MemAlign` column mirror

`Valid_MemAlign`'s accessors are already `ℕ → F`, so this bridge needs no
row window: the welds below hold at a general `row : ℕ` and therefore pin the
generated row indexing (`row` versus `row - 1`) as well as the polynomials.

`Valid_MemAlign` carries its own `[Field]` binders, so it cannot be the class's
carrier directly; `MemAlignColumnTrace`'s two type parameters are phantom. -/

/-- An `Extraction.Circuit` whose stage-1 columns are the accessors of a
    `Valid_MemAlign`. -/
structure MemAlignColumnTrace (F ExtF : Type) where
  columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL

/-- The `Valid_MemAlign` accessors read at one trace row, as a `MemAlignRow`, so
    that both bridges can share the single column map `stage1Column`.

    `delta_pc` is not a column of the AIR (it is a PIL `expr`,
    `mem_align.pil:139`) and `Valid_MemAlign` has no accessor for it, so it is
    filled with `0`.  Nothing reads it: `stage1Column` never returns it, and
    `memAlignConstraints_readOnlyModeledLanes` bounds every welded constraint to
    stage-1 columns `< 29`. -/
@[reducible]
def columnTraceRowAt (c : MemAlignColumnTrace FGL FGL) (row : ℕ) : MemAlignRow FGL where
  addr := c.columns.addr row
  offset := c.columns.offset row
  width := c.columns.width row
  wr := c.columns.wr row
  pc := c.columns.pc row
  reset := c.columns.reset row
  sel_up_to_down := c.columns.sel_up_to_down row
  sel_down_to_up := c.columns.sel_down_to_up row
  reg_0 := c.columns.reg_0 row
  reg_1 := c.columns.reg_1 row
  reg_2 := c.columns.reg_2 row
  reg_3 := c.columns.reg_3 row
  reg_4 := c.columns.reg_4 row
  reg_5 := c.columns.reg_5 row
  reg_6 := c.columns.reg_6 row
  reg_7 := c.columns.reg_7 row
  sel_0 := c.columns.sel_0 row
  sel_1 := c.columns.sel_1 row
  sel_2 := c.columns.sel_2 row
  sel_3 := c.columns.sel_3 row
  sel_4 := c.columns.sel_4 row
  sel_5 := c.columns.sel_5 row
  sel_6 := c.columns.sel_6 row
  sel_7 := c.columns.sel_7 row
  step := c.columns.step row
  delta_addr := c.columns.delta_addr row
  sel_prove := c.columns.sel_prove row
  value_0 := c.columns.value_0 row
  value_1 := c.columns.value_1 row
  preL1 := c.columns.preL1 row
  delta_pc := 0

@[reducible]
def columnTraceMain (c : MemAlignColumnTrace FGL FGL) (id column row _rotation : ℕ) : FGL :=
  if id = 1 then stage1Column (columnTraceRowAt c row) column else 0

@[reducible]
def columnTracePreprocessed (c : MemAlignColumnTrace FGL FGL) (column row _rotation : ℕ) : FGL :=
  preprocessedColumn (columnTraceRowAt c row) column

instance memAlignColumnTraceCircuit : Extraction.Circuit FGL FGL MemAlignColumnTrace where
  main := columnTraceMain
  preprocessed := columnTracePreprocessed
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

@[reducible]
def extractedColumns (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) :
    MemAlignColumnTrace FGL FGL := ⟨columns⟩

/-! ### The 25 `Valid_MemAlign` constraint definitions, welded

Each theorem is `Iff.rfl`: the mirror's polynomial and the generated polynomial
are the same term after unfolding the column map.  `Valid_MemAlign` models 25 of
the AIR's 33 F-only constraints; the eight it skips are the *forward*-rotated
register-continuity constraints `constraint_0`, `constraint_2`, …,
`constraint_14`, which its own docstring records as out of scope.  Those eight
are welded through Bridge B below, so between the two bridges the F-only set is
covered exactly once. -/

/-- `mem_align.pil:117` — `reg[0]` continuity into a down-to-up row. -/
theorem down_to_up_continuity_0_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_0 columns row
      ↔ MemAlign.extraction.constraint_1_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_1_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_1 columns row
      ↔ MemAlign.extraction.constraint_3_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_2_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_2 columns row
      ↔ MemAlign.extraction.constraint_5_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_3_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_3 columns row
      ↔ MemAlign.extraction.constraint_7_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_4_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_4 columns row
      ↔ MemAlign.extraction.constraint_9_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_5_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_5 columns row
      ↔ MemAlign.extraction.constraint_11_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_6_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_6 columns row
      ↔ MemAlign.extraction.constraint_13_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem down_to_up_continuity_7_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.down_to_up_continuity_7 columns row
      ↔ MemAlign.extraction.constraint_15_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:121` — `MemAlign.L1 * pc`.  See the `L1` note in the module header: `preL1` is a WITNESS field standing for a FIXED column. -/
theorem boot_pc_zero_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boot_pc_zero columns row
      ↔ MemAlign.extraction.constraint_16_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:125` — the eight `sel[i]` boolean pins. -/
theorem boolean_sel_0_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_0 columns row
      ↔ MemAlign.extraction.constraint_17_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_1_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_1 columns row
      ↔ MemAlign.extraction.constraint_18_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_2_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_2 columns row
      ↔ MemAlign.extraction.constraint_19_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_3_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_3 columns row
      ↔ MemAlign.extraction.constraint_20_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_4_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_4 columns row
      ↔ MemAlign.extraction.constraint_21_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_5_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_5 columns row
      ↔ MemAlign.extraction.constraint_22_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_6_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_6 columns row
      ↔ MemAlign.extraction.constraint_23_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_7_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_7 columns row
      ↔ MemAlign.extraction.constraint_24_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:127-130` — the four mode boolean pins. -/
theorem boolean_wr_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_wr columns row
      ↔ MemAlign.extraction.constraint_25_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_reset_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_reset columns row
      ↔ MemAlign.extraction.constraint_26_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_up_to_down_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_up_to_down columns row
      ↔ MemAlign.extraction.constraint_27_every_row (extractedColumns columns) row :=
  Iff.rfl

theorem boolean_sel_down_to_up_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.boolean_sel_down_to_up columns row
      ↔ MemAlign.extraction.constraint_28_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:142` — the reset-gated backward difference of `addr`. -/
theorem delta_addr_definition_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.delta_addr_definition columns row
      ↔ MemAlign.extraction.constraint_29_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:165` — `sel_prove` excludes `sel_assume`. -/
theorem sel_prove_disjoint_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.sel_prove_disjoint columns row
      ↔ MemAlign.extraction.constraint_30_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:187` — the low-lane 8-way byte-rotation multiplexer. -/
theorem value_0_reconstruction_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.value_0_reconstruction columns row
      ↔ MemAlign.extraction.constraint_31_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- `mem_align.pil:187` — the high-lane dual of `value_0`. -/
theorem value_1_reconstruction_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.value_1_reconstruction columns row
      ↔ MemAlign.extraction.constraint_32_every_row (extractedColumns columns) row :=
  Iff.rfl

/-- The whole `Valid_MemAlign` bundle at once.  Stronger than the conjunction of
    the 25 welds above in one respect: it also pins the bundle's membership and
    ordering, so dropping a conjunct from `core_every_row` — the shape that
    would silently weaken every consumer of the validator — fails here. -/
theorem core_every_row_weld (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) (row : ℕ) :
    ZiskFv.Airs.MemAlign.core_every_row columns row ↔
      MemAlign.extraction.constraint_1_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_3_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_5_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_7_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_9_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_11_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_13_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_15_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_16_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_17_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_18_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_19_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_20_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_21_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_22_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_23_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_24_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_25_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_26_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_27_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_28_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_29_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_30_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_31_every_row (extractedColumns columns) row
      ∧ MemAlign.extraction.constraint_32_every_row (extractedColumns columns) row
      :=
  Iff.rfl

/-! ## Bridge B — the Clean component's three-row window

`constraint_0`, `constraint_2`, …, `constraint_14` read `row + 1` and
`constraint_1`, `constraint_3`, …, `constraint_15`, `constraint_29` read
`row - 1`, so the component's cross-row predicates need a window.  Every weld
below is read at generated row index `1`, where `row - 1` reduces to `0` and
`row + 1` to `2`. -/

/-- Three adjacent `MemAlignRow`s as an `Extraction.Circuit`. -/
structure MemAlignRowWindow (F ExtF : Type) where
  previous : MemAlignRow FGL
  current : MemAlignRow FGL
  successor : MemAlignRow FGL

/-- Generated row index ↦ window slot.  Only `0`, `1`, `2` occur in the welded
    set (each weld is read at row `1`); indices `≥ 3` alias to `successor`, and
    `memAlignConstraints_readOnlyWindowRows` proves no welded constraint reaches
    them. -/
@[reducible]
def windowRowAt (c : MemAlignRowWindow FGL FGL) (row : ℕ) : MemAlignRow FGL :=
  match row with
  | 0 => c.previous
  | 1 => c.current
  | _ => c.successor

@[reducible]
def windowMain (c : MemAlignRowWindow FGL FGL) (id column row _rotation : ℕ) : FGL :=
  if id = 1 then stage1Column (windowRowAt c row) column else 0

@[reducible]
def windowPreprocessed (c : MemAlignRowWindow FGL FGL) (column row _rotation : ℕ) : FGL :=
  preprocessedColumn (windowRowAt c row) column

instance memAlignRowWindowCircuit : Extraction.Circuit FGL FGL MemAlignRowWindow where
  main := windowMain
  preprocessed := windowPreprocessed
  challenge := fun _ _ => 0
  exposed := fun _ _ => 0

@[reducible]
def windowOf (previous current successor : MemAlignRow FGL) : MemAlignRowWindow FGL FGL :=
  ⟨previous, current, successor⟩

/-! ### The component's three F-only predicates, welded

`Spec` (16 clauses), `transitionRows` (9) and `cyclicSuccessorTransitionRows`
(9) partition the AIR's 33 F-only constraints as 16 + 9 + 8, the ninth clause of
`cyclicSuccessorTransitionRows` being the `delta_pc` relation discussed there.
Each weld is an `Iff`, so the mirror asserts neither less nor more than the
generated set — conjunct for conjunct and in order. -/

/-- `mem_align.pil:121,125,127-130,165,187` — the component's per-row surface. -/
theorem spec_weld (previous current successor : MemAlignRow FGL) :
    Spec current ↔
      MemAlign.extraction.constraint_25_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_26_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_27_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_28_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_17_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_18_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_19_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_20_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_21_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_22_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_23_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_24_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_16_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_30_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_31_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_32_every_row (windowOf previous current successor) 1
      :=
  Iff.rfl

/-- `mem_align.pil:117,142` — the predecessor/current surface. -/
theorem transitionRows_weld (previous current successor : MemAlignRow FGL) :
    transitionRows previous current ↔
      MemAlign.extraction.constraint_29_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_1_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_3_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_5_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_7_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_9_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_11_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_13_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_15_every_row (windowOf previous current successor) 1
      :=
  Iff.rfl

/-- `mem_align.pil:116,141` — the current/successor surface.

    The first conjunct is stated in the open, not hidden behind the generated
    numbers, because it has **no F-only generated counterpart**.  The PIL does
    say `delta_pc = pc' - pc` (`mem_align.pil:141`), but `delta_pc` is a PIL
    `expr`, not a column, so the extractor inlines that difference into
    `constraint_36` — a challenge-lane constraint, outside the welded set.
    Relative to the F-only slice the conjunct is therefore a mirror
    strengthening; `cyclicSuccessorTransitionRows_memAlignIdleRow`
    (`ZiskFv/AirsClean/MemAlign/Circuit.lean`) supplies its constructibility.
    Stating this weld as an implication instead would let a future
    over-assertion in `cyclicSuccessorTransitionRows` slip through; stating it
    without the conjunct would hide the strengthening. -/
theorem cyclicSuccessorTransitionRows_weld (previous current successor : MemAlignRow FGL) :
    cyclicSuccessorTransitionRows current successor ↔
      (current.delta_pc = successor.pc - current.pc)
      ∧ MemAlign.extraction.constraint_0_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_2_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_4_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_6_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_8_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_10_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_12_every_row (windowOf previous current successor) 1
      ∧ MemAlign.extraction.constraint_14_every_row (windowOf previous current successor) 1
      :=
  Iff.rfl

/-! ### Tied to the `Air.Flat.Component` fields

The three welds above name the mirror predicates.  These restate them at
`MemAlign.component`'s own fields, so a rebinding — `transition := fun _ _ _ =>
True`, say — is a build failure and not a silently weaker component.  The `_eq`
lemmas are the definitional step (each `Air.Flat.Component` field of
`MemAlign.component` *is* the corresponding mirror predicate, read through
`rowInputOfEnvironment`); the `_weld` theorems compose them with the welds
above. -/

theorem component_spec_eq (env : Environment FGL) :
    component.Spec env ↔ Spec (rowInputOfEnvironment env) :=
  Iff.rfl

theorem component_transition_eq (index : ℕ) (previous current : Environment FGL) :
    component.transition index previous current ↔
      transitionRows (rowInputOfEnvironment previous) (rowInputOfEnvironment current) :=
  Iff.rfl

theorem component_cyclicSuccessorTransition_eq
    (index : ℕ) (current successor : Environment FGL) :
    component.cyclicSuccessorTransition index current successor ↔
      cyclicSuccessorTransitionRows (rowInputOfEnvironment current)
        (rowInputOfEnvironment successor) :=
  Iff.rfl

/-- `MemAlign.component.Spec`, welded. -/
theorem component_spec_weld (previous env successor : Environment FGL) :
    component.Spec env ↔
      MemAlign.extraction.constraint_25_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_26_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_27_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_28_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_17_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_18_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_19_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_20_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_21_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_22_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_23_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_24_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_16_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_30_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_31_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_32_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
          (rowInputOfEnvironment successor)) 1
      :=
  (component_spec_eq env).trans
    (spec_weld (rowInputOfEnvironment previous) (rowInputOfEnvironment env)
      (rowInputOfEnvironment successor))

/-- `MemAlign.component.transition`, welded. -/
theorem component_transition_weld (index : ℕ) (previous current successor : Environment FGL) :
    component.transition index previous current ↔
      MemAlign.extraction.constraint_29_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_1_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_3_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_5_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_7_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_9_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_11_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_13_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_15_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      :=
  (component_transition_eq index previous current).trans
    (transitionRows_weld (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
      (rowInputOfEnvironment successor))

/-- `MemAlign.component.cyclicSuccessorTransition`, welded.  The visible first
    conjunct is the `delta_pc` relation; see
    `cyclicSuccessorTransitionRows_weld`. -/
theorem component_cyclicSuccessorTransition_weld
    (index : ℕ) (previous current successor : Environment FGL) :
    component.cyclicSuccessorTransition index current successor ↔
      ((rowInputOfEnvironment current).delta_pc
          = (rowInputOfEnvironment successor).pc - (rowInputOfEnvironment current).pc)
      ∧ MemAlign.extraction.constraint_0_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_2_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_4_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_6_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_8_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_10_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_12_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      ∧ MemAlign.extraction.constraint_14_every_row (windowOf (rowInputOfEnvironment previous) (rowInputOfEnvironment current)
          (rowInputOfEnvironment successor)) 1
      :=
  (component_cyclicSuccessorTransition_eq index current successor).trans
    (cyclicSuccessorTransitionRows_weld (rowInputOfEnvironment previous)
      (rowInputOfEnvironment current) (rowInputOfEnvironment successor))

/-! ### From the live `assertZero` list

`component_spec_weld` ties the generated constraints to `Spec`, the predicate
the component *publishes*.  `Spec` is not what the circuit *asserts*; `main`
(`ZiskFv/AirsClean/MemAlign/Constraints.lean`) is.  `spec_of_mainSoundness`
projects `Spec` out of `main`'s own operation list, and
`extracted_of_mainSoundness` composes that projection with `spec_weld`, so the
generated constraints are reachable from the assertion list in one step.

Stated honestly about what each part buys:

* the projection itself is **not** new protection.  It repeats the sixteen-way
  destructuring `MemAlign.circuit.soundness` already performs, so a lone drift
  in an `assertZero` expression already fails there, before reaching this
  module.
* the *composition* is what is new.  A slip that is self-consistent across the
  `Spec` predicate, the `assertZero` expression and `MemAlign.soundness`'s
  hypothesis is invisible to every proof in the repository — measured, not
  assumed: commuting `preL1 * pc` to `pc * preL1` in all three of
  `MemAlign/Spec.lean`, `MemAlign/Constraints.lean` and `MemAlign/Soundness.lean`
  at once leaves `lake build` green everywhere except `spec_weld`. -/

set_option maxRecDepth 4000 in
theorem spec_of_mainSoundness (offset : ℕ) (env : Environment FGL)
    (row : Var MemAlignRow FGL)
    (h : ConstraintsHold.Soundness env ((main row).operations offset)) :
    Spec (eval env row) := by
  simp only [circuit_norm, main] at h
  simp only [Spec, circuit_norm]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15⟩ := h
  exact ⟨ by simpa only [sub_eq_add_neg] using h0
        , by simpa only [sub_eq_add_neg] using h1
        , by simpa only [sub_eq_add_neg] using h2
        , by simpa only [sub_eq_add_neg] using h3
        , by simpa only [sub_eq_add_neg] using h4
        , by simpa only [sub_eq_add_neg] using h5
        , by simpa only [sub_eq_add_neg] using h6
        , by simpa only [sub_eq_add_neg] using h7
        , by simpa only [sub_eq_add_neg] using h8
        , by simpa only [sub_eq_add_neg] using h9
        , by simpa only [sub_eq_add_neg] using h10
        , by simpa only [sub_eq_add_neg] using h11
        , by simpa only [sub_eq_add_neg] using h12
        , by simpa only [sub_eq_add_neg] using h13
        , by simpa only [sub_eq_add_neg] using h14
        , by simpa only [sub_eq_add_neg] using h15 ⟩

/-- The AIR's sixteen per-row constraints, derived from the MemAlign circuit's
    own assertions. -/
theorem extracted_of_mainSoundness (offset : ℕ) (env : Environment FGL)
    (row : Var MemAlignRow FGL) (previous successor : MemAlignRow FGL)
    (h : ConstraintsHold.Soundness env ((main row).operations offset)) :
      MemAlign.extraction.constraint_25_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_26_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_27_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_28_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_17_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_18_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_19_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_20_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_21_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_22_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_23_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_24_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_16_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_30_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_31_every_row (windowOf previous (eval env row) successor) 1
      ∧ MemAlign.extraction.constraint_32_every_row (windowOf previous (eval env row) successor) 1
  := (spec_weld previous (eval env row) successor).mp
      (spec_of_mainSoundness offset env row h)

/-! ## Which lanes a welded constraint is allowed to read

Both bridges are total, so they answer somewhere they are not modeling: `0` for
every stage-2 read (`id ≠ 1`), `0` for stage-1 columns `≥ 29`, `0` on the whole
`challenge` and `exposed` lanes, `0` for `preprocessed` columns `≥ 1`, and —
because both ignore their `rotation` argument — the same cell at every rotation.
`windowRowAt` additionally aliases every generated row index `≥ 2` to
`successor`.  Those answers are harmless only if no welded constraint can
observe them.  This section checks that instead of asserting it.

`MemAlignProbe` is the *free* `Extraction.Circuit`: every lane is an
unconstrained function field.  Instantiating a generated constraint there turns
each cell read into an application of a variable, so a `rfl`-level identity
between a probe and its restriction is a statement about which cells the
generated body mentions, not about their values. -/

/-- The free `Extraction.Circuit` over `FGL`: each lane is a function field. -/
structure MemAlignProbe (F ExtF : Type) where
  mainCell : ℕ → ℕ → ℕ → ℕ → FGL
  preprocessedCell : ℕ → ℕ → ℕ → FGL
  challengeCell : ℕ → FGL
  exposedCell : ℕ → FGL

instance memAlignProbeCircuit : Extraction.Circuit FGL FGL MemAlignProbe where
  main c := c.mainCell
  preprocessed c := c.preprocessedCell
  challenge c := c.challengeCell
  exposed c := c.exposedCell

/-- `c` cut down to the lanes both bridges model: stage 1, columns `< 29`,
    rotation `0`; `preprocessed` column `0` at rotation `0`; `0` on `challenge`
    and `exposed` outright.  Trace rows are left alone — Bridge A models all of
    them. -/
@[reducible]
def restrictToModeledLanes (c : MemAlignProbe FGL FGL) : MemAlignProbe FGL FGL where
  mainCell := fun id column row rotation =>
    if id = 1 ∧ column < 29 ∧ rotation = 0 then c.mainCell id column row rotation else 0
  preprocessedCell := fun column row rotation =>
    if column = 0 ∧ rotation = 0 then c.preprocessedCell column row rotation else 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- `c` cut down further to the three rows Bridge B distinguishes. -/
@[reducible]
def restrictToWindowRows (c : MemAlignProbe FGL FGL) : MemAlignProbe FGL FGL where
  mainCell := fun id column row rotation =>
    if id = 1 ∧ column < 29 ∧ row < 3 ∧ rotation = 0 then c.mainCell id column row rotation else 0
  preprocessedCell := fun column row rotation =>
    if column = 0 ∧ row < 3 ∧ rotation = 0 then c.preprocessedCell column row rotation else 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- `P c r` is unchanged by zeroing every lane the bridges stub.

    Unfolded: `P c r` may mention `c.mainCell 1 k r' 0` for `k < 29` and
    `c.preprocessedCell 0 r' 0`, and nothing else.  A read of a stage-2 column,
    of stage-1 column `≥ 29`, of a nonzero rotation, of `preprocessed` column
    `≥ 1`, or of `challenge`/`exposed` would leave a free `c.<lane> …` on the
    left of the `Iff` with no counterpart on the right, and `Iff.rfl` would not
    typecheck. -/
@[reducible]
def ReadsOnlyModeledLanes (P : MemAlignProbe FGL FGL → ℕ → Prop) : Prop :=
  ∀ (c : MemAlignProbe FGL FGL) (r : ℕ), P c r ↔ P (restrictToModeledLanes c) r

/-- As `ReadsOnlyModeledLanes`, and additionally: read at generated row index
    `1`, `P` mentions no trace row outside `{0, 1, 2}`.  This is what makes
    `windowRowAt`'s `| _ => successor` fold safe for the Bridge B welds. -/
@[reducible]
def ReadsOnlyWindowRows (P : MemAlignProbe FGL FGL → ℕ → Prop) : Prop :=
  ∀ c : MemAlignProbe FGL FGL, P c 1 ↔ P (restrictToWindowRows c) 1

/-- Each of the MemAlign AIR's 33 F-only constraints reads only the lanes the
    bridges model.

    The property is not vacuous — measured, by substituting a non-F-only
    constraint into the first conjunct and rebuilding.  Asserted of
    `constraint_39_every_row` (which reads `preprocessed (column := 1)`,
    `Extraction.Circuit.exposed` and stage 2), `Iff.rfl` is rejected with a type
    mismatch.  Asserted of `constraint_36_every_row` (`main (id := 2)` plus
    `Extraction.Circuit.challenge`) the defeq check does not terminate and the
    declaration is rejected with `maximum recursion depth has been reached`.
    Either way it does not compile.  Those are two of the seven generated
    constraints outside the F-only set. -/
theorem memAlignConstraints_readOnlyModeledLanes :
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_0_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_1_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_2_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_3_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_4_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_5_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_6_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_7_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_8_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_9_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_10_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_11_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_12_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_13_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_14_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_15_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_16_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_17_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_18_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_19_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_20_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_21_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_22_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_23_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_24_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_25_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_26_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_27_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_28_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_29_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_30_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_31_every_row
    ∧
    ReadsOnlyModeledLanes MemAlign.extraction.constraint_32_every_row
     :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- Read at generated row index `1`, each of the 33 mentions only trace rows
    `0`, `1` and `2` — the rows Bridge B's window distinguishes.

    Not vacuous in the same way, and again measured: asserted of
    `constraint_38_every_row`, whose `'gsum` read is at `row - 1` of a stage-2
    column, `Iff.rfl` is rejected with a type mismatch. -/
theorem memAlignConstraints_readOnlyWindowRows :
    ReadsOnlyWindowRows MemAlign.extraction.constraint_0_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_1_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_2_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_3_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_4_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_5_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_6_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_7_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_8_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_9_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_10_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_11_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_12_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_13_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_14_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_15_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_16_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_17_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_18_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_19_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_20_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_21_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_22_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_23_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_24_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_25_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_26_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_27_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_28_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_29_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_30_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_31_every_row
    ∧
    ReadsOnlyWindowRows MemAlign.extraction.constraint_32_every_row
     :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

/-- `extractedColumns columns` re-expressed in the free circuit. -/
@[reducible]
def probeOfColumnTrace (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL) :
    MemAlignProbe FGL FGL where
  mainCell := columnTraceMain (extractedColumns columns)
  preprocessedCell := columnTracePreprocessed (extractedColumns columns)
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- `windowOf previous current successor` re-expressed in the free circuit. -/
@[reducible]
def probeOfWindow (previous current successor : MemAlignRow FGL) : MemAlignProbe FGL FGL where
  mainCell := windowMain (windowOf previous current successor)
  preprocessedCell := windowPreprocessed (windowOf previous current successor)
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- The bridge from the two weld circuits into the free circuit.  Composed with
    `memAlignConstraints_readOnlyModeledLanes` it gives: a welded constraint
    cannot observe a stubbed lane, so the `0` defaults in `stage1Column`,
    `preprocessedColumn` and the `challenge`/`exposed` stubs cannot be what
    makes a weld true.  Stated for all 33 F-only constraints at both bridges. -/
theorem memAlignConstraints_probeBridge
    (columns : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (previous current successor : MemAlignRow FGL) (r : ℕ) :
    (MemAlign.extraction.constraint_0_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_0_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_0_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_0_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_1_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_1_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_1_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_1_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_2_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_2_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_2_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_2_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_3_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_3_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_3_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_3_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_4_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_4_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_4_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_4_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_5_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_5_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_5_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_5_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_6_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_6_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_6_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_6_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_7_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_7_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_7_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_7_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_8_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_8_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_8_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_8_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_9_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_9_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_9_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_9_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_10_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_10_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_10_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_10_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_11_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_11_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_11_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_11_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_12_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_12_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_12_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_12_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_13_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_13_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_13_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_13_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_14_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_14_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_14_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_14_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_15_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_15_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_15_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_15_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_16_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_16_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_16_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_16_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_17_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_17_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_17_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_17_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_18_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_18_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_18_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_18_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_19_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_19_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_19_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_19_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_20_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_20_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_20_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_20_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_21_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_21_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_21_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_21_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_22_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_22_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_22_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_22_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_23_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_23_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_23_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_23_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_24_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_24_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_24_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_24_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_25_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_25_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_25_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_25_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_26_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_26_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_26_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_26_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_27_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_27_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_27_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_27_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_28_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_28_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_28_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_28_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_29_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_29_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_29_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_29_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_30_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_30_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_30_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_30_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_31_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_31_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_31_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_31_every_row
            (probeOfWindow previous current successor) 1)
    ∧
    (MemAlign.extraction.constraint_32_every_row (extractedColumns columns) r
        ↔ MemAlign.extraction.constraint_32_every_row (probeOfColumnTrace columns) r)
    ∧ (MemAlign.extraction.constraint_32_every_row (windowOf previous current successor) 1
        ↔ MemAlign.extraction.constraint_32_every_row
            (probeOfWindow previous current successor) 1)
     :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## The instances are pinned to the pinned column map

A column-map gate can read `stage1Column` and `preprocessedColumn` and nothing
else.  Rebinding either instance's `main` or `preprocessed` field to some other
function would leave such a gate green while every weld above silently spoke
about a different column map: a gate that appears to check something it does
not.  This is the hazard review found in the Arith weld (eth-act/zisk-fv#300),
and it is closed here from the start.

Both theorems are stated through `inferInstance`, so each fails to compile if
any field of its instance drifts *and* if class resolution for
`Extraction.Circuit FGL FGL _` starts finding a different instance.  They are
deliberately the last declarations in the module: every weld above resolves that
class against the instances declared before them, so an instance introduced
anywhere above — including one shadowing these — is also the one these theorems
resolve and check. -/

theorem memAlignColumnTraceCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL MemAlignColumnTrace) =
      { main := columnTraceMain
        preprocessed := columnTracePreprocessed
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

theorem memAlignRowWindowCircuit_pinned :
    (inferInstance : Extraction.Circuit FGL FGL MemAlignRowWindow) =
      { main := windowMain
        preprocessed := windowPreprocessed
        challenge := fun _ _ => 0
        exposed := fun _ _ => 0 } :=
  rfl

end ZiskFv.AirsClean.MemAlignMirrorWeld
