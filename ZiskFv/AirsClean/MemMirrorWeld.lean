import Extraction.Mem
import ZiskFv.AirsClean.Mem.Circuit
import ZiskFv.AirsClean.Mem.Bridge
import Extraction.MemGeneratedArtifact

/-!
# Operational Mem segment correspondence

The live component retains the nine local equations and the full generated
segment/continuity family0..23. Numeric protocol equations24..33 are NOT
base-field live restrictions: their independent typed source audits remain in
Mem.Stage2 and Mem.SourceFinalizerEquation, and in the normal generated bridge.
GROUP0 and all three extension coefficients are never represented by AIR0 or
the unused scalar witness payload.

The actual complete compiled34 source family, its0..23/24..33 index partition
and kind-preserving HOT support are checked in Extraction.MemGeneratedArtifact
BEFORE erasure into the old total scalar Circuit interface. The trace adapter
below binds all13 primary columns, AIR0..14 and SEGMENT_L1 to their real source.
All other methods remain ARBITRARY cold fillers. Whole-family kernel proofs
show every one of0..23 and its segment bridge independent of EVERY filler.
Only after those proofs is a private canonical completion instantiated.
Neither support checking nor cold totalization changes any source equation or
provides numericHolds, native totality, balance or a new Root premise.

The pre-existing nine local-row welds, row independence and instance pins remain
unchanged. No global Extraction.Circuit interface or instance family is added.
-/

namespace ZiskFv.AirsClean.MemMirrorWeld

open Goldilocks
open ZiskFv.AirsClean.Mem (MemRow Spec componentWithDualMemBus
  spec_of_componentWithDualMemBus_constraints SegmentConstraintAssertionWitness
  segment_every_row_of_constraint_assertions)
open ZiskFv.Airs.Mem (Valid_Mem SegmentColumns segment_every_row)

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

/-! ## Part B — all24 operational segment equations

The separately typed protocol audit accounts for24..33. It is not a scalar
Circuit claim and does not supply live numeric protocol restrictions. -/

/-- The pre-existing free Circuit supplies arbitrary values at COLD methods.
    These are data, not source-validity or satisfaction hypotheses. -/
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

structure ExtractedMemTrace (F ExtF : Type) where
  private mk ::
  seg : SegmentColumns FGL
  v : Valid_Mem FGL FGL
  cold : MemProbe FGL FGL
  private supported : ∀ index : Fin 24,
    Extraction.MemGeneratedArtifact.segmentSourceSupported
      (Extraction.MemGeneratedArtifact.segmentSource index) = true

/-- The support certificate is computed from actual compiled kind-preserving
    source, not supplied by a caller or filtered by the desired Spec. -/
@[reducible]
def traceWithCold (seg : SegmentColumns FGL) (v : Valid_Mem FGL FGL)
    (cold : MemProbe FGL FGL) : ExtractedMemTrace FGL FGL :=
  ⟨seg, v, cold, Extraction.MemGeneratedArtifact.compiled_segment_source_support⟩

@[reducible]
def traceMainValue (c : ExtractedMemTrace FGL FGL)
    (id column row rotation : ℕ) : FGL :=
  if id = 1 ∧ rotation = 0 then
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
    | _ => c.cold.mainCell id column row rotation
  else c.cold.mainCell id column row rotation

@[reducible]
def tracePreprocessedValue (c : ExtractedMemTrace FGL FGL)
    (column row rotation : ℕ) : FGL :=
  if column = 0 ∧ rotation = 0 then c.seg.segment_l1 row
  else c.cold.preprocessedCell column row rotation

@[reducible]
def traceChallengeValue (c : ExtractedMemTrace FGL FGL) (index : ℕ) : FGL :=
  c.cold.challengeCell index

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
  | _ => c.cold.exposedCell index

instance extractedMemTraceCircuit : Extraction.Circuit FGL FGL ExtractedMemTrace where
  main := traceMainValue
  preprocessed := tracePreprocessedValue
  challenge := traceChallengeValue
  exposed := traceExposedValue

/-- Fin24 plus the compiled34 partition prevents an unaccounted source tail. -/
def segmentConstraint (index : Fin 24) :
    ExtractedMemTrace FGL FGL → ℕ → Prop :=
  match index.val with
  | 0 => Mem.extraction.constraint_0_every_row
  | 1 => Mem.extraction.constraint_1_every_row
  | 2 => Mem.extraction.constraint_2_every_row
  | 3 => Mem.extraction.constraint_3_every_row
  | 4 => Mem.extraction.constraint_4_every_row
  | 5 => Mem.extraction.constraint_5_every_row
  | 6 => Mem.extraction.constraint_6_every_row
  | 7 => Mem.extraction.constraint_7_every_row
  | 8 => Mem.extraction.constraint_8_every_row
  | 9 => Mem.extraction.constraint_9_every_row
  | 10 => Mem.extraction.constraint_10_every_row
  | 11 => Mem.extraction.constraint_11_every_row
  | 12 => Mem.extraction.constraint_12_every_row
  | 13 => Mem.extraction.constraint_13_every_row
  | 14 => Mem.extraction.constraint_14_every_row
  | 15 => Mem.extraction.constraint_15_every_row
  | 16 => Mem.extraction.constraint_16_every_row
  | 17 => Mem.extraction.constraint_17_every_row
  | 18 => Mem.extraction.constraint_18_every_row
  | 19 => Mem.extraction.constraint_19_every_row
  | 20 => Mem.extraction.constraint_20_every_row
  | 21 => Mem.extraction.constraint_21_every_row
  | 22 => Mem.extraction.constraint_22_every_row
  | _ => Mem.extraction.constraint_23_every_row

/-- EVERY actual operational constraint is independent of ALL arbitrary COLD
    methods, not merely of a chosen zero completion or selected examples. -/
theorem segmentConstraints_cold_independent
    (seg : SegmentColumns FGL) (v : Valid_Mem FGL FGL)
    (first second : MemProbe FGL FGL) (row : ℕ) (index : Fin 24) :
    segmentConstraint index (traceWithCold seg v first) row ↔
      segmentConstraint index (traceWithCold seg v second) row := by
  fin_cases index <;> exact Iff.rfl

theorem segment_weld_withCold (seg : SegmentColumns FGL)
    (v : Valid_Mem FGL FGL) (cold : MemProbe FGL FGL) (r : ℕ) :
    segment_every_row seg v r ↔
      Mem.extraction.constraint_0_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_1_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_2_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_3_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_4_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_5_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_6_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_7_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_8_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_9_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_10_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_11_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_12_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_13_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_14_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_15_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_16_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_17_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_18_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_19_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_20_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_21_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_22_every_row (traceWithCold seg v cold) r
      ∧ Mem.extraction.constraint_23_every_row (traceWithCold seg v cold) r :=
  Iff.rfl

/-- Canonical completion is PRIVATE and occurs only after actual source support
    and whole-family arbitrary-filler independence. No extension value is filled. -/
private def coldCompletion : MemProbe FGL FGL where
  mainCell := fun _ _ _ _ => 0
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

@[reducible]
def extractedMemTrace (seg : SegmentColumns FGL)
    (v : Valid_Mem FGL FGL) : ExtractedMemTrace FGL FGL :=
  traceWithCold seg v coldCompletion

theorem constraint_0_weld (seg : SegmentColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    (seg.is_first_segment * (1 - seg.is_first_segment) = 0) ↔
      Mem.extraction.constraint_0_every_row (extractedMemTrace seg v) r :=
  Iff.rfl

theorem constraint_11_weld (seg : SegmentColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    (seg.segment_l1 (r + 1) * (v.addr r - seg.segment_last_addr) = 0) ↔
      Mem.extraction.constraint_11_every_row (extractedMemTrace seg v) r :=
  Iff.rfl

theorem constraint_19_weld (seg : SegmentColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    ((1 - v.addr_changes r) *
        (v.addr r - ZiskFv.Airs.Mem.segment_previous_addr seg v r) = 0) ↔
      Mem.extraction.constraint_19_every_row (extractedMemTrace seg v) r :=
  Iff.rfl

theorem segment_weld (seg : SegmentColumns FGL)
    (v : Valid_Mem FGL FGL) (r : ℕ) :
    segment_every_row seg v r ↔
      Mem.extraction.constraint_0_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_1_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_2_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_3_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_4_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_5_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_6_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_7_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_8_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_9_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_10_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_11_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_12_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_13_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_14_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_15_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_16_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_17_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_18_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_19_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_20_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_21_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_22_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_23_every_row (extractedMemTrace seg v) r :=
  segment_weld_withCold seg v coldCompletion r

theorem extracted_of_segmentConstraintAssertions
    {seg : SegmentColumns FGL} {v : Valid_Mem FGL FGL} {r : ℕ}
    (w : SegmentConstraintAssertionWitness seg v r) :
    Mem.extraction.constraint_0_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_1_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_2_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_3_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_4_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_5_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_6_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_7_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_8_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_9_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_10_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_11_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_12_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_13_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_14_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_15_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_16_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_17_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_18_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_19_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_20_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_21_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_22_every_row (extractedMemTrace seg v) r
      ∧ Mem.extraction.constraint_23_every_row (extractedMemTrace seg v) r :=
  (segment_weld seg v r).mp (segment_every_row_of_constraint_assertions w)

/-- `extractedMemRow row` re-expressed in the free circuit: `rowMainValue` in the
    stage-1 lane, `0` in every stub lane. -/
@[reducible]
def probeOfRow (row : MemRow FGL) : MemProbe FGL FGL where
  mainCell := rowMainValue (extractedMemRow row)
  preprocessedCell := fun _ _ _ => 0
  challengeCell := fun _ => 0
  exposedCell := fun _ => 0

/-- The unchanged nine local predicates agree through their two existing
    Circuit instances, independently of the row index used here. -/
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
    Mem.extraction.constraint_11_every_row (extractedMemTrace seg v) r ↔
    Mem.extraction.constraint_11_every_row (extractedMemTrace seg v) r'`.
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
