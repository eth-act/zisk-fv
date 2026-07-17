import Extraction.LookupWiring
import ZiskFv.AirsClean.RangeTables
import ZiskFv.AirsClean.Mem.SidecarColumns
import ZiskFv.AirsClean.Mem.GeneratedTransition
import ZiskFv.Channels.SpecifiedRanges

/-!
# Source-linked Mem range wiring

The generated `LookupWiring` links validate the PIL hint tuple against the
extracted accumulator constraint. This module is the small live-model bridge:
it carries the validated hint, the exact raw cell used by the live emission,
and that cell's canonical `ProverData` materialization theorem. It does not
assert range membership; finished-channel balance plus the static provider
supplies that in PR 2b.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.SpecifiedRanges

structure MemRangeWiring where
  link : ValidatedLink
  hint : HintTuple
  validatedHint : link.hints = [hint]
  rawColumn : Nat
  proverDataKey : String
  source : Expression FGL
  sourceRawColumn : source = Expression.var ⟨rawColumn⟩
  sourceMaterializes : ∀ (index : Nat) (data : ProverData FGL) (row : MemRow FGL),
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      source = proverDataScalar data proverDataKey

@[reducible]
def distanceBase0Wiring : MemRangeWiring where
  link := link_Mem_29
  hint := hint_Mem_29_0
  validatedHint := rfl
  rawColumn := MemRangeSidecarRawColumn.distanceBase0
  proverDataKey := MemRawSidecarDataKey.Segment.distanceBase0
  source := memDistanceBase0Expr
  sourceRawColumn := rfl
  sourceMaterializes := eval_memDistanceBase0Expr_materialize

@[reducible]
def distanceBase1Wiring : MemRangeWiring where
  link := link_Mem_30
  hint := hint_Mem_30_0
  validatedHint := rfl
  rawColumn := MemRangeSidecarRawColumn.distanceBase1
  proverDataKey := MemRawSidecarDataKey.Segment.distanceBase1
  source := memDistanceBase1Expr
  sourceRawColumn := rfl
  sourceMaterializes := eval_memDistanceBase1Expr_materialize

@[reducible]
def distanceEnd0Wiring : MemRangeWiring where
  link := link_Mem_31
  hint := hint_Mem_31_0
  validatedHint := rfl
  rawColumn := MemRangeSidecarRawColumn.distanceEnd0
  proverDataKey := MemRawSidecarDataKey.Segment.distanceEnd0
  source := memDistanceEnd0Expr
  sourceRawColumn := rfl
  sourceMaterializes := eval_memDistanceEnd0Expr_materialize

@[reducible]
def distanceEnd1Wiring : MemRangeWiring where
  link := link_Mem_32
  hint := hint_Mem_32_0
  validatedHint := rfl
  rawColumn := MemRangeSidecarRawColumn.distanceEnd1
  proverDataKey := MemRawSidecarDataKey.Segment.distanceEnd1
  source := memDistanceEnd1Expr
  sourceRawColumn := rfl
  sourceMaterializes := eval_memDistanceEnd1Expr_materialize

@[reducible]
def memRangeWirings : List MemRangeWiring :=
  [distanceBase0Wiring, distanceBase1Wiring, distanceEnd0Wiring, distanceEnd1Wiring]

/-- The only live range emissions are the four constraint-validated links,
materialized at their canonical table-resident raw cells. -/
@[reducible]
def rangeMessages : List (SpecifiedRangeMessage (Expression FGL)) :=
  memRangeWirings.map (fun wiring => memDistanceMessage wiring.source)

/-- c29 is the kernel-checked direct-template link for `distance_base[0]`. -/
theorem distanceBase0Wiring_link : distanceBase0Wiring.link = link_Mem_29 := rfl

/-- c30 is the kernel-checked direct-template link for `distance_base[1]`. -/
theorem distanceBase1Wiring_link : distanceBase1Wiring.link = link_Mem_30 := rfl

/-- c31 is the kernel-checked direct-template link for `distance_end[0]`. -/
theorem distanceEnd0Wiring_link : distanceEnd0Wiring.link = link_Mem_31 := rfl

/-- c32 is the kernel-checked direct-template link for `distance_end[1]`. -/
theorem distanceEnd1Wiring_link : distanceEnd1Wiring.link = link_Mem_32 := rfl

/-- The c29 checked wiring expression evaluates at the canonical sidecar key
when its table row is materialized. -/
theorem eval_distanceBase0Wiring_source_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      distanceBase0Wiring.source =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase0 := by
  exact distanceBase0Wiring.sourceMaterializes index data row

/-- The c30 checked wiring expression evaluates at the canonical sidecar key
when its table row is materialized. -/
theorem eval_distanceBase1Wiring_source_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      distanceBase1Wiring.source =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase1 := by
  exact distanceBase1Wiring.sourceMaterializes index data row

/-- The c31 checked wiring expression evaluates at the canonical sidecar key
when its table row is materialized. -/
theorem eval_distanceEnd0Wiring_source_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      distanceEnd0Wiring.source =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd0 := by
  exact distanceEnd0Wiring.sourceMaterializes index data row

/-- The c32 checked wiring expression evaluates at the canonical sidecar key
when its table row is materialized. -/
theorem eval_distanceEnd1Wiring_source_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      distanceEnd1Wiring.source =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd1 := by
  exact distanceEnd1Wiring.sourceMaterializes index data row

/-! ## Concrete source value -/

/-- One table's shared prover data supplies the c29 range value. -/
def distanceBase0DemoData : ProverData FGL := fun key width =>
  if key = MemRawSidecarDataKey.Segment.distanceBase0 then
    match width with
    | 1 => #[Vector.ofFn fun _ : Fin 1 => (7 : FGL)]
    | _ => #[]
  else #[]

@[reducible]
def distanceBase0DemoRow : MemRow FGL :=
  { addr := 0, step := 0, sel := 0, addr_changes := 0, step_dual := 0, sel_dual := 0
    value_0 := 0, value_1 := 0, wr := 0, previous_step := 0, increment_0 := 0
    increment_1 := 0, read_same_addr := 0 }

@[reducible]
def distanceBase0DemoEnvironment : Environment FGL :=
  Environment.fromArray
    (memFixedColumns.materialize 0
      (memRawRowWithProverData distanceBase0DemoData distanceBase0DemoRow))
    distanceBase0DemoData

@[reducible]
def distanceBase0DemoValue : FGL :=
  Expression.eval distanceBase0DemoEnvironment distanceBase0Wiring.source

theorem distanceBase0DemoValue_eq : distanceBase0DemoValue = 7 := by
  unfold distanceBase0DemoValue
  rw [show distanceBase0Wiring.source = memDistanceBase0Expr by rfl,
    eval_memDistanceBase0Expr_materialize]
  simp [distanceBase0DemoData, proverDataScalar, proverDataColumn]

@[reducible]
def distanceBase0DemoMessage : SpecifiedRangeMessage FGL :=
  memDistanceMessage distanceBase0DemoValue

end ZiskFv.AirsClean.Mem
