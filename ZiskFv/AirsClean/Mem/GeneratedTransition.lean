import Clean.Air.FlatComponent
import ZiskFv.Airs.Mem
import ZiskFv.AirsClean.Mem.Row
import ZiskFv.AirsClean.Mem.SidecarColumns

/-!
# Live generated Mem transition

The local Mem component owns constraints 3--8, 18, 21, and 23. This module
places the remaining generated Mem equations in the same component's indexed
transition, using only the transition's predecessor/current environments, the
shared `ProverData`, and component-owned physical fixed columns.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open Air.Flat

/-- ZisK's Mem witness and fixed traces have one physical `2^22`-row domain. -/
def memFixedCapacity : Nat := 4194304

/-- Map the 19 effective Mem slots to 17 raw witness slots followed by
`SEGMENT_L1` and `__L1__`. The extra raw slots carry the four bus-103 values
that are source-linked to the generated Mem range hints. -/
private def memFixedLayout (slot : Fin 19) : Sum (Fin 17) (Fin 2) :=
  if h_raw : slot.val < 17 then
    .inl ⟨slot.val, h_raw⟩
  else if h_segment_l1 : slot.val = 17 then
    .inr ⟨0, by decide⟩
  else
    .inr ⟨1, by decide⟩

/-- Both fixed selectors are `[1, 0, ...]` over the physical Mem domain. -/
private def memFixedValues (_slot : Fin 2) (row : Fin memFixedCapacity) : FGL :=
  if row.val = 0 then 1 else 0

/-- Component-owned physical Mem fixed schema. `fixedAt` rotates by its actual
domain, while `Table.fixed_domain` prevents a materialized table from wrapping. -/
def memFixedColumns : IndexedFixedColumns FGL 17 where
  capacity := memFixedCapacity
  capacity_pos := by decide
  effectiveWidth := 19
  fixedWidth := 2
  layout := memFixedLayout
  values := memFixedValues

/-- Tiny physical-domain regression for indexed fixed columns. The value at
    row three wraps to row zero of the schema's three-row domain; it does not
    depend on a table prefix length. -/
private def smallRotationRegressionColumns : IndexedFixedColumns FGL 0 where
  capacity := 3
  capacity_pos := by decide
  effectiveWidth := 1
  fixedWidth := 1
  layout := fun _ => .inr ⟨0, by decide⟩
  values := fun _ row => if row.val = 0 then 1 else 0

/-- The indexed fixed-column facility preserves physical-domain rotation on a
    small schema. `Table.fixed_domain` separately prevents a materialized
    witness prefix from relying on this wrap. -/
theorem indexedFixedColumns_smallDomain_rotation_regression :
    smallRotationRegressionColumns.fixedAt 0 3 = 1 ∧
      smallRotationRegressionColumns.fixedAt 0 2 = 0 := by
  constructor <;> rfl

set_option maxHeartbeats 4000000 in
/-- Materialization preserves the original 13 raw Mem witness slots; the two
    component-owned fixed cells follow the four range-channel cells. -/
theorem memFixedColumns_materialize_raw
    (index : Nat) (raw : Array FGL) (slot : Fin 13) :
    (memFixedColumns.materialize index raw)[slot.val]'(by
      change slot.val < 19
      omega) = raw.getD slot.val 0 := by
  simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout,
    dif_pos (by omega : slot.val < 17)]

/-- The raw Mem witness row, with zero defaults for the four source-linked
range cells. Constructors with real prover data use
`memRawRowWithProverData`; the defaults preserve existing standalone-row
regressions whose data is empty. -/
def memRawRow (row : MemRow FGL) : Array FGL :=
  #[row.addr, row.step, row.sel, row.addr_changes, row.step_dual, row.sel_dual,
    row.value_0, row.value_1, row.wr, row.previous_step, row.increment_0,
    row.increment_1, row.read_same_addr, 0, 0, 0, 0]

@[simp] theorem memRawRow_size (row : MemRow FGL) : (memRawRow row).size = 17 := by
  simp [memRawRow]

/-- Materialize the four range-channel cells from exactly the same canonical
`ProverData` keys used by the generated Mem sidecar decoder. -/
def memRawRowWithProverData (data : ProverData FGL) (row : MemRow FGL) : Array FGL :=
  #[row.addr, row.step, row.sel, row.addr_changes, row.step_dual, row.sel_dual,
    row.value_0, row.value_1, row.wr, row.previous_step, row.increment_0,
    row.increment_1, row.read_same_addr,
    proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase0,
    proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase1,
    proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd0,
    proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd1]

@[simp] theorem memRawRowWithProverData_size (data : ProverData FGL) (row : MemRow FGL) :
    (memRawRowWithProverData data row).size = 17 := by
  simp [memRawRowWithProverData]

set_option maxHeartbeats 4000000 in
/-- A selected Mem table row evaluates the first bus-103 raw cell at exactly
the canonical sidecar value from its shared `ProverData`. -/
theorem eval_memDistanceBase0Expr_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      memDistanceBase0Expr =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase0 := by
  change
    (memFixedColumns.materialize index (memRawRowWithProverData data row))[13]'(by
      simp [IndexedFixedColumns.materialize, memFixedColumns]) = _
  simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout,
    memRawRowWithProverData]

set_option maxHeartbeats 4000000 in
/-- A selected Mem table row evaluates the second bus-103 raw cell at its
canonical `ProverData` source. -/
theorem eval_memDistanceBase1Expr_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      memDistanceBase1Expr =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceBase1 := by
  change
    (memFixedColumns.materialize index (memRawRowWithProverData data row))[14]'(by
      simp [IndexedFixedColumns.materialize, memFixedColumns]) = _
  simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout,
    memRawRowWithProverData]

set_option maxHeartbeats 4000000 in
/-- A selected Mem table row evaluates the third bus-103 raw cell at its
canonical `ProverData` source. -/
theorem eval_memDistanceEnd0Expr_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      memDistanceEnd0Expr =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd0 := by
  change
    (memFixedColumns.materialize index (memRawRowWithProverData data row))[15]'(by
      simp [IndexedFixedColumns.materialize, memFixedColumns]) = _
  simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout,
    memRawRowWithProverData]

set_option maxHeartbeats 4000000 in
/-- A selected Mem table row evaluates the fourth bus-103 raw cell at its
canonical `ProverData` source. -/
theorem eval_memDistanceEnd1Expr_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Expression.eval
      (Environment.fromArray
        (memFixedColumns.materialize index (memRawRowWithProverData data row)) data)
      memDistanceEnd1Expr =
        proverDataScalar data MemRawSidecarDataKey.Segment.distanceEnd1 := by
  change
    (memFixedColumns.materialize index (memRawRowWithProverData data row))[16]'(by
      simp [IndexedFixedColumns.materialize, memFixedColumns]) = _
  simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout,
    memRawRowWithProverData]

/-- Materializing a raw Mem row preserves its thirteen witness cells; the
    component-owned fixed cells are outside the `MemRow` input layout. -/
theorem eval_memRawRow_materialize
    (index : Nat) (data : ProverData FGL) (row : MemRow FGL) :
    Eval.eval
      (Environment.fromArray (memFixedColumns.materialize index (memRawRow row)) data)
      (varFromOffset (F := FGL) MemRow 0) = row := by
  rw [ProvableStruct.eval_eq_eval, ProvableStruct.varFromOffset_eq_varFromOffset]
  unfold ProvableStruct.eval ProvableStruct.varFromOffset
  simp only [instProvableStructMemRow, ProvableStruct.eval.go,
    ProvableStruct.varFromOffset.go, ProvableType.eval_field,
    ProvableType.varFromOffset_field, Expression.eval, Nat.zero_add]
  cases row with
  | mk addr step sel addr_changes step_dual sel_dual value_0 value_1 wr previous_step
      increment_0 increment_1 read_same_addr =>
    simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout, memRawRow,
      ProvableType.size]

/-- Decode the 13 raw Mem witness cells from an effective transition environment. -/
@[reducible]
def memRowFromEnvironment (env : Environment FGL) : MemRow FGL :=
  Eval.eval env (varFromOffset (F := FGL) MemRow 0)

/-- The generated equations at `index` use only that row and its saturated
predecessor. Every other request is therefore the predecessor row; the named
AIR formulas only request `index` or `index - 1`. -/
@[reducible]
def memWindow (index : Nat) (previous current : Environment FGL) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL :=
  let rowAt := fun row => if row = index then memRowFromEnvironment current else
    memRowFromEnvironment previous
  { addr := fun row => (rowAt row).addr
    step := fun row => (rowAt row).step
    sel := fun row => (rowAt row).sel
    addr_changes := fun row => (rowAt row).addr_changes
    step_dual := fun row => (rowAt row).step_dual
    sel_dual := fun row => (rowAt row).sel_dual
    value_0 := fun row => (rowAt row).value_0
    value_1 := fun row => (rowAt row).value_1
    wr := fun row => (rowAt row).wr
    previous_step := fun row => (rowAt row).previous_step
    increment_0 := fun row => (rowAt row).increment_0
    increment_1 := fun row => (rowAt row).increment_1
    read_same_addr := fun row => (rowAt row).read_same_addr
    gsum := memSidecarGsumOfProverData current.data
    im_0 := memSidecarIm0OfProverData current.data
    im_1 := memSidecarIm1OfProverData current.data }

/-- The table-resident range cells are definitionally tied to the selected
Mem table's canonical sidecar source. This is an existing-component transition
fact, not an accepted-trace field or a new caller-supplied promise hypothesis. -/
def memRangeSidecarBridge (current : Environment FGL) : Prop :=
  current memDistanceBase0Expr =
      proverDataScalar current.data MemRawSidecarDataKey.Segment.distanceBase0
    ∧ current memDistanceBase1Expr =
      proverDataScalar current.data MemRawSidecarDataKey.Segment.distanceBase1
    ∧ current memDistanceEnd0Expr =
      proverDataScalar current.data MemRawSidecarDataKey.Segment.distanceEnd0
    ∧ current memDistanceEnd1Expr =
      proverDataScalar current.data MemRawSidecarDataKey.Segment.distanceEnd1

/-- All non-local generated Mem equations at one row, sourced from canonical
live data and the component's fixed schema. -/
def generatedTransition (columns : IndexedFixedColumns FGL 17)
    (index : Nat) (previous current : Environment FGL) : Prop :=
  let mem := memWindow index previous current
  let segment := memSegmentColumnsOfProverDataAndFixed current.data
    (fun row => columns.fixedAt MemFixedColumn.segmentL1 row)
  let permutation := memPermutationColumnsOfProverDataAndFixed current.data
    (fun row => columns.fixedAt MemFixedColumn.l1 row)
  ZiskFv.Airs.Mem.segmentResidualEveryRow segment mem index
    ∧ ZiskFv.Airs.Mem.permutation_every_row segment permutation mem index
    ∧ memRangeSidecarBridge current

end ZiskFv.AirsClean.Mem
