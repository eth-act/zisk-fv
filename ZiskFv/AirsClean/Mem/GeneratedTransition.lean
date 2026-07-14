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

/-- Map the 15 effective Mem slots to the 13 raw witness slots followed by
`SEGMENT_L1` and `__L1__`. -/
private def memFixedLayout (slot : Fin 15) : Sum (Fin 13) (Fin 2) :=
  if h_raw : slot.val < 13 then
    .inl ⟨slot.val, h_raw⟩
  else if h_segment_l1 : slot.val = 13 then
    .inr ⟨0, by decide⟩
  else
    .inr ⟨1, by decide⟩

/-- Both fixed selectors are `[1, 0, ...]` over the physical Mem domain. -/
private def memFixedValues (_slot : Fin 2) (row : Fin memFixedCapacity) : FGL :=
  if row.val = 0 then 1 else 0

/-- Component-owned physical Mem fixed schema. `fixedAt` rotates by its actual
domain, while `Table.fixed_domain` prevents a materialized table from wrapping. -/
def memFixedColumns : IndexedFixedColumns FGL 13 where
  capacity := memFixedCapacity
  capacity_pos := by decide
  effectiveWidth := 15
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

/-- Materialization preserves every raw Mem witness slot; the two
    component-owned fixed cells are appended after this 13-cell prefix. -/
theorem memFixedColumns_materialize_raw
    (index : Nat) (raw : Array FGL) (slot : Fin 13) :
    (memFixedColumns.materialize index raw)[slot.val]'(by
      change slot.val < 15
      omega) = raw.getD slot.val 0 := by
  simp [IndexedFixedColumns.materialize, memFixedColumns, memFixedLayout]

/-- The 13 raw witness cells of a Mem row. The component-owned fixed columns
    are appended after this exact AIR witness layout. -/
def memRawRow (row : MemRow FGL) : Array FGL :=
  #[row.addr, row.step, row.sel, row.addr_changes, row.step_dual, row.sel_dual,
    row.value_0, row.value_1, row.wr, row.previous_step, row.increment_0,
    row.increment_1, row.read_same_addr]

@[simp] theorem memRawRow_size (row : MemRow FGL) : (memRawRow row).size = 13 := by
  simp [memRawRow]

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

/-- All non-local generated Mem equations at one row, sourced from canonical
live data and the component's fixed schema. -/
def generatedTransition (columns : IndexedFixedColumns FGL 13)
    (index : Nat) (previous current : Environment FGL) : Prop :=
  let mem := memWindow index previous current
  let segment := memSegmentColumnsOfProverDataAndFixed current.data
    (fun row => columns.fixedAt MemFixedColumn.segmentL1 row)
  let permutation := memPermutationColumnsOfProverDataAndFixed current.data
    (fun row => columns.fixedAt MemFixedColumn.l1 row)
  ZiskFv.Airs.Mem.segmentResidualEveryRow segment mem index
    ∧ ZiskFv.Airs.Mem.permutation_every_row segment permutation mem index

end ZiskFv.AirsClean.Mem
