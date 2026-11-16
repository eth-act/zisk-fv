import ZiskFv.AirsClean.Mem.PhysicalSource.Domain
import ZiskFv.AirsClean.NativeTraceCells

/-! INTERNAL Mem projection through the ONE owner-supplied shared native-cell
implementation (six-kind checkpoint205c4c19). No second getter/parser/Kind or
word->field callback is implemented here. BOTH packed and unpacked rows use the
same occurrence's original UInt64 store; unpacked field storage is not forced
through Rust typed Bool/narrow getters or additional range predicates.
This source-only bridge does not authenticate native/PIL operands, runtime ABI,
materialized execution, stage2 auxiliary/challenge worlds or live Root data. -/
namespace ZiskFv.AirsClean.Mem.PhysicalSource.NativeProjection

open Goldilocks
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native
open Extraction.RuntimeMemWriteByteTraceLayout

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- One checked source geometry supplies every finite canonical row view. -/
theorem shared_row_base (view : View resolved) (row : view.Index) :
    NativeTraceCells.rowBase? .mem resolved false row.val =
      some (row.val * view.nativeStride) := by
  have scope := view.registry_scope
  have cpu := view.cpu_profile
  have rows : view.setup.rowCount = memProfile.nativeRows := by
    simpa [View.count, Stage1.SourceColumns.physicalRows] using view.setup_rows
  have within : row.val < view.setup.rowCount := by
    rw [view.setup_rows]
    exact row.isLt
  have stride : resolved.slotData.metadata.nColsTrace =
      NativeTraceCells.nativeStride .mem resolved.slotData.metadata.isPacked := by
    simpa [NativeTraceCells.nativeStride, NativeTraceCells.profile] using view.native_stride_profile
  have coverage : view.setup.rowCount * resolved.slotData.metadata.nColsTrace ≤
      (resolved.params false).trace.size := by
    simpa [view.setup_rows, View.nativeStride] using view.trace_coverage
  simp only [NativeTraceCells.rowBase?, view.setupSelected, bind, pure,
    view.cm1Selected]
  rw [if_pos ⟨NativeTraceRules.actual_source_ready, scope.1, scope.2, cpu.1, cpu.2,
    rows, within, view.logical_width, stride, view.native_stride_positive, coverage⟩]

def sharedRow (view : View resolved) (row : view.Index) :
    NativeTraceCells.Row .mem resolved false row.val :=
  ⟨row.val * view.nativeStride, shared_row_base view row⟩

/-- Exactly one finite thirteen-cell request is allocated WHEN a row is
requested. The domain is lazy Fin4194304, not a materialized row array/list. -/
def logicalRow (view : View resolved) (row : view.Index) : Vector FGL 13 :=
  match selected : (sharedRow view row).values? with
  | some values => values
  | none => False.elim (by
      obtain ⟨values, present⟩ := (sharedRow view row).values_defined
      simp [selected] at present)

theorem logicalRow_checked (view : View resolved) (row : view.Index) :
    (sharedRow view row).values? = some (logicalRow view row) := by
  unfold logicalRow
  split
  · rfl
  · rename_i absent
    obtain ⟨values, present⟩ := (sharedRow view row).values_defined
    simp [absent] at present

/-- Every requested logical coordinate is the actual shared native result. -/
theorem actual_coordinates (view : View resolved) (row : view.Index)
    (column : Stage1.SourceColumns.Column) :
    NativeTraceCells.cell? .mem resolved false row.val column.val =
      some (logicalRow view row)[column.val] :=
  (sharedRow view row).values_coordinates _ (logicalRow_checked view row) column

/-- Exact current PIL metadata identity, not a guessed compiled r.id or cm map
stageId. Unknown/unsupported native fields are not silently assigned zero. -/
theorem actual_pil_binding (column : Stage1.SourceColumns.Column) :
    (NativeTraceCells.selectedCell? .mem column.val).bind
      (fun cell => Stage1.SourceColumns.pilColumn? (cell.field, cell.indices)) =
      some column.val := by
  fin_cases column <;> rfl

theorem all_current_stage1_cells (view : View resolved) :
    ∀ row : view.Index, ∀ column : Stage1.SourceColumns.Column,
      NativeTraceCells.cell? .mem resolved false row.val column.val =
        some (logicalRow view row)[column.val] ∧
      (NativeTraceCells.selectedCell? .mem column.val).bind
        (fun cell => Stage1.SourceColumns.pilColumn? (cell.field, cell.indices)) =
        some column.val := by
  intro row column
  exact ⟨actual_coordinates view row column, actual_pil_binding column⟩

/-- Both physical row values and all extension blocks are tied to the SAME
source and occurrence. No detached group result or padding/prefix count enters. -/
def jointAt (view : View resolved) (row : view.Index) :
    Vector FGL 13 × Stage2.Ext3 FGL × (Fin 6 → Stage2.Ext3 FGL) :=
  (logicalRow view row, view.group, view.direct)

theorem physical_last_keeps_joint_source (view : View resolved) :
    view.l1? (view.next view.last) = some 1 ∧
    jointAt view view.last = (logicalRow view view.last, view.group, view.direct) := by
  constructor
  · have positive := view.count_pos
    simp [view.shifted_l1, View.last,
      Nat.sub_add_cancel (by omega : 1 ≤ view.count)]
  · rfl

end ZiskFv.AirsClean.Mem.PhysicalSource.NativeProjection
