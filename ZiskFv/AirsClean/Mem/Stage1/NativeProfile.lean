import ZiskFv.AirsClean.Mem.Stage1.SourceColumns
import Extraction.RuntimeMemWriteByteTraceLayout

/-! INTERNAL correspondence to the actual same-source-renderer Mem companion.
No native getter, parser, Profile type, cast or unpacked range predicate is
introduced. SourceColumn ordinals are not compiled native r.id/opening ids. -/
namespace ZiskFv.AirsClean.Mem.Stage1.NativeProfile

open Extraction.RuntimeMainTraceLayout Extraction.RuntimeMemWriteByteTraceLayout
open SourceColumns

/-- The independent source inventory describes EVERY actual logical cell. -/
theorem actual_cell (column : Column) :
    memProfile.cells[column.val]? =
      some ⟨(nativeKey column).1, (nativeKey column).2,
        packedWidth column, bitOffset column⟩ := by
  fin_cases column <;> rfl

theorem actual_profile_scope :
    memProfile.nativeName = "MemTraceRow" ∧ memProfile.rowParameter = "R" ∧
    memProfile.nativeRows = physicalRows ∧ memProfile.nativeGroup = 0 ∧
    memProfile.nativeAir = 14 ∧ memProfile.unpackedWords = 13 ∧
    memProfile.packedBits = 252 ∧ memProfile.packedWords = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual emitted native ordinal -> actual PIL declaration/array coordinate.
There are no skipped cells, stageId matches, free native-layout certificates or
assumptions that the native operand/opening id equals this logical ordinal. -/
theorem actual_native_to_pil (column : Column) :
    (memProfile.cells[column.val]?).bind
      (fun cell => pilColumn? (cell.field, cell.indices)) = some column.val := by
  rw [actual_cell]
  exact native_order_is_pil_order column

theorem actual_keys_injective (left right : Column)
    (same : (memProfile.cells[left.val]?).map (fun cell => (cell.field, cell.indices)) =
      (memProfile.cells[right.val]?).map (fun cell => (cell.field, cell.indices))) :
    left = right := by
  rw [actual_cell, actual_cell] at same
  apply native_keys_injective
  exact Option.some.inj same

theorem all_pil_cells_covered (pil : Column) :
    ∃ native : Column, (memProfile.cells[native.val]?).bind
      (fun cell => pilColumn? (cell.field, cell.indices)) = some pil.val :=
  ⟨pil, actual_native_to_pil pil⟩

end ZiskFv.AirsClean.Mem.Stage1.NativeProfile
