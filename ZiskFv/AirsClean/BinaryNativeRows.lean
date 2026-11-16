import ZiskFv.AirsClean.NativeTraceCells
import ZiskFv.AirsClean.Binary.Row
import Extraction.SourceDimensions

/-!
INTERNAL Binary full physical-domain projection, using the SOLE NativeTraceCells
source-profile decoder. No second packed decoder, matrix, source crop or N-row
list is constructed. genProof=false selects the constraint Params; actual slot
metadata independently chooses the packed or unpacked PRIMARY getter.

The native source declaration starts with b_op, unlike the nested Clean row.
All 39 coordinates are retained explicitly, including all arrays/mode columns.
Unpacked F storage is not reinterpreted as a typed Rust Bool return value.
This is structural source fidelity, not production/Accepted/ABI authentication.
-/
namespace ZiskFv.AirsClean.BinaryNativeRows

open Goldilocks
open ZiskFv.AirsClean
open ZiskFv.AirsClean.Binary
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

abbrev Index := Fin Extraction.SourceDimensions.Binary.rowCount

/-- Actual compiled physical capacity, not the PIL template's default argument
or a populated-prefix length. This equality is used for every row bound. -/
theorem actual_physical_capacity :
    (NativeTraceCells.profile .binary).nativeRows = Extraction.SourceDimensions.Binary.rowCount := rfl

theorem actual_cell_count : (NativeTraceCells.profile .binary).unpackedWords = 39 := rfl

def ofCells (v : Vector FGL 39) : BinaryRow FGL :=
  ⟨⟨v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]⟩,
   ⟨v[9], v[10], v[11], v[12], v[13], v[14], v[15], v[16]⟩,
   ⟨v[17], v[18], v[19], v[20], v[21], v[22], v[23], v[24]⟩,
   ⟨v[25], v[26], v[27], v[28], v[29], v[30], v[31], v[32], v[0], v[37]⟩,
   ⟨v[33], v[34], v[35], v[36], v[38]⟩⟩

def cells (row : BinaryRow FGL) : Vector FGL 39 :=
  #v[row.chain.b_op,
    row.aBytes.free_in_a_0, row.aBytes.free_in_a_1, row.aBytes.free_in_a_2,
    row.aBytes.free_in_a_3, row.aBytes.free_in_a_4, row.aBytes.free_in_a_5,
    row.aBytes.free_in_a_6, row.aBytes.free_in_a_7,
    row.bBytes.free_in_b_0, row.bBytes.free_in_b_1, row.bBytes.free_in_b_2,
    row.bBytes.free_in_b_3, row.bBytes.free_in_b_4, row.bBytes.free_in_b_5,
    row.bBytes.free_in_b_6, row.bBytes.free_in_b_7,
    row.cBytes.free_in_c_0, row.cBytes.free_in_c_1, row.cBytes.free_in_c_2,
    row.cBytes.free_in_c_3, row.cBytes.free_in_c_4, row.cBytes.free_in_c_5,
    row.cBytes.free_in_c_6, row.cBytes.free_in_c_7,
    row.chain.carry_0, row.chain.carry_1, row.chain.carry_2, row.chain.carry_3,
    row.chain.carry_4, row.chain.carry_5, row.chain.carry_6, row.chain.carry_7,
    row.mode.mode32, row.mode.result_is_a, row.mode.use_first_byte,
    row.mode.c_is_signed, row.chain.b_op_or_sext, row.mode.mode32_and_c_is_signed]

theorem ofCells_cells (row : BinaryRow FGL) : ofCells (cells row) = row := by
  rcases row with ⟨a, b, c, chain, mode⟩
  cases a; cases b; cases c; cases chain; cases mode
  rfl

theorem cells_ofCells (values : Vector FGL 39) : cells (ofCells values) = values := by
  apply Vector.ext
  intro index bound
  interval_cases index <;> rfl

/-- Every observer of the existing Clean row is fixed, not merely its OpBus
message or selected table slots. There is no hidden unrepresented gauge. -/
theorem all_observers {α : Sort*} (observer : BinaryRow FGL → α)
    (first second : BinaryRow FGL) (h : cells first = cells second) :
    observer first = observer second := by
  have heq := congrArg ofCells h
  simpa only [ofCells_cells] using congrArg observer heq

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

/-- The existing native row-zero constructor checks the entire physical buffer
coverage and source profile once. Its actual checks imply each full FinN row;
no universal getter-success or height promise is requested from a caller. -/
private theorem base_at (anchor : NativeTraceCells.Row .binary resolved false 0)
    (index : Index) :
    NativeTraceCells.rowBase? .binary resolved false index.val =
      some (index.val * resolved.slotData.metadata.nColsTrace) := by
  have hbase := anchor.selected
  unfold NativeTraceCells.rowBase? at hbase ⊢
  cases hs : resolved.setup? with
  | none => simp [hs] at hbase
  | some setup =>
    cases hc : setup.mapSectionsN["cm1"]? with
    | none => simp [hs, hc] at hbase
    | some cm1 =>
      simp only [hs] at hbase ⊢
      dsimp only [Bind.bind, Option.bind] at hbase ⊢
      simp only [hc] at hbase ⊢
      split at hbase
      · rename_i hprofile
        rcases hprofile with ⟨ready, group, air, verify, gpu, count, _, width,
          stride, positive, coverage⟩
        have bound : index.val < setup.rowCount := by
          rw [count, actual_physical_capacity]
          exact index.isLt
        rw [if_pos ⟨ready, group, air, verify, gpu, count, bound, width,
          stride, positive, coverage⟩]
      · simp at hbase

def nativeAt (anchor : NativeTraceCells.Row .binary resolved false 0)
    (index : Index) : NativeTraceCells.Row .binary resolved false index.val :=
  ⟨index.val * resolved.slotData.metadata.nColsTrace, base_at anchor index⟩

theorem native_getter_total (anchor : NativeTraceCells.Row .binary resolved false 0)
    (index : Index) :
    NativeTraceCells.row? .binary resolved false index.val = some (nativeAt anchor index) :=
  (nativeAt anchor index).constructor_recovers

/-- Only this requested finite row is decoded; no entire trace is mapped. -/
def row? (anchor : NativeTraceCells.Row .binary resolved false 0) (index : Index) :
    Option (BinaryRow FGL) :=
  (nativeAt anchor index).values?.map ofCells

theorem rows_total (anchor : NativeTraceCells.Row .binary resolved false 0) (index : Index) :
    ∃ row, row? anchor index = some row := by
  obtain ⟨values, hv⟩ := (nativeAt anchor index).values_defined
  exact ⟨ofCells values, by simp [row?, hv]⟩

theorem all_source_coordinates (anchor : NativeTraceCells.Row .binary resolved false 0)
    (index : Index) (row : BinaryRow FGL) (h : row? anchor index = some row)
    (column : Fin 39) :
    NativeTraceCells.cell? .binary resolved false index.val column.val =
      some (cells row)[column.val] := by
  unfold row? at h
  cases hv : (nativeAt anchor index).values? with
  | none => simp [hv] at h
  | some values =>
    have heq : ofCells values = row := by simpa [hv] using h
    subst row
    rw [cells_ofCells]
    exact (nativeAt anchor index).values_coordinates values hv column

end ZiskFv.AirsClean.BinaryNativeRows
