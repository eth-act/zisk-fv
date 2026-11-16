import ZiskFv.AirsClean.ByteMemoryLogicalRows
import ZiskFv.AirsClean.ByteMemoryTraceProfiles
import ZiskFv.AirsClean.NativeTraceCells

/-!
INTERNAL lazy Byte/Read projection from the SAME checked physical
source descriptor. Each call decodes at most one finite row through the sole
shared NativeTraceCells decoder; no physical-N list, map, crop or matrix is
constructed. Missing/unsupported source data remains None, never native0.
The complete native-coordinate inverse laws account for EVERY existing Clean
row field; there is no hidden auxiliary gauge in these two row types.
No existing Component/Table/Environment/Accepted/Root interface is changed.
-/
namespace ZiskFv.AirsClean.ByteMemorySourceProjection

open Goldilocks
open ByteMemoryPhysicalRows ByteMemoryLogicalRows
open ZiskFv.AirsClean
open ZiskFv.AirsClean.MemAlignWriteByte.RawSource.Native

variable {source : SourceObject FGL} {resolved : ResolvedOccurrence source}

def byte? (physical : Rows resolved) (index : physical.Index) : Option (MemAlignByte.MemAlignByteRow FGL) := do
  if physical.air = .byte then
    let native ← NativeTraceCells.row? .byte resolved false index.val
    let values ← native.values?
    return byteOfCells values
  else none

def read? (physical : Rows resolved) (index : physical.Index) : Option (MemAlignReadByte.MemAlignReadByteRow FGL) := do
  if physical.air = .readByte then
    let native ← NativeTraceCells.row? .readByte resolved false index.val
    let values ← native.values?
    return readOfCells values
  else none

theorem byte_projection_defined (physical : Rows resolved) (index : physical.Index)
    (hair : physical.air = .byte)
    (native : NativeTraceCells.Row .byte resolved false index.val) :
    ∃ row, byte? physical index = some row := by
  obtain ⟨values, hv⟩ := native.values_defined
  exact ⟨byteOfCells values, by
    simp [byte?, hair, native.constructor_recovers, hv]⟩

theorem read_projection_defined (physical : Rows resolved) (index : physical.Index)
    (hair : physical.air = .readByte)
    (native : NativeTraceCells.Row .readByte resolved false index.val) :
    ∃ row, read? physical index = some row := by
  obtain ⟨values, hv⟩ := native.values_defined
  exact ⟨readOfCells values, by
    simp [read?, hair, native.constructor_recovers, hv]⟩

theorem byte_all_source_coordinates (physical : Rows resolved) (index : physical.Index)
    (row : MemAlignByte.MemAlignByteRow FGL) (h : byte? physical index = some row) (column : Fin 16) :
    NativeTraceCells.cell? .byte resolved false index.val column.val =
      some (byteCells row)[column.val] := by
  unfold byte? at h
  split at h
  · cases hn : NativeTraceCells.row? .byte resolved false index.val with
    | none => simp [hn] at h
    | some native =>
      cases hv : native.values? with
      | none => simp [hn, hv] at h
      | some values =>
        have heq : byteOfCells values = row := by simpa [hn, hv] using h
        subst row
        rw [byteCells_byteOfCells]
        exact native.values_coordinates values hv column
  · simp at h

theorem read_all_source_coordinates (physical : Rows resolved) (index : physical.Index)
    (row : MemAlignReadByte.MemAlignReadByteRow FGL) (h : read? physical index = some row) (column : Fin 10) :
    NativeTraceCells.cell? .readByte resolved false index.val column.val =
      some (readCells row)[column.val] := by
  unfold read? at h
  split at h
  · cases hn : NativeTraceCells.row? .readByte resolved false index.val with
    | none => simp [hn] at h
    | some native =>
      cases hv : native.values? with
      | none => simp [hn, hv] at h
      | some values =>
        have heq : readOfCells values = row := by simpa [hn, hv] using h
        subst row
        rw [readCells_readOfCells]
        exact native.values_coordinates values hv column
  · simp at h

/-- Exact row determination is stronger than selecting a few messages. ANY
existing circuit/operation/message/write observer agrees, with no gauge choice. -/
theorem byte_projection_all_observers {α : Sort*} (physical : Rows resolved)
    (index : physical.Index) (first second : MemAlignByte.MemAlignByteRow FGL)
    (hfirst : byte? physical index = some first) (hsecond : byte? physical index = some second)
    (observer : MemAlignByte.MemAlignByteRow FGL → α) : observer first = observer second := by
  have heq : first = second := Option.some.inj (hfirst.symm.trans hsecond)
  exact congrArg observer heq

theorem read_projection_all_observers {α : Sort*} (physical : Rows resolved)
    (index : physical.Index) (first second : MemAlignReadByte.MemAlignReadByteRow FGL)
    (hfirst : read? physical index = some first) (hsecond : read? physical index = some second)
    (observer : MemAlignReadByte.MemAlignReadByteRow FGL → α) : observer first = observer second := by
  have heq : first = second := Option.some.inj (hfirst.symm.trans hsecond)
  exact congrArg observer heq

end ZiskFv.AirsClean.ByteMemorySourceProjection
