import ZiskFv.AirsClean.ByteMemoryPhysicalRows
import ZiskFv.AirsClean.MemAlignByte.Row
import ZiskFv.AirsClean.MemAlignReadByte.Row

/-!
INTERNAL finite-row representation only. Native ordinal order is retained
explicitly, including every source array element. No gauge or
invented zero fills a missing field. The inverse laws establish that these
two current Clean rows have NO additional unrepresented scalar coordinate.
No entire physical trace is allocated or transported to an old Table list.
-/
namespace ZiskFv.AirsClean.ByteMemoryLogicalRows

open Goldilocks
open ZiskFv.AirsClean.MemAlignByte
open ZiskFv.AirsClean.MemAlignReadByte

def byteOfCells (cells : Vector FGL 16) : MemAlignByteRow FGL :=
  ⟨cells[0], cells[1], cells[2], cells[3], cells[4], cells[5], cells[6], cells[7],
   cells[8], cells[9], cells[10], cells[11], cells[12], cells[13], cells[14], cells[15]⟩

def byteCells (row : MemAlignByteRow FGL) : Vector FGL 16 :=
  #v[row.sel_high_4b, row.sel_high_2b, row.sel_high_b, row.direct_value,
    row.composed_value, row.written_composed_value, row.written_byte_value,
    row.value_16b, row.value_8b, row.byte_value, row.addr_w, row.step, row.is_write,
    row.mem_write_values_0, row.mem_write_values_1, row.bus_byte]

theorem byteOfCells_byteCells (row : MemAlignByteRow FGL) :
    byteOfCells (byteCells row) = row := by
  cases row
  rfl

theorem byteCells_byteOfCells (cells : Vector FGL 16) :
    byteCells (byteOfCells cells) = cells := by
  apply Vector.ext
  intro index bound
  interval_cases index <;> rfl

def readOfCells (cells : Vector FGL 10) : MemAlignReadByteRow FGL :=
  ⟨cells[0], cells[1], cells[2], cells[3], cells[4], cells[5], cells[6], cells[7], cells[8], cells[9]⟩

def readCells (row : MemAlignReadByteRow FGL) : Vector FGL 10 :=
  #v[row.sel_high_4b, row.sel_high_2b, row.sel_high_b, row.direct_value,
    row.composed_value, row.value_16b, row.value_8b, row.byte_value, row.addr_w, row.step]

theorem readOfCells_readCells (row : MemAlignReadByteRow FGL) :
    readOfCells (readCells row) = row := by
  cases row
  rfl

theorem readCells_readOfCells (cells : Vector FGL 10) :
    readCells (readOfCells cells) = cells := by
  apply Vector.ext
  intro index bound
  interval_cases index <;> rfl

/-- No auxiliary gauge survives the complete native-coordinate inventory.
Consequently ANY circuit/operation/message/write observer is determined, not
merely one selected message. No relevant observer is silently omitted. -/
theorem byte_all_observers {α : Sort*} (observer : MemAlignByteRow FGL → α)
    (first second : MemAlignByteRow FGL) (h : byteCells first = byteCells second) :
    observer first = observer second := by
  have heq := congrArg byteOfCells h
  simpa only [byteOfCells_byteCells] using congrArg observer heq

theorem read_all_observers {α : Sort*} (observer : MemAlignReadByteRow FGL → α)
    (first second : MemAlignReadByteRow FGL) (h : readCells first = readCells second) :
    observer first = observer second := by
  have heq := congrArg readOfCells h
  simpa only [readOfCells_readCells] using congrArg observer heq

end ZiskFv.AirsClean.ByteMemoryLogicalRows
