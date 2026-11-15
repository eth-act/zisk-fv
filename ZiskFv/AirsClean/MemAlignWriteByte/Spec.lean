import ZiskFv.AirsClean.MemAlignWriteByte.Row
import ZiskFv.AirsClean.MemAlignByte.Spec

namespace ZiskFv.AirsClean.MemAlignWriteByte

open Goldilocks
open ZiskFv.AirsClean.MemAlignByte (byte_value_factor value_8b_factor value_16b_factor)

/-- Exactly the seven F-only source equations, including all three selectors. -/
def PolynomialSpec (row : MemAlignWriteByteRow FGL) : Prop :=
  row.sel_high_4b * (1 - row.sel_high_4b) = 0 ∧
  row.sel_high_2b * (1 - row.sel_high_2b) = 0 ∧
  row.sel_high_b * (1 - row.sel_high_b) = 0 ∧
  row.composed_value =
    row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b +
    row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b +
    row.value_16b * value_16b_factor row.sel_high_2b ∧
  row.written_composed_value =
    row.written_byte_value * byte_value_factor row.sel_high_2b row.sel_high_b +
    row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b +
    row.value_16b * value_16b_factor row.sel_high_2b ∧
  row.mem_write_values_0 =
    row.sel_high_4b * (row.direct_value - row.written_composed_value) +
      row.written_composed_value ∧
  row.mem_write_values_1 =
    row.sel_high_4b * (row.written_composed_value - row.direct_value) + row.direct_value

/-- Only actual lookups, not the unenforced `bits` witness annotations:
written byte uses source bus107, value16 bus103, and the pair bus88. -/
def RangeSpec (row : MemAlignWriteByteRow FGL) : Prop :=
  row.written_byte_value.val < 256 ∧ row.value_16b.val < 65536 ∧
  row.byte_value.val < 256 ∧ row.value_8b.val < 256

def Spec (row : MemAlignWriteByteRow FGL) : Prop :=
  PolynomialSpec row ∧ RangeSpec row

end ZiskFv.AirsClean.MemAlignWriteByte
