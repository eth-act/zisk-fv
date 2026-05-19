import ZiskFv.AirsClean.MemAlignByte.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlignByte Soundness

The Spec follows directly from PIL constraints 3, 5, 6, 7, 8 via
linear_combination. No carry-chain or range reasoning needed —
these constraints have the same shape as their Spec components
modulo `linear_combination` reshuffling.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks

theorem soundness (row : MemAlignByteRow FGL)
    (_h_assumptions : Assumptions row)
    (h_composed :
      row.composed_value
        - (row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b) = 0)
    (h_written_composed :
      row.written_composed_value
        - (row.written_byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b) = 0)
    (h_mem_0 :
      row.mem_write_values_0
        - (row.sel_high_4b * (row.direct_value - row.written_composed_value)
            + row.written_composed_value) = 0)
    (h_mem_1 :
      row.mem_write_values_1
        - (row.sel_high_4b * (row.written_composed_value - row.direct_value)
            + row.direct_value) = 0)
    (h_bus_byte :
      row.bus_byte
        - (row.is_write * (row.written_byte_value - row.byte_value) + row.byte_value) = 0) :
    Spec row := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h_composed
  · linear_combination h_written_composed
  · linear_combination h_mem_0
  · linear_combination h_mem_1
  · linear_combination h_bus_byte

end ZiskFv.AirsClean.MemAlignByte
