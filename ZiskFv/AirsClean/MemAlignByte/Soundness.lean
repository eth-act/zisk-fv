import ZiskFv.AirsClean.MemAlignByte.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlignByte Soundness

The 5 algebraic `Spec` clauses follow directly from PIL constraints
3, 5, 6, 7, 8 via `linear_combination` — no carry-chain or range
reasoning; these constraints have the same shape as their Spec
components modulo `linear_combination` reshuffling. The 3 `bits(N)`
range clauses are supplied to `soundness_of_ranges` as explicit
hypotheses — the Clean Component's `soundness` field now draws them from
concrete Clean static lookups emitted by `main`.

## Trust note

No axioms. This file proves the Spec from the 5 definitional
constraints plus the 3 declared `bits(N)` range bounds.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks

/-- MemAlignByte row soundness from the 5 definitional constraints
    plus the 3 byte/selector range bounds. The 5 definitional
    constraints (3, 5, 6, 7, 8) discharge the algebraic clauses; the
    range bounds pass straight through.

    This is the form the Clean `Component`'s `soundness` field
    consumes — the 3 range bounds arrive from static lookup soundness,
    so the Component's `Assumptions` can be `True`. The four boolean
    constraints (0, 1, 2, 4) are unused. -/
theorem soundness_of_ranges (row : MemAlignByteRow FGL)
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
        - (row.is_write * (row.written_byte_value - row.byte_value) + row.byte_value) = 0)
    (h_bus_byte_range : row.bus_byte.val < 2 ^ 8)
    (h_byte_value_range : row.byte_value.val < 2 ^ 8)
    (h_is_write_range : row.is_write.val < 2 ^ 1) :
    Spec row := by
  refine ⟨?_, ?_, ?_, ?_, ?_, h_bus_byte_range, h_byte_value_range, h_is_write_range⟩
  · linear_combination h_composed
  · linear_combination h_written_composed
  · linear_combination h_mem_0
  · linear_combination h_mem_1
  · linear_combination h_bus_byte

/-- MemAlignByte row soundness: the 5 definitional constraints + the
    3 range bounds (here as part of `Assumptions`) imply the Spec.
    Thin wrapper over `soundness_of_ranges`; the four boolean
    `Assumptions` conjuncts are unused. -/
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
        - (row.is_write * (row.written_byte_value - row.byte_value) + row.byte_value) = 0)
    (h_bus_byte_range : row.bus_byte.val < 2 ^ 8)
    (h_byte_value_range : row.byte_value.val < 2 ^ 8)
    (h_is_write_range : row.is_write.val < 2 ^ 1) :
    Spec row :=
  soundness_of_ranges row h_composed h_written_composed h_mem_0 h_mem_1 h_bus_byte
    h_bus_byte_range h_byte_value_range h_is_write_range

end ZiskFv.AirsClean.MemAlignByte
