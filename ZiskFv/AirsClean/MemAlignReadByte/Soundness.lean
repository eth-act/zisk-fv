import ZiskFv.AirsClean.MemAlignReadByte.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlignReadByte Soundness

The algebraic `Spec` clause (the `composed_value` relation) follows
directly from PIL constraint 3 (`composed_value - (byte_value *
b_factor + value_8b * v8_factor + value_16b * v16_factor) = 0`) via
`linear_combination` — no carry-chain reasoning; the constraint *is*
the Spec clause modulo `linear_combination` reshuffling. The `bits(8)`
range clause is supplied to `soundness_of_ranges` as an explicit
hypothesis — the Clean Component's `soundness` field draws it from
`range_bus_sound` (the range-checker bus, plan F-4).

## Trust note

No axioms. This file proves the Spec from the definitional
`composed_value` constraint plus the declared `bits(8)` range bound.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

/-- MemAlignReadByte row soundness from the definitional
    `composed_value` constraint plus the `byte_value` `bits(8)` range
    bound. The definitional constraint discharges the algebraic clause;
    the range bound passes straight through.

    This is the form the Clean `Component`'s `soundness` field
    consumes — the range bound arrives from `range_bus_sound` (the
    range-checker bus), so the Component's `Assumptions` can be `True`
    (plan D-2 / F-4). The three boolean selector constraints are
    unused. -/
theorem soundness_of_ranges (row : MemAlignReadByteRow FGL)
    (h_composed :
      row.composed_value
        - (row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b)
        = 0)
    (h_byte_value_range : row.byte_value.val < 2 ^ 8) :
    Spec row := by
  refine ⟨?_, h_byte_value_range⟩
  linear_combination h_composed

/-- Row-level soundness: the definitional `composed_value` constraint +
    the `bits(8)` range bound (here as explicit hypotheses) imply the
    Spec. Thin wrapper over `soundness_of_ranges`; the boolean
    `Assumptions` and selector-boolean conjuncts are unused — they
    constrain *which* byte is read but the equation holds for any
    selector values. -/
theorem soundness (row : MemAlignReadByteRow FGL)
    (_h_assumptions : Assumptions row)
    (_h_bool_4b : row.sel_high_4b * (1 - row.sel_high_4b) = 0)
    (_h_bool_2b : row.sel_high_2b * (1 - row.sel_high_2b) = 0)
    (_h_bool_b : row.sel_high_b * (1 - row.sel_high_b) = 0)
    (h_composed :
      row.composed_value
        - (row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
            + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
            + row.value_16b * value_16b_factor row.sel_high_2b)
        = 0)
    (h_byte_value_range : row.byte_value.val < 2 ^ 8) :
    Spec row :=
  soundness_of_ranges row h_composed h_byte_value_range

end ZiskFv.AirsClean.MemAlignReadByte
