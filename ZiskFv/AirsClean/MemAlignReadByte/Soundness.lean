import ZiskFv.AirsClean.MemAlignReadByte.Spec
import Mathlib.Tactic.LinearCombination

/-!
# MemAlignReadByte Soundness

The Spec (composed_value relation) follows directly from PIL
constraint 3 (`composed_value - (byte_value * b_factor + value_8b *
v8_factor + value_16b * v16_factor) = 0`). No range-discharge or
carry-chain reasoning is needed — the constraint *is* the Spec
modulo `linear_combination` reshuffling.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

/-- Row-level soundness: the per-byte recombination constraint
    implies the Spec. The boolean assumptions on the selectors are
    not needed for this implication — they constrain *which* byte
    is read but the equation holds for any selector values. -/
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
        = 0) :
    Spec row := by
  simp only [Spec]
  linear_combination h_composed

end ZiskFv.AirsClean.MemAlignReadByte
