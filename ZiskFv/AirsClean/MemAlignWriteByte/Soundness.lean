import ZiskFv.AirsClean.MemAlignWriteByte.Spec
import ZiskFv.AirsClean.CompletenessHelpers
import Mathlib.Tactic.LinearCombination

namespace ZiskFv.AirsClean.MemAlignWriteByte
open Goldilocks
open ZiskFv.AirsClean.MemAlignByte (byte_value_factor value_8b_factor value_16b_factor)

/-- The nonselected 8-bit and 16-bit pieces cancel: the selected 32-bit limb
changes by exactly the written-minus-read byte at its selected power of 256. -/
theorem replacement_delta (row : MemAlignWriteByteRow FGL) (h : PolynomialSpec row) :
    row.written_composed_value - row.composed_value =
      (row.written_byte_value - row.byte_value) *
        byte_value_factor row.sel_high_2b row.sel_high_b := by
  obtain ⟨_, _, _, hc, hw, _, _⟩ := h
  linear_combination hw - hc

/-- All four positions within either limb; the high-limb selector is independent.
Combined with `write_lanes`, this covers every byte offset 0--7. -/
theorem byte_factor_routes (high2 high1 : Bool) :
    byte_value_factor (boolF high2) (boolF high1) =
      (256 : FGL) ^ ((if high2 then 2 else 0) + (if high1 then 1 else 0)) := by
  cases high2 <;> cases high1 <;> norm_num [boolF, byte_value_factor]

/-- A write changes exactly the selected 32-bit limb and preserves the other
limb. No address/step or direct-limb range assertion absent from PIL is added. -/
theorem write_lanes (row : MemAlignWriteByteRow FGL) (high4 : Bool)
    (hsel : row.sel_high_4b = boolF high4) (h : PolynomialSpec row) :
    row.mem_write_values_0 = (if high4 then row.direct_value else row.written_composed_value) ∧
    row.mem_write_values_1 = (if high4 then row.written_composed_value else row.direct_value) := by
  obtain ⟨_, _, _, _, _, h0, h1⟩ := h
  cases high4 <;> simp_all [boolF]

/-- Selector classification is proved from the three source equations, not
required as an extra byte-route validator. -/
theorem selectors_boolean (row : MemAlignWriteByteRow FGL) (h : PolynomialSpec row) :
    ∃ high4 high2 high1 : Bool,
      row.sel_high_4b = boolF high4 ∧ row.sel_high_2b = boolF high2 ∧
      row.sel_high_b = boolF high1 := by
  have boolean (x : FGL) (hx : x * (1 - x) = 0) :
      ∃ b : Bool, x = boolF b := by
    rcases mul_eq_zero.mp hx with hzero | hone
    · exact ⟨false, by simpa [boolF] using hzero⟩
    · refine ⟨true, ?_⟩
      simp only [boolF]
      linear_combination -hone
  obtain ⟨high4, h4⟩ := boolean _ h.1
  obtain ⟨high2, h2⟩ := boolean _ h.2.1
  obtain ⟨high1, h1⟩ := boolean _ h.2.2.1
  exact ⟨high4, high2, high1, h4, h2, h1⟩

/-- Every source-valid row belongs to one of the eight actual byte routes. -/
theorem write_routes_exhaustive (row : MemAlignWriteByteRow FGL) (h : PolynomialSpec row) :
    ∃ high4 high2 high1 : Bool,
      row.sel_high_4b = boolF high4 ∧ row.sel_high_2b = boolF high2 ∧
      row.sel_high_b = boolF high1 ∧
      row.written_composed_value - row.composed_value =
        (row.written_byte_value - row.byte_value) *
          (256 : FGL) ^ ((if high2 then 2 else 0) + (if high1 then 1 else 0)) ∧
      row.mem_write_values_0 = (if high4 then row.direct_value else row.written_composed_value) ∧
      row.mem_write_values_1 = (if high4 then row.written_composed_value else row.direct_value) := by
  obtain ⟨high4, high2, high1, h4, h2, h1⟩ := selectors_boolean row h
  refine ⟨high4, high2, high1, h4, h2, h1, ?_, write_lanes row high4 h4 h⟩
  rw [replacement_delta row h, h2, h1, byte_factor_routes]

end ZiskFv.AirsClean.MemAlignWriteByte
