import ZiskFv.AirsClean.MemAlignByte.Soundness
import ZiskFv.Airs.MemAlignByte

/-!
# `Valid_MemAlignByte` ↔ `MemAlignByteRow` compatibility

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignByte

open Goldilocks


@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ)
    : MemAlignByteRow FGL where
  sel_high_4b := v.sel_high_4b r
  sel_high_2b := v.sel_high_2b r
  sel_high_b := v.sel_high_b r
  direct_value := v.direct_value r
  composed_value := v.composed_value r
  written_composed_value := v.written_composed_value r
  written_byte_value := v.written_byte_value r
  value_16b := v.value_16b r
  value_8b := v.value_8b r
  byte_value := v.byte_value r
  addr_w := v.addr_w r
  step := v.step r
  is_write := v.is_write r
  mem_write_values_0 := v.mem_write_values_0 r
  mem_write_values_1 := v.mem_write_values_1 r
  bus_byte := v.bus_byte r

/-- The 9 F-typed MemAlignByte row constraints at row `r`, expressed
    against a `Valid_MemAlignByte`. The 5 definitional identities (4,
    6, 7, 8, 9) are what `soundness` consumes; the 4 booleans (1, 2,
    3, 5) live in `Assumptions`. -/
def constraints_at
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ) : Prop :=
  v.composed_value r - (v.byte_value r
      * byte_value_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_8b r * value_8b_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_16b r * value_16b_factor (v.sel_high_2b r)) = 0
  ∧ v.written_composed_value r - (v.written_byte_value r
      * byte_value_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_8b r * value_8b_factor (v.sel_high_2b r) (v.sel_high_b r)
    + v.value_16b r * value_16b_factor (v.sel_high_2b r)) = 0
  ∧ v.mem_write_values_0 r
      - (v.sel_high_4b r * (v.direct_value r - v.written_composed_value r)
         + v.written_composed_value r) = 0
  ∧ v.mem_write_values_1 r
      - (v.sel_high_4b r * (v.written_composed_value r - v.direct_value r)
         + v.direct_value r) = 0
  ∧ v.bus_byte r
      - (v.is_write r * (v.written_byte_value r - v.byte_value r)
         + v.byte_value r) = 0

/-- **Bridge theorem.** -/
theorem spec_of_valid
    (v : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h_c, h_wc, h_m0, h_m1, h_bb⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h_c h_wc h_m0 h_m1 h_bb

end ZiskFv.AirsClean.MemAlignByte
