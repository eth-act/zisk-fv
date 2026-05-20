import ZiskFv.AirsClean.MemAlignReadByte.Soundness
import ZiskFv.Airs.MemAlignReadByte

/-!
# `Valid_MemAlignReadByte` ↔ `MemAlignReadByteRow` compatibility

Connects the existing `Valid_MemAlignReadByte` interface to the
Clean Component's row type.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks


/-- Project a `Valid_MemAlignReadByte` at row `r` into a Clean
    `MemAlignReadByteRow FGL`. -/
@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ)
    : MemAlignReadByteRow FGL where
  sel_high_4b := v.sel_high_4b r
  sel_high_2b := v.sel_high_2b r
  sel_high_b := v.sel_high_b r
  direct_value := v.direct_value r
  composed_value := v.composed_value r
  value_16b := v.value_16b r
  value_8b := v.value_8b r
  byte_value := v.byte_value r
  addr_w := v.addr_w r
  step := v.step r

/-- The 4 F-typed MemAlignReadByte row constraints at row `r`,
    expressed against a `Valid_MemAlignReadByte`. -/
def constraints_at
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ) : Prop :=
  v.sel_high_4b r * (1 - v.sel_high_4b r) = 0
  ∧ v.sel_high_2b r * (1 - v.sel_high_2b r) = 0
  ∧ v.sel_high_b r * (1 - v.sel_high_b r) = 0
  ∧ v.composed_value r - (v.byte_value r
        * byte_value_factor (v.sel_high_2b r) (v.sel_high_b r)
      + v.value_8b r * value_8b_factor (v.sel_high_2b r) (v.sel_high_b r)
      + v.value_16b r * value_16b_factor (v.sel_high_2b r)) = 0

/-- **Bridge theorem.** Given a row of a `Valid_MemAlignReadByte`
    satisfying the 4 Clean Component constraints + the boolean
    assumptions, the MemAlignReadByte Spec holds. -/
theorem spec_of_valid
    (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL) (r : ℕ)
    (h_assumptions : Assumptions (rowAt v r))
    (h_constraints : constraints_at v r) :
    Spec (rowAt v r) := by
  obtain ⟨h_4b, h_2b, h_b, h_composed⟩ := h_constraints
  exact soundness (rowAt v r) h_assumptions h_4b h_2b h_b h_composed

end ZiskFv.AirsClean.MemAlignReadByte
