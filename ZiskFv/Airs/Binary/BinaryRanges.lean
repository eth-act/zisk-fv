import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Binary.Binary

/-!
# Residual Binary W-mode trusted facts

T7 retires the range-bus source dependency from this module. The remaining
facts are existing W-mode Binary-table trust-ledger axioms; they are not
derived from `range_bus_sound`.
-/

namespace ZiskFv.Airs.Binary

open Goldilocks

/-- Existing W-mode sign-extension trust boundary for ADDW/SUBW/ADDIW. -/
axiom binary_w_sext_choice_pin
    (v : Valid_Binary FGL FGL) (r : ℕ) (op_emit : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = (op_emit : FGL))
    (h_op_w : op_emit = 0x1A ∨ op_emit = 0x1B) :
    (((v.free_in_c_4 r).val = 0 ∧ (v.free_in_c_5 r).val = 0
        ∧ (v.free_in_c_6 r).val = 0 ∧ (v.free_in_c_7 r).val = 0) ∧
      (v.free_in_c_0 r).val + (v.free_in_c_1 r).val * 256
        + (v.free_in_c_2 r).val * 65536
        + (v.free_in_c_3 r).val * 16777216 < 2147483648)
    ∨ (((v.free_in_c_4 r).val = 255 ∧ (v.free_in_c_5 r).val = 255
        ∧ (v.free_in_c_6 r).val = 255 ∧ (v.free_in_c_7 r).val = 255) ∧
      (v.free_in_c_0 r).val + (v.free_in_c_1 r).val * 256
        + (v.free_in_c_2 r).val * 65536
        + (v.free_in_c_3 r).val * 16777216 ≥ 2147483648)

/-- Existing W-mode carry-chain trust boundary paired with
    `binary_w_sext_choice_pin`. -/
axiom binary_w_mode_carry_7_zero
    (v : Valid_Binary FGL FGL) (r : ℕ) (op_emit : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = (op_emit : FGL))
    (h_op_w : op_emit = 0x1A ∨ op_emit = 0x1B) :
    v.carry_7 r = 0

end ZiskFv.Airs.Binary
