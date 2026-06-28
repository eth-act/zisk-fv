import RvCompleteness

open Aeneas Aeneas.Std Result
open zisk_core

namespace allhelpers

/-! ===== setWidth family: numBits case-split then rw then decide ===== -/

theorem one_u64_scalar_not_lt_regs_from_set_width :
    ¬ ((1#64#uscalar : Std.U64) <
      (BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem regs_to_set_width_not_lt_one_u64_scalar :
    ¬ ((BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) <
      (1#64#uscalar : Std.U64)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem one_i64_scalar_not_lt_regs_from_set_width :
    ¬ ((1#64#iscalar : Std.I64) <
      (BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem regs_to_set_width_not_lt_one_i64_scalar :
    ¬ ((BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) <
      (1#64#iscalar : Std.I64)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem one_u64_val_not_lt_regs_from_set_width :
    ¬ ((↑(1#64#uscalar : Std.U64) : Nat) <
      (↑(BitVec.setWidth 64 1#System.Platform.numBits#uscalar : Std.U64) : Nat)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem regs_to_set_width_val_not_lt_one_u64 :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#uscalar : Std.U64) : Nat) <
      (↑(1#64#uscalar : Std.U64) : Nat)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem one_i64_val_not_lt_regs_from_set_width :
    ¬ ((↑(1#64#iscalar : Std.I64) : Int) <
      (↑(BitVec.setWidth 64 1#System.Platform.numBits#iscalar : Std.I64) : Int)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

theorem regs_to_set_width_val_not_lt_one_i64 :
    ¬ ((↑(BitVec.setWidth 64 31#System.Platform.numBits#iscalar : Std.I64) : Int) <
      (↑(1#64#iscalar : Std.I64) : Int)) := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

/-! ===== fixed-width literal facts: plain decide ===== -/

theorem one_u64_scalar_ne_zero : ¬ ((1#64#uscalar : Std.U64) = 0#u64) := by decide
theorem one_i64_scalar_ne_zero : ¬ ((1#64#iscalar : Std.I64) = 0#i64) := by decide
theorem i64_zero_eq_zero : (0#64#iscalar : Std.I64) = 0#i64 := by decide
theorem i32_32_nonnegative : (32#i32 : Std.I32).val ≥ 0 := by decide
theorem i32_32_toNat_lt_u64_numBits :
    (32#i32 : Std.I32).toNat < UScalarTy.U64.numBits := by decide

/-! ===== shift helper: uses i32_32 facts (no native_decide) ===== -/

theorem uscalar64_shift_right_i32_32_ok_true (x : Std.U64) :
    (do
      let _ ← x >>> 32#i32
      ok true) = ok true := by
  simp only [HShiftRight.hShiftRight,
    UScalar.shiftRight_IScalar, UScalar.shiftRight,
    i32_32_nonnegative, i32_32_toNat_lt_u64_numBits,
    Bind.bind, Std.bind, ↓reduceIte]

/-! ===== usize cast/hcast variants (REGS_IN_MAIN_FROM/TO are Usize = numBits-wide) ===== -/

theorem one_u64_ne_zero : ¬ ((1#u64 : Std.U64) = 0#u64) := by decide
theorem one_i64_ne_zero : ¬ ((1#i64 : Std.I64) = 0#i64) := by decide

theorem one_u64_not_lt_regs_from :
    ¬ ((1#u64 : Std.U64) < (UScalar.cast .U64 zisk_registers.REGS_IN_MAIN_FROM)) := by
  unfold zisk_registers.REGS_IN_MAIN_FROM
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalar.cast, h] <;> decide

theorem one_i64_not_lt_regs_from :
    ¬ ((1#i64 : Std.I64) < (UScalar.hcast .I64 zisk_registers.REGS_IN_MAIN_FROM)) := by
  unfold zisk_registers.REGS_IN_MAIN_FROM
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalar.hcast, h] <;> decide

theorem regs_to_not_lt_one_u64 :
    ¬ ((UScalar.cast .U64 zisk_registers.REGS_IN_MAIN_TO) < (1#u64 : Std.U64)) := by
  unfold zisk_registers.REGS_IN_MAIN_TO
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalar.cast, h] <;> decide

theorem regs_to_not_lt_one_i64 :
    ¬ ((UScalar.hcast .I64 zisk_registers.REGS_IN_MAIN_TO) < (1#i64 : Std.I64)) := by
  unfold zisk_registers.REGS_IN_MAIN_TO
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalar.hcast, h] <;> decide

#print axioms one_u64_scalar_not_lt_regs_from_set_width
#print axioms regs_to_set_width_val_not_lt_one_u64
#print axioms one_i64_val_not_lt_regs_from_set_width
#print axioms regs_to_set_width_val_not_lt_one_i64
#print axioms i32_32_nonnegative
#print axioms i32_32_toNat_lt_u64_numBits
#print axioms uscalar64_shift_right_i32_32_ok_true
#print axioms one_u64_not_lt_regs_from
#print axioms one_i64_not_lt_regs_from
#print axioms regs_to_not_lt_one_i64

end allhelpers
