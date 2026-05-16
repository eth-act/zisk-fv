import Mathlib

import ZiskFv.Equivalence.BranchLessThanUnsigned
import ZiskFv.SailSpec.bltu
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_BLTU` Compliance wrapper — ControlFlow branches

Within-shape companion to `FromTrust/Beq.lean`. Unsigned comparison;
zero new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

private theorem bltu_pure_no_exception_of_aligned
    (input : PureSpec.BltuInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BLTU_pure input).throws = false
    ∧ (PureSpec.execute_BLTU_pure input).success = true := by
  set t : BitVec 64 := input.PC + BitVec.signExtend 64 input.imm with h_t
  have h_bit0 : t[0] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero]
    have h_mod2 : t.toNat % 2 = 0 := by omega
    simp [h_mod2]
  have h_bit1 : t[1] = false := by
    rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_succ, Nat.testBit_zero]
    have h_div_mod : (t.toNat / 2) % 2 = 0 := by omega
    simp [h_div_mod]
  refine ⟨?_, ?_⟩
  · simp [PureSpec.execute_BLTU_pure, ← h_t, h_bit0]
  · simp [PureSpec.execute_BLTU_pure, ← h_t, h_bit0, h_bit1]

/-- **Compliance wrapper for `equiv_BLTU`.** -/
theorem equiv_BLTU_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2 := by
  obtain ⟨h_not_throws, h_success⟩ :=
    bltu_pure_no_exception_of_aligned bltu_input h_target_aligned
  exact ZiskFv.Equivalence.BranchLessThanUnsigned.equiv_BLTU
    state bltu_input imm r1 r2 misa_val exec_row
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }

end ZiskFv.Compliance
