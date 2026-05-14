import Mathlib

import ZiskFv.Equivalence.BranchLessThan
import ZiskFv.Sail.blt
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main

/-!
# `equiv_BLT` Compliance wrapper — ControlFlow branches (Step 4.2)

Within-shape companion to `FromTrust/Beq.lean`. The pure-spec
`throws`/`fails`/`success` shape on BLT is structurally identical to
BEQ; the signed-comparison decision affects only `taken` and hence
`nextPC` (carried by `h_nextPC_matches`). The alignment-implies-no-
exception discharge is opcode-agnostic.

Zero new axioms. Signed comparison sign-witness pins, when required
by a Binary-flag-correctness discharge of `h_nextPC_matches`, would
live in `Bridge/ControlFlow.lean` (not added here per the
discharge-recipe — `h_nextPC_matches` is passed through as a
structural bus pin).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

private theorem blt_pure_no_exception_of_aligned
    (input : PureSpec.BltInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BLT_pure input).throws = false
    ∧ (PureSpec.execute_BLT_pure input).success = true := by
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
  · simp [PureSpec.execute_BLT_pure, ← h_t, h_bit0]
  · simp [PureSpec.execute_BLT_pure, ← h_t, h_bit0, h_bit1]

/-- **Compliance wrapper for `equiv_BLT`.** -/
theorem equiv_BLT_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok blt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok blt_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (blt_input.PC + BitVec.signExtend 64 blt_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) state
      = (bus_effect exec_row [] state).2 := by
  obtain ⟨h_not_throws, h_success⟩ :=
    blt_pure_no_exception_of_aligned blt_input h_target_aligned
  exact ZiskFv.Equivalence.BranchLessThan.equiv_BLT
    state blt_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_not_throws h_success

end ZiskFv.Compliance
