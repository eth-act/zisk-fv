import Mathlib

import ZiskFv.Equivalence.BranchNotEqual
import ZiskFv.Sail.bne
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main

/-!
# `equiv_BNE` Compliance wrapper — ControlFlow branches (Step 4.2)

Within-shape companion to `FromTrust/Beq.lean`. The pure-spec
`throws` / `fails` / `success` formula on BNE is structurally
identical to BEQ (only the `taken` predicate flips polarity); the
alignment-implies-no-exception discharge is therefore opcode-agnostic.

Zero new axioms.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Alignment-implies-no-exception lemma for BNE.** Same proof
    structure as `beq_pure_no_exception_of_aligned`. -/
private theorem bne_pure_no_exception_of_aligned
    (input : PureSpec.BneInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BNE_pure input).throws = false
    ∧ (PureSpec.execute_BNE_pure input).success = true := by
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
  · simp [PureSpec.execute_BNE_pure, ← h_t, h_bit0]
  · simp [PureSpec.execute_BNE_pure, ← h_t, h_bit0, h_bit1]

/-- **Compliance wrapper for `equiv_BNE`.** -/
theorem equiv_BNE_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- SPEC-PRE alignment witness (ZisK assembler/transpiler invariant).
    (h_target_aligned :
      (bne_input.PC + BitVec.signExtend 64 bne_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) state
      = (bus_effect exec_row [] state).2 := by
  obtain ⟨h_not_throws, h_success⟩ :=
    bne_pure_no_exception_of_aligned bne_input h_target_aligned
  exact ZiskFv.Equivalence.BranchNotEqual.equiv_BNE
    state bne_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_not_throws h_success

end ZiskFv.Compliance
