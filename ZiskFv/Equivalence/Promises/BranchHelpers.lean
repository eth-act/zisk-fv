import Mathlib

import ZiskFv.Equivalence.Promises.Branch
import ZiskFv.SailSpec.beq
import ZiskFv.SailSpec.bne
import ZiskFv.SailSpec.blt
import ZiskFv.SailSpec.bge
import ZiskFv.SailSpec.bltu
import ZiskFv.SailSpec.bgeu

/-!
# `BranchPromises` smart constructors

Per-branch builders that derive the no-exception bundle fields
(`not_throws`, `success`) from a single 4-byte-alignment hypothesis
on the branch target, and package the result as a full
`BranchPromises` bundle.

The alignment-implies-no-exception lemma is a pure BitVec computation:
bits 0 and 1 of an address ≡ 0 mod 4 are both zero, so both
`BitVec.ofBool x[i] == 1#1` checks inside `execute_<OP>_pure` fail
uniformly (regardless of taken/not-taken). The same 6-step proof
works for every branch — only the `execute_<OP>_pure` symbol differs.

These helpers were extracted from the per-opcode `Compliance/FromTrust/<Op>.lean`
wrappers (where they previously lived inline as `private theorem
<op>_pure_no_exception_of_aligned`). The wrappers are now pure
pass-throughs that take a fully-populated `BranchPromises` bundle.
-/

namespace ZiskFv.Equivalence.Promises

open ZiskFv.Trusted

/-! ## BEQ -/

private theorem beq_pure_no_exception_of_aligned
    (input : PureSpec.BeqInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BEQ_pure input).throws = false
    ∧ (PureSpec.execute_BEQ_pure input).success = true := by
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
  · simp [PureSpec.execute_BEQ_pure, ← h_t, h_bit0]
  · simp [PureSpec.execute_BEQ_pure, ← h_t, h_bit0, h_bit1]

/-- Build a `BranchPromises` bundle for BEQ from a 4-byte-alignment
    hypothesis on the branch target plus the structural pass-through
    pins. ZisK's assembler/transpiler invariant guarantees the
    alignment; the not-throws and success bundle fields are derived
    here via `beq_pure_no_exception_of_aligned`. -/
def BranchPromises.of_aligned_BEQ
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (beq_input : PureSpec.BeqInput)
    {imm : BitVec 13} {r1 r2 : regidx}
    {misa_val : RegisterType Register.misa}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (beq_input.PC + BitVec.signExtend 64 beq_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC) :
    BranchPromises state beq_input.imm beq_input.r1_val beq_input.r2_val
      beq_input.PC misa_val
      (PureSpec.execute_BEQ_pure beq_input).nextPC
      (PureSpec.execute_BEQ_pure beq_input).throws
      (PureSpec.execute_BEQ_pure beq_input).success
      imm r1 r2 exec_row :=
  let ⟨h_not_throws, h_success⟩ :=
    beq_pure_no_exception_of_aligned beq_input h_target_aligned
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

/-! ## BNE -/

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

/-- Build a `BranchPromises` bundle for BNE from a 4-byte-alignment
    hypothesis on the branch target. Mirrors `of_aligned_BEQ`. -/
def BranchPromises.of_aligned_BNE
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (bne_input : PureSpec.BneInput)
    {imm : BitVec 13} {r1 r2 : regidx}
    {misa_val : RegisterType Register.misa}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bne_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bne_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bne_input.PC + BitVec.signExtend 64 bne_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC) :
    BranchPromises state bne_input.imm bne_input.r1_val bne_input.r2_val
      bne_input.PC misa_val
      (PureSpec.execute_BNE_pure bne_input).nextPC
      (PureSpec.execute_BNE_pure bne_input).throws
      (PureSpec.execute_BNE_pure bne_input).success
      imm r1 r2 exec_row :=
  let ⟨h_not_throws, h_success⟩ :=
    bne_pure_no_exception_of_aligned bne_input h_target_aligned
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

/-! ## BLT -/

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

/-- Build a `BranchPromises` bundle for BLT. Mirrors `of_aligned_BEQ`. -/
def BranchPromises.of_aligned_BLT
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (blt_input : PureSpec.BltInput)
    {imm : BitVec 13} {r1 r2 : regidx}
    {misa_val : RegisterType Register.misa}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
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
    BranchPromises state blt_input.imm blt_input.r1_val blt_input.r2_val
      blt_input.PC misa_val
      (PureSpec.execute_BLT_pure blt_input).nextPC
      (PureSpec.execute_BLT_pure blt_input).throws
      (PureSpec.execute_BLT_pure blt_input).success
      imm r1 r2 exec_row :=
  let ⟨h_not_throws, h_success⟩ :=
    blt_pure_no_exception_of_aligned blt_input h_target_aligned
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

/-! ## BGE -/

private theorem bge_pure_no_exception_of_aligned
    (input : PureSpec.BgeInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BGE_pure input).throws = false
    ∧ (PureSpec.execute_BGE_pure input).success = true := by
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
  · simp [PureSpec.execute_BGE_pure, ← h_t, h_bit0]
  · simp [PureSpec.execute_BGE_pure, ← h_t, h_bit0, h_bit1]

/-- Build a `BranchPromises` bundle for BGE. Mirrors `of_aligned_BEQ`. -/
def BranchPromises.of_aligned_BGE
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (bge_input : PureSpec.BgeInput)
    {imm : BitVec 13} {r1 r2 : regidx}
    {misa_val : RegisterType Register.misa}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bge_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bge_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bge_input.PC + BitVec.signExtend 64 bge_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGE_pure bge_input).nextPC) :
    BranchPromises state bge_input.imm bge_input.r1_val bge_input.r2_val
      bge_input.PC misa_val
      (PureSpec.execute_BGE_pure bge_input).nextPC
      (PureSpec.execute_BGE_pure bge_input).throws
      (PureSpec.execute_BGE_pure bge_input).success
      imm r1 r2 exec_row :=
  let ⟨h_not_throws, h_success⟩ :=
    bge_pure_no_exception_of_aligned bge_input h_target_aligned
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

/-! ## BLTU -/

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

/-- Build a `BranchPromises` bundle for BLTU. Mirrors `of_aligned_BEQ`. -/
def BranchPromises.of_aligned_BLTU
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (bltu_input : PureSpec.BltuInput)
    {imm : BitVec 13} {r1 r2 : regidx}
    {misa_val : RegisterType Register.misa}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
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
    BranchPromises state bltu_input.imm bltu_input.r1_val bltu_input.r2_val
      bltu_input.PC misa_val
      (PureSpec.execute_BLTU_pure bltu_input).nextPC
      (PureSpec.execute_BLTU_pure bltu_input).throws
      (PureSpec.execute_BLTU_pure bltu_input).success
      imm r1 r2 exec_row :=
  let ⟨h_not_throws, h_success⟩ :=
    bltu_pure_no_exception_of_aligned bltu_input h_target_aligned
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

/-! ## BGEU -/

private theorem bgeu_pure_no_exception_of_aligned
    (input : PureSpec.BgeuInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BGEU_pure input).throws = false
    ∧ (PureSpec.execute_BGEU_pure input).success = true := by
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
  · simp [PureSpec.execute_BGEU_pure, ← h_t, h_bit0]
  · simp [PureSpec.execute_BGEU_pure, ← h_t, h_bit0, h_bit1]

/-- Build a `BranchPromises` bundle for BGEU. Mirrors `of_aligned_BEQ`. -/
def BranchPromises.of_aligned_BGEU
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (bgeu_input : PureSpec.BgeuInput)
    {imm : BitVec 13} {r1 r2 : regidx}
    {misa_val : RegisterType Register.misa}
    {exec_row : List (Interaction.ExecutionBusEntry FGL)}
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_target_aligned :
      (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm).toNat % 4 = 0)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC) :
    BranchPromises state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val
      bgeu_input.PC misa_val
      (PureSpec.execute_BGEU_pure bgeu_input).nextPC
      (PureSpec.execute_BGEU_pure bgeu_input).throws
      (PureSpec.execute_BGEU_pure bgeu_input).success
      imm r1 r2 exec_row :=
  let ⟨h_not_throws, h_success⟩ :=
    bgeu_pure_no_exception_of_aligned bgeu_input h_target_aligned
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

end ZiskFv.Equivalence.Promises
