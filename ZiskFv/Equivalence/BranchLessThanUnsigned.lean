import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.BranchLessThanUnsigned
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.bltu
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 BLTU. Combines:

* `ZiskFv.Trusted.transpile_BLTU`,
* `ZiskFv.Circuit.BranchLessThanUnsigned.branch_ltu_compositional`
  (archetype at `opcode_lit = OP_LTU`),
* `PureSpec.execute_BLTU_pure_equiv`.

Shape (b) bus — reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence.BranchLessThanUnsigned

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.BranchLessThanUnsigned

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BLTU theorem.** -/
theorem equiv_BLTU
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_ltu_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_ltu_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** -/
theorem equiv_BLTU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = let bltu_output := PureSpec.execute_BLTU_pure bltu_input
        (do
          Sail.writeReg Register.nextPC bltu_output.nextPC
          if bltu_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bltu_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BLTU_pure_equiv bltu_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem.** -/
theorem equiv_BLTU_metaplan
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
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false)
    (h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BLTU_sail state bltu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BLTU_pure bltu_input).nextPC
    (PureSpec.execute_BLTU_pure bltu_input).throws
    (PureSpec.execute_BLTU_pure bltu_input).success
    bltu_input.PC bltu_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- **Bus-driven companion for BLTU.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. Other
    `h_input_*` stay — branch memory bus is empty, so rs1/rs2
    reads go via operation bus (not derivable from `h_bus` here). -/
theorem equiv_BLTU_metaplan_from_bus
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
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : bltu_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false)
    (h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2
    := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_BLTU_metaplan state bltu_input imm r1 r2 misa_val exec_row h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- Constructor: build a `PureSpec.BltuInput` from exec_row PC + free operand values. -/
def BltuInput_of_bus
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (imm : BitVec 13)
    (r1_val r2_val : BitVec 64) :
    PureSpec.BltuInput :=
  { imm := imm
    r1_val := r1_val
    r2_val := r2_val
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for BLTU.** Bus-derived input form. -/
theorem equiv_BLTU_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (r1_val r2_val : BitVec 64)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok (BltuInput_of_bus exec_row imm r1_val r2_val).r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok (BltuInput_of_bus exec_row imm r1_val r2_val).r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure (BltuInput_of_bus exec_row imm r1_val r2_val)).nextPC)
    (h_not_throws : (PureSpec.execute_BLTU_pure (BltuInput_of_bus exec_row imm r1_val r2_val)).throws = false)
    (h_success : (PureSpec.execute_BLTU_pure (BltuInput_of_bus exec_row imm r1_val r2_val)).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2

    := by
  exact equiv_BLTU_metaplan_from_bus state
    (BltuInput_of_bus exec_row imm r1_val r2_val) imm r1 r2 misa_val exec_row
    rfl h_input_r1 h_input_r2
    h_input_misa h_misa_c 
    h_bus rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_not_throws h_success

/-- **Track Q POC for BLTU.** Operation-bus companion to
    `equiv_BLTU_metaplan_from_bus`. Mirrors `equiv_BEQ_metaplan_op_bus`. -/
theorem equiv_BLTU_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (op_entry : OperationBusEntry FGL)
    (h_input_imm : bltu_input.imm = imm)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r2)).1)
    (h_a_match :
      bltu_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_b_match :
      bltu_input.r2_val = Goldilocks.lanes_to_bv64 op_entry.b_lo op_entry.b_hi)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : bltu_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false)
    (h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = (bus_effect exec_row [] state).2 := by
  have h_reads := ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_branch
    state op_entry (regidx_to_fin r1) (regidx_to_fin r2) h_op_mult h_op_bus
  obtain ⟨h_r1_read, h_r2_read⟩ := h_reads
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state := by rw [h_a_match]; exact h_r1_read
  have h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state := by rw [h_b_match]; exact h_r2_read
  exact equiv_BLTU_metaplan_from_bus state bltu_input imm r1 r2 misa_val exec_row
    h_input_imm h_input_r1 h_input_r2 h_input_misa h_misa_c
    h_bus h_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

/-! ## Misaligned-target companions

Same shape as BLT; case-split predicate is `h_taken : r1.toNat < r2.toNat`
(BLTU taken on unsigned less-than). -/

/-- **Misaligned-target companion (bit-1 case): Sail-side reduction.** -/
theorem equiv_BLTU_metaplan_misaligned
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_taken : bltu_input.r1_val.toNat < bltu_input.r2_val.toNat)
    (h_bit0_aligned :
      BitVec.ofBool (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)[0] = 0#1)
    (h_bit1_misaligned :
      BitVec.ofBool (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)[1] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = EStateM.Result.ok
          (ExecutionResult.Memory_Exception
            ((virtaddr.Virtaddr (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)),
             (ExceptionType.E_Fetch_Addr_Align ())))
          (write_reg_state state Register.nextPC (bltu_input.PC + 4#64)) := by
  rw [equiv_BLTU_sail state bltu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  have h_ltu_b : (bltu_input.r1_val.toNat <b bltu_input.r2_val.toNat) = true := by
    simp [h_taken]
  simp [PureSpec.execute_BLTU_pure, h_ltu_b, h_bit0_aligned, h_bit1_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure,
        EStateM.bind, EStateM.pure, write_reg_state]

/-- **Misaligned-target companion (bit-0 case): Sail-side reduction.** -/
theorem equiv_BLTU_metaplan_misaligned_bit0
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bltu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_taken : bltu_input.r1_val.toNat < bltu_input.r2_val.toNat)
    (h_bit0_misaligned :
      BitVec.ofBool (bltu_input.PC + BitVec.signExtend 64 bltu_input.imm)[0] = 1#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) state
      = EStateM.Result.error
          (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          (write_reg_state state Register.nextPC (bltu_input.PC + 4#64)) := by
  rw [equiv_BLTU_sail state bltu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  have h_ltu_b : (bltu_input.r1_val.toNat <b bltu_input.r2_val.toNat) = true := by
    simp [h_taken]
  simp [PureSpec.execute_BLTU_pure, h_ltu_b, h_bit0_misaligned,
        Sail.writeReg, PreSail.writeReg, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind,
        EStateM.bind, write_reg_state]

end ZiskFv.Equivalence.BranchLessThanUnsigned
