import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.BranchGreaterEqualUnsigned
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.bgeu
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses

/-!
End-to-end theorem for RV64 BGEU (Phase 3A B4). Combines:

* `ZiskFv.Trusted.transpile_BGEU`,
* `ZiskFv.Spec.BranchGreaterEqualUnsigned.branch_geu_compositional`
  (archetype at `opcode_lit = OP_LTU`),
* `PureSpec.execute_BGEU_pure_equiv` (direct proof — Phase 4
  retired C2d).

Shape (b) bus — reuses `bus_effect_matches_sail_beq`.
-/

namespace ZiskFv.Equivalence.BranchGreaterEqualUnsigned

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.BranchGreaterEqualUnsigned

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level BGEU theorem.** -/
theorem equiv_BGEU
    (_rs1 _rs2 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : branch_geu_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main
            + m.flag r_main * (m.jmp_offset1 r_main - m.jmp_offset2 r_main) :=
  branch_geu_compositional m r_main next_pc h_circuit

/-- **Sail-level companion.** -/
theorem equiv_BGEU_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = let bgeu_output := PureSpec.execute_BGEU_pure bgeu_input
        (do
          Sail.writeReg Register.nextPC bgeu_output.nextPC
          if bgeu_output.throws then
            throw (Sail.Error.Assertion "extensions/I/base_insts.sail:59.29-59.30")
          else if !bgeu_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (bgeu_input.PC + BitVec.signExtend 64 bgeu_input.imm)),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_BGEU_pure_equiv bgeu_input imm r1 r2 h_input_imm h_input_r1 h_input_r2
    h_input_pc h_input_misa h_misa_c

/-- **Metaplan theorem (Phase 3A B4).** -/
theorem equiv_BGEU_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false)
    (h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = (bus_effect exec_row [] state).2 := by
  rw [equiv_BGEU_sail state bgeu_input imm r1 r2 misa_val
        h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c]
  symm
  exact ZiskFv.Airs.BusEmission.bus_effect_matches_sail_beq
    state exec_row
    (PureSpec.execute_BGEU_pure bgeu_input).nextPC
    (PureSpec.execute_BGEU_pure bgeu_input).throws
    (PureSpec.execute_BGEU_pure bgeu_input).success
    bgeu_input.PC bgeu_input.imm
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success


/-- **Phase 5 V12 companion for BGEU.** Drops `h_input_pc` via
    `chip_bus_hyps_branch_rrw` + `readReg_of_readReg_succ`. Other
    `h_input_*` stay — branch memory bus is empty, so rs1/rs2
    reads go via operation bus (not derivable from `h_bus` here). -/
theorem equiv_BGEU_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok bgeu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok bgeu_input.r2_val state)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Phase 5 V12: bus precondition + PC match (replaces h_input_pc).
    (h_bus : (bus_effect exec_row [] state).1)
    (h_pc : bgeu_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false)
    (h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) state
      = (bus_effect exec_row [] state).2
    := by
  have h_pc_read := ZiskFv.Airs.BusHypotheses.chip_bus_hyps_branch_rrw
    state exec_row h_exec_len h_e0_mult h_e1_mult h_bus
  have h_input_pc : state.regs.get? Register.PC = .some bgeu_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_BGEU_metaplan state bgeu_input imm r1 r2 misa_val exec_row h_input_imm h_input_r1 h_input_r2 h_input_pc h_input_misa h_misa_c h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_not_throws h_success

end ZiskFv.Equivalence.BranchGreaterEqualUnsigned
