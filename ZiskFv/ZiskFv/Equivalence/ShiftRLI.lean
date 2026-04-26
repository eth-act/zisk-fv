import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.ShiftRLI
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.srliw
import ZiskFv.RV64D.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses

/-!
End-to-end theorem for RV64 SRLIW (Phase 3A H2c — `ShiftArchetype`
sibling, W-variant immediate).

Mirrors `Equivalence.ShiftLI` for SLLIW with the shift direction swapped
on the Sail side (`sopw.SRLIW`) and the opcode literal swapped on the
circuit side (`OP_SRL_W = 37`).
-/

namespace ZiskFv.Equivalence.ShiftRLI

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.ShiftRLI

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SRLIW
    (_rs1 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : srliw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  srliw_compositional m r_main bus_entry h_circuit

theorem equiv_SRLIW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srliw_input.r1_val state)
    (h_input_rd : srliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srliw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = let srliw_output := PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input
        (do
          Sail.writeReg Register.nextPC srliw_output.nextPC
          match srliw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIWOP_srliw_pure_equiv
    srliw_input r1 rd h_input_r1 h_input_rd h_input_pc

theorem equiv_SRLIW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srliw_input.r1_val state)
    (h_input_rd : srliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srliw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : srliw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_right
            (Sail.BitVec.extractLsb srliw_input.r1_val 31 0) srliw_input.shamt)) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SRLIW_sail state srliw_input r1 rd
        h_input_r1 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_SHIFTIWOP_srliw_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]


/-- **Phase 5 V12 companion.** Drops `h_input_r1` / `h_input_r2` / 
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_SRLIW_metaplan` after chip_bus_hyps + match composition.  -/
theorem equiv_SRLIW_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 5 V12: bus precondition + ptr/value match (replaces h_input_r1/pc/rd).
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : srliw_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_pc : srliw_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : srliw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_right
            (Sail.BitVec.extractLsb srliw_input.r1_val 31 0) srliw_input.shamt)) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2
    := by
  obtain ⟨h_pc_read, h_rs1_read, h_rs2_read⟩ :=
    ZiskFv.Airs.BusHypotheses.chip_bus_hyps_alu_rrw
      state exec_row e0 e1 e2
      h_exec_len h_e0_mult h_e1_mult
      h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
      h_bus
  have h_input_r1 :
      read_xreg (regidx_to_fin r1) state
        = EStateM.Result.ok srliw_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_rd : srliw_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some srliw_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_SRLIW_metaplan state srliw_input r1 rd exec_row e0 e1 e2 h_input_r1 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val


/-- Constructor: build a `PureSpec.SrliwInput` from bus + shamt. -/
def SrliwInput_of_bus
    (e0 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (shamt : BitVec 5) :
    PureSpec.SrliwInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    shamt := shamt
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Item 4 closure for SRLIW.** Bus-derived input form. -/
theorem equiv_SRLIW_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx)
    (shamt : BitVec 5)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_srliw_pure (SrliwInput_of_bus e0 e2 exec_row shamt)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 5 V12: bus precondition + ptr/value match (replaces h_input_r1/pc/rd).
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_right
            (Sail.BitVec.extractLsb (SrliwInput_of_bus e0 e2 exec_row shamt).r1_val 31 0) (SrliwInput_of_bus e0 e2 exec_row shamt).shamt)) :
    execute_instruction
      (instruction.SHIFTIWOP ((SrliwInput_of_bus e0 e2 exec_row shamt).shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2

    := by
  exact equiv_SRLIW_metaplan_from_bus state
    (SrliwInput_of_bus e0 e2 exec_row shamt) r1 rd exec_row e0 e1 e2
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl rfl h_rd_ptr
    rfl h_rd_val

/-- **Track Q ALU fan-out for SRLIW.** Op-bus companion to
    `equiv_SRLIW_metaplan`: drops `h_input_r1` in favour of an op-bus
    precondition. Mirrors `equiv_ADD_metaplan_op_bus`. -/
theorem equiv_SRLIW_metaplan_op_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (op_entry : OperationBusEntry FGL)
    (h_op_mult : op_entry.multiplicity = 1)
    (h_op_bus : (ZiskFv.Airs.OpBusEffect.op_bus_effect [op_entry] state
                  (regidx_to_fin r1) (regidx_to_fin r1)).1)
    (h_a_match :
      srliw_input.r1_val = Goldilocks.lanes_to_bv64 op_entry.a_lo op_entry.a_hi)
    (h_input_rd : srliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srliw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    -- Phase 4.5 A-rewire: decomposed rd-match hypotheses (see equiv_MUL_metaplan).
    (h_rd_idx : srliw_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = LeanRV64D.Functions.sign_extend (m := 64)
          (Sail.shift_bits_right
            (Sail.BitVec.extractLsb srliw_input.r1_val 31 0) srliw_input.shamt)) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  have h_r1_read := (ZiskFv.Airs.OpBusHypotheses.chip_op_bus_hyps_alu
      state op_entry (regidx_to_fin r1) (regidx_to_fin r1) h_op_mult h_op_bus).1
  have h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srliw_input.r1_val state := by
    rw [h_a_match]; exact h_r1_read
  exact equiv_SRLIW_metaplan state srliw_input r1 rd exec_row e0 e1 e2 h_input_r1 h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val

end ZiskFv.Equivalence.ShiftRLI
