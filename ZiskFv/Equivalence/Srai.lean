import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Circuit.Srai
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.srai
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Equivalence.RdValDerivation.BinaryShift
import ZiskFv.Equivalence.RdValDerivation.SailBridge

/-!
End-to-end theorem for RV64 SRAI (immediate sibling of SRA).

Mirrors `Equivalence.Slli` structurally, swapping `sop.SLLI` for
`sop.SRAI`.
-/

namespace ZiskFv.Equivalence.Srai

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Srai

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SRAI theorem.** -/
theorem equiv_SRAI
    (_rs1 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : srai_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = m.a_1 r_main ∧ bus_entry.b_hi = m.b_1 r_main :=
  srai_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** -/
theorem equiv_SRAI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srai_input.r1_val state)
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srai_input.PC) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = let srai_output := PureSpec.execute_SHIFTIOP_srai_pure srai_input
        (do
          Sail.writeReg Register.nextPC srai_output.nextPC
          match srai_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIOP_srai_pure_equiv
    srai_input r1 rd shamt h_input_r1 h_input_shamt h_input_rd h_input_pc

/-- **Metaplan theorem.** -/
theorem equiv_SRAI_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srai_input.r1_val state)
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srai_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srai_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_SHIFTIOP_pure srai_input.r1_val srai_input.shamt sop.SRAI) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SRAI_sail state srai_input r1 rd shamt
        h_input_r1 h_input_shamt h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_SHIFTIOP_srai_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-- **Tier-1 metaplan: SRAI without `h_rd_val` parameter**. -/
theorem equiv_SRAI_metaplan_tier1
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main C FGL FGL)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srai_input.r1_val state)
    (h_input_shamt : srai_input.shamt = shamt)
    (h_input_rd : srai_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srai_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : srai_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_op : (v.op r_binary).val = ZiskFv.Airs.BinaryExtensionTable.OP_SRA)
    (h_bytes : ZiskFv.Airs.BinaryExtension.ByteLookupHypotheses v r_binary)
    (h_a_range : ZiskFv.Airs.BinaryExtension.a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_circuit : srai_input.r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift_pin : srai_input.shamt.toNat = (v.free_in_b r_binary).val % 64) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  set shift : ℕ := srai_input.shamt.toNat with h_shift_def
  have h_discharge :=
    ZiskFv.Equivalence.RdValDerivation.BinaryShift.h_rd_val_shift_srai
      m v r_main r_binary e2 srai_input.r1_val shift h_op h_bytes h_a_range
      hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
      hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
      hc_lo_sum_lt hc_hi_sum_lt
      h_match_clo h_match_chi h_lane_rd
      h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
      h_input_r1_circuit
      (by rw [h_shift_def]; exact h_shift_pin)
  have h_bridge :=
    ZiskFv.Equivalence.RdValDerivation.SailBridge.sail_srai_bridge
      srai_input.r1_val srai_input.shamt shift h_shift_def
  have h_rd_val : U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                              e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_SHIFTIOP_pure srai_input.r1_val srai_input.shamt sop.SRAI := by
    rw [h_discharge, h_bridge]
  exact equiv_SRAI_metaplan state srai_input r1 rd shamt exec_row e0 e1 e2
    h_input_r1 h_input_shamt h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_rd_idx h_rd_val


/-- **Bus-precondition companion.** Drops `h_input_r1` / `h_input_r2` /
    `h_input_pc` / `h_input_rd` in favor of a single `h_bus :
    (bus_effect ...).1` plus ptr/value match hypotheses.
    Delegates to `equiv_SRAI_metaplan` after chip_bus_hyps + match composition.  -/
theorem equiv_SRAI_metaplan_from_bus
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srai_input : PureSpec.SraiInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_shamt : srai_input.shamt = shamt)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_r1_val : srai_input.r1_val
      = U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                    e0.x4, e0.x5, e0.x6, e0.x7])
    (h_pc : srai_input.PC = BitVec.ofNat 64 (exec_row[0]!.pc).val)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_idx : srai_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_SHIFTIOP_pure srai_input.r1_val srai_input.shamt sop.SRAI) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
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
        = EStateM.Result.ok srai_input.r1_val state := by
    rw [h_r1_ptr, h_r1_val]; exact h_rs1_read
  have h_input_rd : srai_input.rd = regidx_to_fin rd := by
    rw [h_rd_ptr]; exact h_rd_idx
  have h_input_pc : state.regs.get? Register.PC = .some srai_input.PC := by
    rw [h_pc]
    exact ZiskFv.Airs.BusHypotheses.readReg_of_readReg_succ h_pc_read
  exact equiv_SRAI_metaplan state srai_input r1 rd shamt exec_row e0 e1 e2 h_input_r1 h_input_shamt h_input_rd h_input_pc h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx h_rd_val


/-- Constructor: build a `PureSpec.SraiInput` from bus entries + shamt. -/
def SraiInput_of_bus
    (e0 e2 : Interaction.MemoryBusEntry FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (shamt : BitVec 6) :
    PureSpec.SraiInput :=
  { r1_val := U64.toBV #v[e0.x0, e0.x1, e0.x2, e0.x3,
                          e0.x4, e0.x5, e0.x6, e0.x7]
    shamt := shamt
    rd := Transpiler.wrap_to_regidx e2.ptr
    PC := BitVec.ofNat 64 (exec_row[0]!.pc).val }

/-- **Bus-self form for SRAI.** Eliminates value-level match hyps via `SraiInput_of_bus`. -/
theorem equiv_SRAI_metaplan_bus_self
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (r1 rd : regidx) (shamt : BitVec 6)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_shamt : (SraiInput_of_bus e0 e2 exec_row shamt).shamt = shamt)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIOP_srai_pure (SraiInput_of_bus e0 e2 exec_row shamt)).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_bus : (bus_effect exec_row [e0, e1, e2] state).1)
    (h_r1_ptr : regidx_to_fin r1 = Transpiler.wrap_to_regidx e0.ptr)
    (h_rd_ptr : regidx_to_fin rd = Transpiler.wrap_to_regidx e2.ptr)
    (h_rd_val :
      U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                  e2.x4, e2.x5, e2.x6, e2.x7]
      = execute_SHIFTIOP_pure (SraiInput_of_bus e0 e2 exec_row shamt).r1_val (SraiInput_of_bus e0 e2 exec_row shamt).shamt sop.SRAI) :
    execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SRAI)) state
      = (bus_effect exec_row [e0, e1, e2] state).2

    := by
  exact equiv_SRAI_metaplan_from_bus state
    (SraiInput_of_bus e0 e2 exec_row shamt)
    r1 rd shamt exec_row e0 e1 e2
    rfl
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as
    h_bus h_r1_ptr rfl rfl h_rd_ptr
    rfl h_rd_val

end ZiskFv.Equivalence.Srai
