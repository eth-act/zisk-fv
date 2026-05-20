import ZiskFv.Compliance.Wrappers.Shift
import ZiskFv.Compliance.Wrappers.ShiftR
import ZiskFv.Compliance.Wrappers.ShiftRA
import ZiskFv.Compliance.Wrappers.ShiftLI
import ZiskFv.Compliance.Wrappers.ShiftRLI
import ZiskFv.Compliance.Wrappers.ShiftRAI
import ZiskFv.Vm.StateEffect

/-!
# Phase 4 probes — W-shift family equiv_<OP>_v2 corollaries

W-suffix shifts: SLLW / SRLW / SRAW (RTYPEW shape with many extra
unfolded promises) and SLLIW / SRLIW / SRAIW (SHIFTIOPW shape).
All pair with BinaryExtension and map to SLL_W / SRL_W / SRA_W
mainOpKind arms.

## Trust note

No axioms added.
-/

open ZiskFv.Vm
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SLL_W OP_SRL_W OP_SRA_W)

namespace ZiskFv.Vm.Probe


theorem equiv_SLLW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sllw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sllw_input.r2_val state)
    (h_input_rd : sllw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sllw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sllw_pure sllw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : sllw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SLLW state sllw_input r1 r2 rd m v r_main bus
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    pins h_lane_rd

theorem equiv_SRLW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok srlw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok srlw_input.r2_val state)
    (h_input_rd : srlw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some srlw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : srlw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRLW state srlw_input r1 r2 rd m v r_main bus
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    pins h_lane_rd

theorem equiv_SRAW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraw_input : PureSpec.SrawInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (h_input_r1_sail : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sraw_input.r1_val state)
    (h_input_r2_sail : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sraw_input.r2_val state)
    (h_input_rd : sraw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sraw_input.PC)
    (h_exec_len : bus.exec_row.length = 2)
    (h_e0_mult : bus.exec_row[0]!.multiplicity = -1)
    (h_e1_mult : bus.exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (bus.exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_sraw_pure sraw_input).nextPC)
    (h_m0_mult : bus.e0.multiplicity = -1) (h_m0_as : bus.e0.as.val = 1)
    (h_m1_mult : bus.e1.multiplicity = -1) (h_m1_as : bus.e1.as.val = 1)
    (h_m2_mult : bus.e2.multiplicity = 1) (h_m2_as : bus.e2.as.val = 1)
    (h_rd_idx : sraw_input.rd = Transpiler.wrap_to_regidx bus.e2.ptr)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRAW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRAW state sraw_input r1 r2 rd m v r_main bus
    h_input_r1_sail h_input_r2_sail h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    pins h_lane_rd

-- Immediate W-shifts (cleaner shape: only promises + pins + lane).
theorem equiv_SLLIW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SLLIW state slliw_input r1 rd m v r_main bus promises pins h_lane_rd

theorem equiv_SRLIW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRLIW state srliw_input r1 rd m v r_main bus promises pins h_lane_rd

theorem equiv_SRAIW_v2
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraiw_input : PureSpec.SraiwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRA_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRAIW state sraiw_input r1 rd m v r_main bus promises pins h_lane_rd

end ZiskFv.Vm.Probe
