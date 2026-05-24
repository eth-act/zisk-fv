import Mathlib

import ZiskFv.EquivCore.Sllw
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Compliance.SharedBundles

/-! `equiv_SLLW` Compliance wrapper — BinaryExtension W-shift,
    OP_SLL_W = 0x24. RTYPEW form. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_SLLW
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
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SLL_W m v r_main h_main_active h_main_op
  exact ZiskFv.EquivCore.Sllw.equiv_SLLW state sllw_input r1 r2 rd
    m v r_main r_binary
    ⟨exec_row, e0, e1, e2⟩
    { input_r1_eq := h_input_r1_sail
      input_r2_eq := h_input_r2_sail
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := h_m0_mult
      m0_as := h_m0_as
      m1_mult := h_m1_mult
      m1_as := h_m1_as
      m2_mult := h_m2_mult
      m2_as := h_m2_as
      rd_idx := h_rd_idx }
    ⟨h_main_active, h_main_op⟩
    h_match h_lane_rd

/-- Static-lookup route for the SLLW wrapper. This is not the canonical wrapper
    surface; it consumes the shared BinaryExtension static lookup witness and
    delegates through the explicit-wf core route. -/
theorem equiv_SLLW_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sllw_input : PureSpec.SllwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
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
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SLLW)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SLL_W m v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
      ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
        v r_binary offset env h_static
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SLL_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift r_binary = 1 :=
    ZiskFv.Airs.BinaryExtension.op_is_shift_one_SLL_W_of_static_lookup
      v r_binary offset env h_static h_op_v_eq
  exact ZiskFv.EquivCore.Sllw.equiv_SLLW_of_wf state sllw_input r1 r2 rd
    m v r_main r_binary bus
    { input_r1_eq := h_input_r1_sail
      input_r2_eq := h_input_r2_sail
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := h_m0_mult
      m0_as := h_m0_as
      m1_mult := h_m1_mult
      m1_as := h_m1_as
      m2_mult := h_m2_mult
      m2_as := h_m2_as
      rd_idx := h_rd_idx }
    ⟨h_main_active, h_main_op⟩
    h_match h_lane_rd h_bytes h_wfs h_op_is_shift

end ZiskFv.Compliance
