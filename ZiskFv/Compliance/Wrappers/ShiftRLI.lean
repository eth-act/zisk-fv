import Mathlib

import ZiskFv.EquivCore.Srliw
import ZiskFv.EquivCore.Promises.ShiftImm
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Compliance.SharedBundles

/-! `equiv_SRLIW` Compliance wrapper — BinaryExtension W immediate shift,
    OP_SRL_W = 0x25. SHIFTIWOP form. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


theorem equiv_SRLIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SRL_W m v r_main h_main_active h_main_op
  exact ZiskFv.EquivCore.Srliw.equiv_SRLIW state srliw_input r1 rd
    m v r_main r_binary
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h_main_active, h_main_op⟩
    h_match h_lane_rd

/-- Static-lookup route for the SRLIW wrapper. This is not the canonical
    wrapper surface; it consumes the shared BinaryExtension static lookup
    witness and delegates through the explicit-wf core route. -/
theorem equiv_SRLIW_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srliw_input : PureSpec.SrliwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state srliw_input.r1_val srliw_input.rd srliw_input.PC
        (PureSpec.execute_SHIFTIWOP_srliw_pure srliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction
      (instruction.SHIFTIWOP (srliw_input.shamt, r1, rd, sopw.SRLIW)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SRL_W m v r_main h_main_active h_main_op
  obtain ⟨h_op_fgl, _, _⟩ :=
    ZiskFv.EquivCore.Bridge.BinaryExtension.project_match_op_clo_chi
      m v r_main r_binary h_match
  let h_bytes := ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookups v r_binary
  have h_wfs : ZiskFv.Airs.BinaryExtension.ByteLookupWfHypotheses h_bytes := by
    simpa [h_bytes] using
      ZiskFv.Airs.BinaryExtension.binary_extension_row_byte_lookup_wfs_of_static_lookup
        v r_binary offset env h_static
  have h_op_v_eq : v.op r_binary = ZiskFv.Trusted.OP_SRL_W := by
    rw [← h_op_fgl, h_main_op]
  have h_op_is_shift : v.op_is_shift r_binary = 1 :=
    ZiskFv.Airs.BinaryExtension.op_is_shift_one_SRL_W_of_static_lookup
      v r_binary offset env h_static h_op_v_eq
  exact ZiskFv.EquivCore.Srliw.equiv_SRLIW_of_wf state srliw_input r1 rd
    m v r_main r_binary bus
    promises
    ⟨h_main_active, h_main_op⟩
    h_match h_lane_rd h_bytes h_wfs h_op_is_shift

end ZiskFv.Compliance
