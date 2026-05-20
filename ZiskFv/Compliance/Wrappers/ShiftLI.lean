import Mathlib

import ZiskFv.Equivalence_v1.Slliw
import ZiskFv.Equivalence_v1.Promises.ShiftImm
import ZiskFv.Equivalence_v1.Promises.BinaryExtensionHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Compliance.SharedBundles

/-! `equiv_SLLIW` Compliance wrapper — BinaryExtension W immediate shift,
    OP_SLL_W = 0x24. SHIFTIWOP form. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus
open ZiskFv.Equivalence_v1.Promises

variable {C : Type → Type → Type} [Circuit FGL FGL C]

theorem equiv_SLLIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.Equivalence_v1.Promises.ShiftWImmPromises
        state slliw_input.r1_val slliw_input.rd slliw_input.PC
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SLL_W)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h_main_active, h_main_op⟩ := pins
  obtain ⟨r_binary, h_match⟩ :=
    binexec_op_bus_handshake_SLL_W m v r_main h_main_active h_main_op
  exact ZiskFv.Equivalence_v1.Slliw.equiv_SLLIW state slliw_input r1 rd
    m v r_main r_binary
    ⟨exec_row, e0, e1, e2⟩
    promises
    ⟨h_main_active, h_main_op⟩
    h_match h_lane_rd

end ZiskFv.Compliance
