import Mathlib

import ZiskFv.EquivCore.Sraiw
import ZiskFv.EquivCore.Promises.ShiftImm
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-! `equiv_SRAIW` Compliance wrapper — BinaryExtension W signed
    immediate shift, OP_SRA_W = 0x26. SHIFTIWOP form. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


lemma equiv_SRAIW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sraiw_input : PureSpec.SraiwInput)
    (r1 rd : regidx)
    (m : Valid_Main FGL FGL)
    (p : ZiskFv.AirsClean.BinaryFamily.ShiftStaticProvider)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftWImmPromises
        state sraiw_input.r1_val sraiw_input.rd sraiw_input.PC
        (PureSpec.execute_SHIFTIWOP_sraiw_pure sraiw_input).nextPC
        r1 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA_W)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage p.rowInput) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb sraiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32 p.rowInput)
    (h_shift_pin_row : sraiw_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32 p.rowInput)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction
      (instruction.SHIFTIWOP (sraiw_input.shamt, r1, rd, sopw.SRAIW)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  exact ZiskFv.EquivCore.Sraiw.equiv_SRAIW_of_static_row state sraiw_input r1 rd
    m p.rowInput r_main bus promises pins h_match p.facts.1 p.facts.2
    h_input_r1_row h_shift_pin_row h_lane_rd

-- equiv_<OP>_of_static_lookup (alt route, op_bus_perm_sound) deleted in T4-purge P3.2.

end ZiskFv.Compliance
