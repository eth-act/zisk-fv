import ZiskFv.Compliance.Wrappers.Lw
import ZiskFv.Channels.StateEffect

/-!
# `equiv_LW_via_static_match` channel-effect shim
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_SIGNEXTEND_W)

namespace ZiskFv.Equivalence.Lw


theorem equiv_LW_via_static_match
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lw_input : PureSpec.LwInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_binary offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main main r_main)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 OP_SIGNEXTEND_W)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lw_state_assumptions lw_input state)
        (PureSpec.execute_LOADW_pure lw_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lw_input.imm, regidx.Regidx lw_input.r1, regidx.Regidx lw_input.rd, false, 4
      ))) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LW_of_static_match
    state lw_input regs main mem r_main v r_binary offset env h_static h_match
    bus pins promises

end ZiskFv.Equivalence.Lw
