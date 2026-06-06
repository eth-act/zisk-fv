import ZiskFv.Compliance.Wrappers.Lh
import ZiskFv.Channels.StateEffect

/-!
# `equiv_LH` per-opcode canonical theorem (channel-balance form)

Post-T4-purge canonical: mirror of equiv_LB for 2-byte signed loads.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_SIGNEXTEND_H)

namespace ZiskFv.Equivalence.Lh


theorem equiv_LH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
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
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 OP_SIGNEXTEND_H)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_memory_burden : promises.memoryBurden)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LoadCleanWitness
        main mem r_main bus lh_input.r1_val lh_input.imm lh_input.rd)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
      ))) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LH
    state lh_input regs main mem r_main v r_binary offset env h_static h_match
    bus pins promises h_memory_burden w

end ZiskFv.Equivalence.Lh
