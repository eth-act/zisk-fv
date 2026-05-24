import ZiskFv.Compliance.Wrappers.Lh
import ZiskFv.Channels.StateEffect

/-!
# `equiv_LH` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LH. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_LH`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Lh.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_LH`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_SIGNEXTEND_B OP_SIGNEXTEND_H OP_SIGNEXTEND_W)

namespace ZiskFv.Equivalence.Lh


theorem equiv_LH
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 OP_SIGNEXTEND_H)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
      ))) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LH state lh_input regs main mem r_main v bus pins promises

/-- Noncanonical static-lookup route for LH in channel-balance form. -/
theorem equiv_LH_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (lh_input : PureSpec.LhInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 1 OP_SIGNEXTEND_H)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.lh_state_assumptions lh_input state)
        (PureSpec.execute_LOADH_pure lh_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        lh_input.imm, regidx.Regidx lh_input.r1, regidx.Regidx lh_input.rd, false, 2
      ))) state = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LH_of_static_lookup state lh_input regs main mem r_main v
    offset env h_static bus pins promises

end ZiskFv.Equivalence.Lh
