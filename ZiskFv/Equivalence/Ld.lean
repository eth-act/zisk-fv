import ZiskFv.Compliance.Wrappers.Ld
import ZiskFv.Channels.StateEffect

/-!
# `equiv_LD` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for LD. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_LD`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Ld.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_LD`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.Trusted (OP_COPYB)

namespace ZiskFv.Equivalence.Ld


theorem equiv_LD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (ld_input : PureSpec.LdInput)
    (regs : ZiskFv.Compliance.ModeRegsFull)
    (main : Valid_Main FGL FGL) (mem : Valid_Mem FGL FGL) (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins main r_main 0 OP_COPYB)
    (promises : ZiskFv.EquivCore.Promises.LoadPromises
        state regs.mstatus regs.pmaRegion regs.misa regs.mseccfg
        (PureSpec.ld_state_assumptions ld_input state)
        (PureSpec.execute_LOADD_pure ld_input).nextPC
        bus.exec_row bus.e0 bus.e1 bus.e2)
    (h_memory_burden : promises.memoryBurden)
    (w : ZiskFv.EquivCore.Bridge.MemClean.LdCleanWitness
        main mem r_main bus ld_input)
    : execute_instruction (instruction.LOAD (
      ld_input.imm,
      regidx.Regidx ld_input.r1,
      regidx.Regidx ld_input.rd,
      false,
      8
    )) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_LD state ld_input regs main mem r_main bus pins promises h_memory_burden w

end ZiskFv.Equivalence.Ld
