import ZiskFv.Compliance.Wrappers.Or
import ZiskFv.Channels.StateEffect

/-!
# `equiv_OR` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for OR. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_OR`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Or.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_OR`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_SUB OP_AND OP_OR OP_XOR)

namespace ZiskFv.Equivalence.Or


theorem equiv_OR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_OR state or_input r1 r2 rd m v r_main bus pins h_lane_rd promises


/-- Static-provider BinaryTable route for `equiv_OR`. -/
theorem equiv_OR_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (h_binary_core : ∀ r, ZiskFv.Airs.Binary.core_every_row v r)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_OR)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_OR_of_static_lookup state or_input r1 r2 rd m v r_main offset env h_static h_binary_core bus pins h_lane_rd promises

end ZiskFv.Equivalence.Or
