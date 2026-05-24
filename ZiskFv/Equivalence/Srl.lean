import ZiskFv.Compliance.Wrappers.Srl
import ZiskFv.Channels.StateEffect

/-!
# `equiv_SRL` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SRL. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SRL`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Srl.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SRL`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SRL OP_SRA)

namespace ZiskFv.Equivalence.Srl


theorem equiv_SRL
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srl_input : PureSpec.SrlInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRL state srl_input r1 r2 rd m v r_main bus promises pins h_lane_rd

/-- Noncanonical static-lookup route for SRL in channel-balance form. -/
theorem equiv_SRL_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srl_input : PureSpec.SrlInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (v : Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRL)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRL)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRL_of_static_lookup state srl_input r1 r2 rd
    m v r_main offset env h_static bus promises pins h_lane_rd

end ZiskFv.Equivalence.Srl
