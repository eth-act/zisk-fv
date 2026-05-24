import ZiskFv.Compliance.Wrappers.Xori
import ZiskFv.Channels.StateEffect

/-!
# `equiv_XORI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for XORI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_XORI`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Xori.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_XORI`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_AND OP_OR OP_XOR)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)

namespace ZiskFv.Equivalence.Xori


theorem equiv_XORI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_XORI state xori_input r1 rd imm m v r_main bus pins h_xori_subset h_lane_rd promises


/-- Static-provider BinaryTable route for `equiv_XORI`. -/
theorem equiv_XORI_of_static_lookup
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (xori_input : PureSpec.XoriInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.Binary.StaticLookupSoundness v)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_XOR)
    (h_xori_subset : itype_imm_subset_holds_main m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.XORI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_XORI_of_static_lookup state xori_input r1 rd imm m v r_main offset env h_static bus pins h_xori_subset h_lane_rd promises

end ZiskFv.Equivalence.Xori
