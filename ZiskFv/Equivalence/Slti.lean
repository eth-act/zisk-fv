import ZiskFv.Compliance.Wrappers.Slti
import ZiskFv.Channels.StateEffect
import ZiskFv.AirsClean.BinaryFamily.Balance

/-!
# `equiv_SLTI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SLTI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SLTI`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Slti.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SLTI`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_LT OP_LTU)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)

namespace ZiskFv.Equivalence.Slti


theorem equiv_SLTI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slti_input : PureSpec.SltiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_LT)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_main_m32 : m.m32 r_main = 0)
    (h_input_r1_row : slti_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_slti_subset : itype_imm_subset_holds_main m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SLTI
    state slti_input r1 rd imm m providerTable providerRow r_main bus pins
    h_component h_table_spec h_provider_row h_match
    h_main_m32 h_input_r1_row h_slti_subset h_lane_rd promises

end ZiskFv.Equivalence.Slti
