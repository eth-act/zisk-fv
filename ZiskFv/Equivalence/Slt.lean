import ZiskFv.Compliance.Wrappers.Slt
import ZiskFv.Channels.StateEffect
import ZiskFv.AirsClean.BinaryFamily.Balance

/-!
# `equiv_SLT` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SLT. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SLT`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Slt.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SLT`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)
open ZiskFv.Trusted (OP_LT OP_LTU)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)

namespace ZiskFv.Equivalence.Slt


theorem equiv_SLT
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slt_input : PureSpec.SltInput)
    (r1 r2 rd : regidx)
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
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state slt_input.r1_val slt_input.r2_val slt_input.rd slt_input.PC
        (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SLT
    state slt_input r1 r2 rd m providerTable providerRow r_main bus pins
    h_component h_table_spec h_provider_row h_match h_lane_rd promises

end ZiskFv.Equivalence.Slt
