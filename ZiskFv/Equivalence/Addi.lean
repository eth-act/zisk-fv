import ZiskFv.Compliance.Wrappers.Addi
import ZiskFv.Channels.StateEffect

/-!
# `equiv_ADDI` per-opcode canonical theorem (channel-balance form)

Post-T4-purge canonical: ADDI routes through the lookup-aware Binary
provider. The legacy BinaryAdd-arm path was retired in T4-purge.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open ZiskFv.Trusted (OP_ADD)

namespace ZiskFv.Equivalence.Addi


theorem equiv_ADDI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_ADD)
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
    (h_addi_subset : itype_imm_subset_holds_main m r_main addi_input.imm)
    (h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2)
    : (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADDI
    state addi_input r1 rd imm m providerTable providerRow r_main bus pins
    h_component h_table_spec h_provider_row h_match h_addi_subset h_lane_rd promises

end ZiskFv.Equivalence.Addi
