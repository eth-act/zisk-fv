import ZiskFv.Compliance.Wrappers.Add
import ZiskFv.Channels.StateEffect

/-!
# `equiv_ADD` per-opcode canonical theorem (channel-balance form)

Post-T4-purge canonical: ADD routes through the lookup-aware Binary
provider (`Compliance.equiv_ADD`). The legacy BinaryAdd-arm path was
retired in T4-purge (op_bus_permutation_sound + binaryAdd_circuit_completeness
no longer in this theorem's closure).
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Trusted (OP_ADD)

namespace ZiskFv.Equivalence.Add


theorem equiv_ADD
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (add_input : PureSpec.AddInput)
    (r1 r2 rd : regidx)
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
    (h_input_r1_row : add_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : add_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd :
      ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    : execute_instruction (instruction.RTYPE (r2, r1, rd, rop.ADD)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_ADD
    state add_input r1 r2 rd m providerTable providerRow r_main bus pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_input_r2_row h_lane_rd promises

end ZiskFv.Equivalence.Add
