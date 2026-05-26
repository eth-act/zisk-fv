import ZiskFv.Compliance.Wrappers.Slli
import ZiskFv.Channels.StateEffect

/-!
# `equiv_SLLI` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SLLI. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SLLI`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Slli.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SLLI`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SLL)

namespace ZiskFv.Equivalence.Slli


theorem equiv_SLLI
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slli_input : PureSpec.SlliInput)
    (r1 rd : regidx) (shamt : BitVec 6)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SLL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.SHIFTIOP (shamt, r1, rd, sop.SLLI)) state
      = state_effect_via_channels
          ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SLLI state slli_input r1 rd shamt
    m providerTable providerRow r_main bus promises pins
    h_component h_table_spec h_provider_row h_match h_lane_rd

-- equiv_<OP>_of_static_lookup (noncanonical alt route) deleted in T4-purge step P3.1.

end ZiskFv.Equivalence.Slli
