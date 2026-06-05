import ZiskFv.Compliance.Wrappers.ShiftR
import ZiskFv.Channels.StateEffect

/-!
# `equiv_SRLW` per-opcode canonical theorem (channel-balance form)

Post-Phase-6 canonical per-opcode theorem for SRLW. Proves the
channel-balance conclusion (`= state_effect_via_channels …`) by
invoking the corresponding wrapper theorem `ZiskFv.Compliance.equiv_SRLW`.

The pre-cutover v1 form (`= (bus_effect …).2`) lives at
`ZiskFv/EquivCore/Srlw.lean`.

## Trust note

No new axioms. The axiom closure equals `ZiskFv.Compliance.equiv_SRLW`'s closure exactly.
-/

open ZiskFv.Channels
open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.BinaryExtension (Valid_BinaryExtension)
open ZiskFv.Trusted (OP_SLL_W OP_SRL_W OP_SRA_W)

namespace ZiskFv.Equivalence.Srlw


theorem equiv_SRLW
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (srlw_input : PureSpec.SrlwInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
      state srlw_input.r1_val srlw_input.r2_val srlw_input.rd srlw_input.PC
      (PureSpec.execute_RTYPE_srlw_pure srlw_input).nextPC
      r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_SRL_W)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row :
      (Sail.BitVec.extractLsb srlw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat =
        ZiskFv.AirsClean.BinaryExtension.rowA32
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow)))
    (h_shift_pin_row : srlw_input.r2_val.toNat % 32 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount32
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    : execute_instruction (instruction.RTYPEW (r2, r1, rd, ropw.SRLW)) state
      = state_effect_via_channels ⟨bus.exec_row, [bus.e0, bus.e1, bus.e2]⟩ state := by
  rw [ZiskFv.Channels.state_effect_via_channels_eq_bus_effect_2]
  exact ZiskFv.Compliance.equiv_SRLW state srlw_input r1 r2 rd
    m providerTable providerRow r_main bus
    promises pins
    h_component h_table_spec h_provider_row h_match
    h_input_r1_row h_shift_pin_row h_lane_rd

-- equiv_<OP>_of_static_lookup (noncanonical alt route) deleted in T4-purge step P3.1.

end ZiskFv.Equivalence.Srlw
