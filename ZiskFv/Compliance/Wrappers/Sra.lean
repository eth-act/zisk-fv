import Mathlib

import ZiskFv.EquivCore.Sra
import ZiskFv.EquivCore.Promises.RType
import ZiskFv.EquivCore.Promises.BinaryExtensionHelpers
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.AirsClean.BinaryFamily.Balance
import ZiskFv.Compliance.SharedBundles

/-! `equiv_SRA` Compliance wrapper — BinaryExtension (signed shift,
    OP_SRA = 0x23). RTYPE form. The signed-vs-unsigned distinction
    is handled inside the canonical theorem via the BinaryExtension
    AIR's op-routed semantics; no extra sign-witness pin needed at
    the wrapper level — `op_bus_perm_sound_BinaryExtension`'s
    disjunction member is enough. -/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises


lemma equiv_SRA
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (sra_input : PureSpec.SraInput)
    (r1 r2 rd : regidx)
    (m : Valid_Main FGL FGL)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (r_main : ℕ)
    (bus : ZiskFv.Compliance.BusRows)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 ZiskFv.Trusted.OP_SRA)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sra_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sra_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    execute_instruction (instruction.RTYPE (r2, r1, rd, rop.SRA)) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  let row :=
    ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
      (providerTable.environment providerRow)
  have h_shift_facts :=
    ZiskFv.AirsClean.BinaryFamily.shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
      h_component h_table_spec h_provider_row
  exact ZiskFv.EquivCore.Sra.equiv_SRA_of_static_row state sra_input r1 r2 rd
    m row r_main bus promises pins h_match h_shift_facts.1
    (by simpa [row] using h_input_r1_row)
    (by simpa [row] using h_shift_pin_row)
    h_shift_facts.2 h_lane_rd

-- equiv_<OP>_of_static_lookup (alt route, op_bus_perm_sound) deleted in T4-purge P3.2.

end ZiskFv.Compliance
