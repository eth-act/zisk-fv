import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.AeneasBridgeTrust.Base

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- Construct the ADD Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addViaBinaryOfExtractedShape
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAdd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
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
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.add_via_binary add_input r1 r2 rd bus
    (MainRowProvenance.addPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The ADD Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addViaBinaryOfExtractedShape
    (add_input : PureSpec.AddInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAdd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
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
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state add_input.r1_val add_input.r2_val add_input.rd add_input.PC
        (PureSpec.execute_RTYPE_add_pure add_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addViaBinaryOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      add_input r1 r2 rd bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addViaBinaryOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the ADDW Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addwOfExtractedShape
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_input_r2_extract :
      (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.addw addw_input r1 r2 rd v bus
    (MainRowProvenance.addwPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_extract h_input_r2_extract h_lane_rd promises

/-- The ADDW Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addwOfExtractedShape
    (addw_input : PureSpec.AddwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_input_r2_extract :
      (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state addw_input.r1_val addw_input.r2_val addw_input.rd addw_input.PC
        (PureSpec.execute_RTYPE_addw_pure addw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      addw_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_extract, h_input_r2_extract⟩

/-- Construct the SUBW Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.subwOfExtractedShape
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSubW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_input_r2_extract :
      (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.subw subw_input r1 r2 rd v bus
    (MainRowProvenance.subwPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_extract h_input_r2_extract h_lane_rd promises

/-- The SUBW Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_subwOfExtractedShape
    (subw_input : PureSpec.SubwInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSubW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_input_r2_extract :
      (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state subw_input.r1_val subw_input.r2_val subw_input.rd subw_input.PC
        (PureSpec.execute_RTYPE_subw_pure subw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.subwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      subw_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_extract h_input_r2_extract h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.subwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_extract, h_input_r2_extract⟩

/-- Construct the ADDIW Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addiwOfExtractedShape
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_addiw_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main addiw_input.imm)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.addiw addiw_input r1 rd imm v bus
    (MainRowProvenance.addwPins_of_extracted_shape provenance h_op h_external)
    h_addiw_subset providerTable providerRow h_component h_table_spec
    h_provider_row h_match_static h_input_r1_extract h_lane_rd promises

/-- The ADDIW Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addiwOfExtractedShape
    (addiw_input : PureSpec.AddiwInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAddW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_addiw_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main addiw_input.imm)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_extract :
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addiw_input.r1_val addiw_input.imm addiw_input.rd addiw_input.PC
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addiwOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      addiw_input r1 rd imm v bus provenance h_op h_external h_addiw_subset
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_extract h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addiwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact h_input_r1_extract

/-- Construct the SUB Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.subOfExtractedShape
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSub)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sub_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : sub_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sub sub_input r1 r2 rd v bus
    (MainRowProvenance.subPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The SUB Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_subOfExtractedShape
    (sub_input : PureSpec.SubInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSub)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sub_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : sub_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sub_input.r1_val sub_input.r2_val sub_input.rd sub_input.PC
        (PureSpec.execute_RTYPE_sub_pure sub_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.subOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sub_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.subOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the AND Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.andOfExtractedShape
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : and_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : and_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.and and_input r1 r2 rd v bus
    (MainRowProvenance.andPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The AND Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_andOfExtractedShape
    (and_input : PureSpec.AndInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : and_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : and_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state and_input.r1_val and_input.r2_val and_input.rd and_input.PC
        (PureSpec.execute_RTYPE_and_pure and_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.andOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      and_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.andOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the OR Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.orOfExtractedShape
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opOr)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : or_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : or_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.or or_input r1 r2 rd v bus
    (MainRowProvenance.orPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The OR Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_orOfExtractedShape
    (or_input : PureSpec.OrInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opOr)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : or_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : or_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state or_input.r1_val or_input.r2_val or_input.rd or_input.PC
        (PureSpec.execute_RTYPE_or_pure or_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.orOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      or_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.orOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the XOR Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.xorOfExtractedShape
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opXor)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : xor_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : xor_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
        (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.xor xor_input r1 r2 rd v bus
    (MainRowProvenance.xorPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The XOR Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_xorOfExtractedShape
    (xor_input : PureSpec.XorInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opXor)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : xor_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : xor_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state xor_input.r1_val xor_input.r2_val xor_input.rd xor_input.PC
        (PureSpec.execute_RTYPE_xor_pure xor_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.xorOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      xor_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.xorOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the SLT Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.sltOfExtractedShape
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : slt_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : slt_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state slt_input.r1_val slt_input.r2_val slt_input.rd slt_input.PC
        (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.slt slt_input r1 r2 rd v bus
    (MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The SLT Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sltOfExtractedShape
    (slt_input : PureSpec.SltInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : slt_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : slt_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state slt_input.r1_val slt_input.r2_val slt_input.rd slt_input.PC
        (PureSpec.execute_RTYPE_slt_pure slt_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slt_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩

/-- Construct the SLTU Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.sltuOfExtractedShape
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sltu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : sltu_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sltu_input.r1_val sltu_input.r2_val sltu_input.rd sltu_input.PC
        (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sltu sltu_input r1 r2 rd v bus
    (MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_r2_row h_lane_rd promises

/-- The SLTU Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_sltuOfExtractedShape
    (sltu_input : PureSpec.SltuInput) (r1 r2 rd : regidx)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (h_component :
      providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_table_spec : providerTable.Spec)
    (h_provider_row : providerRow ∈ providerTable.table)
    (h_match_static : ZiskFv.Airs.OperationBus.matches_entry
      (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))) 1))
    (h_input_r1_row : sltu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_r2_row : sltu_input.r2_val =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sltu_input.r1_val sltu_input.r2_val sltu_input.rd sltu_input.PC
        (PureSpec.execute_RTYPE_sltu_pure sltu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sltu_input r1 r2 rd v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_r2_row h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_r2_row⟩


end ZiskFv.Compliance
