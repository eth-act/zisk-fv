import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.AeneasBridgeTrust.Base

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

def OpEnvelope.andiOfExtractedShape
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_input_r1_row : andi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 andi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_andi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.andi andi_input r1 rd imm v bus
    (MainRowProvenance.andPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row h_andi_subset h_lane_rd
    promises

theorem OpEnvelope.aeneasBridgeTrust_andiOfExtractedShape
    (andi_input : PureSpec.AndiInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_input_r1_row : andi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 andi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_andi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main andi_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state andi_input.r1_val andi_input.imm andi_input.rd andi_input.PC
        (PureSpec.execute_ITYPE_andi_pure andi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.andiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      andi_input r1 rd imm v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_andi_subset h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.andiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

def OpEnvelope.oriOfExtractedShape
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_input_r1_row : ori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 ori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_ori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.ori ori_input r1 rd imm v bus
    (MainRowProvenance.orPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row h_ori_subset h_lane_rd
    promises

theorem OpEnvelope.aeneasBridgeTrust_oriOfExtractedShape
    (ori_input : PureSpec.OriInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_input_r1_row : ori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 ori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_ori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main ori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state ori_input.r1_val ori_input.imm ori_input.rd ori_input.PC
        (PureSpec.execute_ITYPE_ori_pure ori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.oriOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      ori_input r1 rd imm v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_ori_subset h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.oriOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

def OpEnvelope.xoriOfExtractedShape
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_input_r1_row : xori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 xori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_xori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.xori xori_input r1 rd imm v bus
    (MainRowProvenance.xorPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_input_r1_row h_input_imm_row h_xori_subset h_lane_rd
    promises

theorem OpEnvelope.aeneasBridgeTrust_xoriOfExtractedShape
    (xori_input : PureSpec.XoriInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_input_r1_row : xori_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 xori_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_xori_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main xori_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state xori_input.r1_val xori_input.imm xori_input.rd xori_input.PC
        (PureSpec.execute_ITYPE_xori_pure xori_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.xoriOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      xori_input r1 rd imm v bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_input_r1_row h_input_imm_row h_xori_subset h_lane_rd promises).aeneasBridgeTrust := by
  unfold OpEnvelope.xoriOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

def OpEnvelope.sltiOfExtractedShape
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : slti_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_slti_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.slti slti_input r1 rd imm v bus
    (MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static
    (by simpa [boolF, h_m32_shape] using provenance.m32_eq)
    h_input_r1_row h_slti_subset h_lane_rd promises

theorem OpEnvelope.aeneasBridgeTrust_sltiOfExtractedShape
    (slti_input : PureSpec.SltiInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : slti_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_slti_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main slti_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state slti_input.r1_val slti_input.imm slti_input.rd slti_input.PC
        (PureSpec.execute_ITYPE_slti_pure slti_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slti_input r1 rd imm v bus provenance h_op h_external h_m32_shape
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_slti_subset h_lane_rd
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [boolF, h_m32_shape] using provenance.m32_eq, h_input_r1_row⟩

def OpEnvelope.sltiuOfExtractedShape
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : sltiu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_sltiu_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sltiu sltiu_input r1 rd imm v bus
    (MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static
    (by simpa [boolF, h_m32_shape] using provenance.m32_eq)
    h_input_r1_row h_sltiu_subset h_lane_rd promises

theorem OpEnvelope.aeneasBridgeTrust_sltiuOfExtractedShape
    (sltiu_input : PureSpec.SltiuInput) (r1 rd : regidx) (imm : BitVec 12)
    (v : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
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
    (h_input_r1_row : sltiu_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_sltiu_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main sltiu_input.imm)
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state sltiu_input.r1_val sltiu_input.imm sltiu_input.rd sltiu_input.PC
        (PureSpec.execute_ITYPE_sltiu_pure sltiu_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.sltiuOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sltiu_input r1 rd imm v bus provenance h_op h_external h_m32_shape
      providerTable providerRow h_component h_table_spec h_provider_row
      h_match_static h_input_r1_row h_sltiu_subset h_lane_rd
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.sltiuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨by simpa [boolF, h_m32_shape] using provenance.m32_eq, h_input_r1_row⟩


end ZiskFv.Compliance
