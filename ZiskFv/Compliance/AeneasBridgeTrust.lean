import ZiskFv.Compliance.OpEnvelope

/-!
# Explicit Aeneas bridge trust

The main Lake proof does not yet import generated Aeneas Lean and derive every
row-provenance/source-lane field from the extracted production lowerer.  The
corresponding facts are carried by `OpEnvelope` constructors as ordinary proof
fields.  This file records that gap as an explicit trust axiom, so the global
theorem's axiom closure names the Aeneas bridge boundary instead of leaving it
only in caller-burden ledgers.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- The Aeneas-backed row-lowering facts currently carried by `OpEnvelope`.

This predicate makes the representative bridge facts that replaced the retired
hand-written Lean transpiler visible in the global theorem's trusted surface.
The existing wrappers still take their full proof-field parameter lists, so the
caller-burden ledgers remain the mechanical inventory of fields that a later
wrapper refactor can remove. -/
def OpEnvelope.aeneasBridgeTrust : OpEnvelope state m r_main → Prop
  | .lui _ imm _ _ _ _ _ provenance _ _ _ _ _ =>
      Nonempty (MainRowProvenance m r_main)
      ∧ MainRowProvenance.LuiRowMode provenance
      ∧ (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat
      ∧ (m.b_1 r_main).val
          = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296
  | .auipc auipc_input _ _ _ _ _ _ _ provenance _ _ _ _ _ _ _ =>
      Nonempty (MainRowProvenance m r_main)
      ∧ MainRowProvenance.AuipcRowMode provenance
      ∧ (m.jmp_offset2 r_main).val
          = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
      ∧ (m.pc r_main).val = auipc_input.PC.toNat
  | .jal jal_input _ _ _ _ _ _ _ _ provenance _ _ _ _ _ _ _ _ _ =>
      Nonempty (MainRowProvenance m r_main)
      ∧ MainRowProvenance.JalRowMode provenance
      ∧ m.jmp_offset2 r_main = 4
      ∧ (m.pc r_main).val = jal_input.PC.toNat
  | .jalr jalr_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      m.flag r_main = 0
      ∧ m.m32 r_main = 0
      ∧ m.set_pc r_main = 1
      ∧ m.store_pc r_main = 1
      ∧ (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat
  | .add_via_binary add_input _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      add_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ add_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .addi_via_binary addi_input _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      addi_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 addi_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .addw addw_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      (Sail.BitVec.extractLsb addw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
      ∧ (Sail.BitVec.extractLsb addw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
  | .subw subw_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      (Sail.BitVec.extractLsb subw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
      ∧ (Sail.BitVec.extractLsb subw_input.r2_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowB32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
  | .addiw addiw_input _ _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ =>
      (Sail.BitVec.extractLsb addiw_input.r1_val 31 0 : BitVec (31 - 0 + 1)).toNat
        = ZiskFv.EquivCore.Addw.binaryRowA32
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow)) % 2^32
  | .sub sub_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      sub_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sub_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .and and_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      and_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ and_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .or or_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      or_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ or_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .xor xor_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      xor_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ xor_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slt slt_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      slt_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ slt_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sltu sltu_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ =>
      sltu_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sltu_input.r2_val =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .andi andi_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      andi_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 andi_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .ori ori_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      ori_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 ori_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .xori xori_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      xori_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ BitVec.signExtend 64 xori_input.imm =
        ZiskFv.EquivCore.Add.binaryRowB64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slti slti_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      m.m32 r_main = 0
      ∧ slti_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sltiu sltiu_input _ _ _ _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ =>
      m.m32 r_main = 0
      ∧ sltiu_input.r1_val =
        ZiskFv.EquivCore.Add.binaryRowA64
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sll sll_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      sll_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sll_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srl srl_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      srl_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srl_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .sra sra_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      sra_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ sra_input.r2_val.toNat % 64 =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .slli slli_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      slli_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ slli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srli srli_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      srli_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srli_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | .srai srai_input _ _ _ providerTable providerRow _ _ _ _ _ _ _ _ _ _ =>
      srai_input.r1_val =
        ZiskFv.AirsClean.BinaryExtension.rowA64
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
      ∧ srai_input.shamt.toNat =
        ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (providerTable.environment providerRow))
  | _ => True

/-- Construct the LUI envelope while deriving its row-mode field from
production-extracted row-shape equalities. -/
def OpEnvelope.luiOfExtractedShape
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_lui_subset : ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    OpEnvelope state m r_main :=
  OpEnvelope.lui lui_input imm rd next_pc exec_row e_rd store_pc_mem provenance
    (MainRowProvenance.luiRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc)
    h_lui_subset h_imm_lo_nat h_imm_hi_nat promises

/-- The LUI bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic LUI facts. -/
theorem OpEnvelope.aeneasBridgeTrust_luiOfExtractedShape
    (lui_input : PureSpec.LuiInput)
    (imm : BitVec 20) (rd : regidx) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opCopyB)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_lui_subset : ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m r_main next_pc)
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state lui_input.imm lui_input.rd lui_input.PC
        (PureSpec.execute_LUI_pure lui_input).nextPC
        imm rd exec_row e_rd (lui_input.PC + 4#64)) :
    (OpEnvelope.luiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      lui_input imm rd next_pc exec_row e_rd store_pc_mem provenance
      h_op h_internal h_m32 h_set_pc h_store_pc
      h_lui_subset h_imm_lo_nat h_imm_hi_nat promises).aeneasBridgeTrust := by
  unfold OpEnvelope.luiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨⟨provenance⟩,
    MainRowProvenance.luiRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc,
    h_imm_lo_nat,
    h_imm_hi_nat⟩

/-- Construct the AUIPC envelope while deriving its row-mode field from
production-extracted row-shape equalities. -/
def OpEnvelope.auipcOfExtractedShape
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_auipc_subset : ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m r_main next_pc)
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_pc_bridge : (m.pc r_main).val = auipc_input.PC.toNat)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    OpEnvelope state m r_main :=
  OpEnvelope.auipc auipc_input imm rd exec_row e_rd nextPC_val next_pc
    store_pc_mem provenance
    (MainRowProvenance.auipcRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc)
    h_auipc_subset h_offset_bridge h_pc_bridge promises
    h_no_wrap h_pc_offset_lt_2_32

/-- The AUIPC bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic AUIPC facts. -/
theorem OpEnvelope.aeneasBridgeTrust_auipcOfExtractedShape
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20) (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_auipc_subset : ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m r_main next_pc)
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat)
    (h_pc_bridge : (m.pc r_main).val = auipc_input.PC.toNat)
    (promises : ZiskFv.EquivCore.Promises.UTypePromises
        state auipc_input.imm auipc_input.rd auipc_input.PC
        (PureSpec.execute_AUIPC_pure auipc_input).nextPC
        imm rd exec_row e_rd nextPC_val)
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    (OpEnvelope.auipcOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      auipc_input imm rd exec_row e_rd nextPC_val next_pc
      store_pc_mem provenance
      h_op h_internal h_m32 h_set_pc h_store_pc
      h_auipc_subset h_offset_bridge h_pc_bridge promises
      h_no_wrap h_pc_offset_lt_2_32).aeneasBridgeTrust := by
  unfold OpEnvelope.auipcOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨⟨provenance⟩,
    MainRowProvenance.auipcRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc,
    h_offset_bridge,
    h_pc_bridge⟩

/-- Construct the JAL envelope while deriving its row-mode field from
production-extracted row-shape equalities. -/
def OpEnvelope.jalOfExtractedShape
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_pc_bridge : (m.pc r_main).val = jal_input.PC.toNat)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    OpEnvelope state m r_main :=
  OpEnvelope.jal jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
    store_pc_mem provenance
    (MainRowProvenance.jalRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc)
    h_jal_subset h_jmp2 h_pc_bridge promises h_input_imm h_not_throws
    h_pc_bound h_pc_offset_lt_2_32

/-- The JAL bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic JAL facts. -/
theorem OpEnvelope.aeneasBridgeTrust_jalOfExtractedShape
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21) (rd : regidx)
    (misa_val : RegisterType Register.misa)
    (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = true)
    (h_jal_subset : ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_pc_bridge : (m.pc r_main).val = jal_input.PC.toNat)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jal_input.PC jal_input.rd misa_val
        (PureSpec.execute_JAL_pure jal_input).success
        (PureSpec.execute_JAL_pure jal_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jal_input.imm = imm)
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    (OpEnvelope.jalOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      jal_input imm rd misa_val next_pc exec_row e_rd nextPC_val
      store_pc_mem provenance
      h_op h_internal h_m32 h_set_pc h_store_pc
      h_jal_subset h_jmp2 h_pc_bridge promises h_input_imm h_not_throws
      h_pc_bound h_pc_offset_lt_2_32).aeneasBridgeTrust := by
  unfold OpEnvelope.jalOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨⟨provenance⟩,
    MainRowProvenance.jalRowMode_of_extracted_shape provenance
      h_op h_internal h_m32 h_set_pc h_store_pc,
    h_jmp2,
    h_pc_bridge⟩

/-- Construct the JALR envelope while deriving its final-row activation,
opcode, and control pins from production-extracted row-shape equalities. -/
def OpEnvelope.jalrOfExtractedShape
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
    (h_set_pc_shape : provenance.extractedRow.setPc = true)
    (h_store_pc_shape : provenance.extractedRow.storePc = true)
    (h_flag : m.flag r_main = 0)
    (h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m r_main
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m r_main
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r_main
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jalr_input.PC jalr_input.rd misa_val
        (PureSpec.execute_JALR_pure jalr_input).success
        (PureSpec.execute_JALR_pure jalr_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_link_bridge :
      (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    OpEnvelope state m r_main :=
  let control := MainRowProvenance.jalrControl_of_extracted_shape provenance
    h_m32_shape h_set_pc_shape h_store_pc_shape
  OpEnvelope.jalr jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd
    nextPC_val next_pc store_pc_mem
    (MainRowProvenance.jalrPins_of_extracted_shape provenance h_op h_external)
    h_flag control.1 control.2.1 control.2.2 h_jalr_subset promises
    h_input_imm h_input_rs1 h_cur_privilege h_mseccfg h_link_bridge h_pc_bound
    h_pc_offset_lt_2_32

/-- The JALR bridge predicate is derivable for the envelope constructed from
extracted row-shape equalities and the remaining dynamic JALR facts. -/
theorem OpEnvelope.aeneasBridgeTrust_jalrOfExtractedShape
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12) (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL) (nextPC_val : BitVec 64)
    (next_pc : FGL)
    (store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m r_main e_rd)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opAnd)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32_shape : provenance.extractedRow.m32 = false)
    (h_set_pc_shape : provenance.extractedRow.setPc = true)
    (h_store_pc_shape : provenance.extractedRow.storePc = true)
    (h_flag : m.flag r_main = 0)
    (h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m r_main
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m r_main
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m r_main
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m r_main next_pc)
    (promises : ZiskFv.EquivCore.Promises.JumpPromises
        state jalr_input.PC jalr_input.rd misa_val
        (PureSpec.execute_JALR_pure jalr_input).success
        (PureSpec.execute_JALR_pure jalr_input).nextPC
        rd exec_row e_rd nextPC_val)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    (h_link_bridge :
      (m.pc r_main + m.jmp_offset2 r_main).val = (jalr_input.PC + 4#64).toNat)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (OpEnvelope.jalrOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      jalr_input imm rs1 rd misa_val mseccfg exec_row e_rd nextPC_val next_pc
      store_pc_mem provenance
      h_op h_external h_m32_shape h_set_pc_shape h_store_pc_shape
      h_flag h_jalr_subset promises h_input_imm h_input_rs1 h_cur_privilege
      h_mseccfg h_link_bridge h_pc_bound h_pc_offset_lt_2_32).aeneasBridgeTrust := by
  let control := MainRowProvenance.jalrControl_of_extracted_shape provenance
    h_m32_shape h_set_pc_shape h_store_pc_shape
  unfold OpEnvelope.jalrOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_flag, control.1, control.2.1, control.2.2, h_link_bridge⟩

/-- Construct the FENCE envelope while deriving its activation/opcode pins from
production-extracted row-shape equalities. -/
def OpEnvelope.fenceOfExtractedShape
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.fence fence_input fm pred succ rs rd exec_row
    (MainRowProvenance.fencePins_of_extracted_shape provenance h_op h_internal)
    promises

/-- The FENCE bridge predicate is trivial, but this theorem records that the
real FENCE envelope pins can be filled from extracted row-shape equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape
    (fence_input : PureSpec.FenceInput)
    (fm pred succ : BitVec 4) (rs rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opFlag)
    (h_internal : provenance.extractedRow.isExternalOp = false)
    (promises : ZiskFv.EquivCore.Promises.FencePromises
        state fence_input.PC
        (PureSpec.execute_FENCE_pure fence_input).nextPC
        exec_row) :
    (OpEnvelope.fenceOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      fence_input fm pred succ rs rd exec_row provenance h_op h_internal
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.fenceOfExtractedShape OpEnvelope.aeneasBridgeTrust
  trivial

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

/-- Construct the ADDI Binary-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.addiViaBinaryOfExtractedShape
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_addi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main addi_input.imm)
    (h_input_r1_row : addi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 addi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.addi_via_binary addi_input r1 rd imm bus
    (MainRowProvenance.addPins_of_extracted_shape provenance h_op h_external)
    providerTable providerRow h_component h_table_spec h_provider_row
    h_match_static h_addi_subset h_input_r1_row h_input_imm_row h_lane_rd
    promises

/-- The ADDI Binary-provider bridge predicate is derivable for the envelope
constructed from extracted row-shape pins and provider source-lane facts. -/
theorem OpEnvelope.aeneasBridgeTrust_addiViaBinaryOfExtractedShape
    (addi_input : PureSpec.AddiInput) (r1 rd : regidx) (imm : BitVec 12)
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
    (h_addi_subset : ZiskFv.Tactics.ALUITypeArchetype.itype_imm_subset_holds_main
      m r_main addi_input.imm)
    (h_input_r1_row : addi_input.r1_val =
      ZiskFv.EquivCore.Add.binaryRowA64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_input_imm_row : BitVec.signExtend 64 addi_input.imm =
      ZiskFv.EquivCore.Add.binaryRowB64
        (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2)
    (promises : ZiskFv.EquivCore.Promises.ITypePromises
        state addi_input.r1_val addi_input.imm addi_input.rd addi_input.PC
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        r1 rd imm bus.exec_row bus.e0 bus.e1 bus.e2) :
    (OpEnvelope.addiViaBinaryOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      addi_input r1 rd imm bus provenance h_op h_external providerTable
      providerRow h_component h_table_spec h_provider_row h_match_static
      h_addi_subset h_input_r1_row h_input_imm_row h_lane_rd
      promises).aeneasBridgeTrust := by
  unfold OpEnvelope.addiViaBinaryOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_input_imm_row⟩

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

def OpEnvelope.sllOfExtractedShape
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : sll_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sll_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sll sll_input r1 r2 rd providerTable providerRow bus promises
    (MainRowProvenance.sllPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sllOfExtractedShape
    (sll_input : PureSpec.SllInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sll_input.r1_val sll_input.r2_val sll_input.rd sll_input.PC
        (PureSpec.execute_RTYPE_sll_pure sll_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : sll_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sll_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (OpEnvelope.sllOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sll_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sllOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srlOfExtractedShape
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : srl_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srl_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.srl srl_input r1 r2 rd providerTable providerRow bus promises
    (MainRowProvenance.srlPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srlOfExtractedShape
    (srl_input : PureSpec.SrlInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state srl_input.r1_val srl_input.r2_val srl_input.rd srl_input.PC
        (PureSpec.execute_RTYPE_srl_pure srl_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : srl_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srl_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (OpEnvelope.srlOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srl_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srlOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.sraOfExtractedShape
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : sra_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sra_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.sra sra_input r1 r2 rd providerTable providerRow bus promises
    (MainRowProvenance.sraPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sraOfExtractedShape
    (sra_input : PureSpec.SraInput) (r1 r2 rd : regidx)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state sra_input.r1_val sra_input.r2_val sra_input.rd sra_input.PC
        (PureSpec.execute_RTYPE_sra_pure sra_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : sra_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : sra_input.r2_val.toNat % 64 =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (OpEnvelope.sraOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      sra_input r1 r2 rd providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sraOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.slliOfExtractedShape
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : slli_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : slli_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.slli slli_input r1 rd shamt providerTable providerRow bus promises
    (MainRowProvenance.sllPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_slliOfExtractedShape
    (slli_input : PureSpec.SlliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSll)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state slli_input.r1_val slli_input.shamt slli_input.rd slli_input.PC
        (PureSpec.execute_SHIFTIOP_slli_pure slli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : slli_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : slli_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (OpEnvelope.slliOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      slli_input r1 rd shamt providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.slliOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.srliOfExtractedShape
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : srli_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srli_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.srli srli_input r1 rd shamt providerTable providerRow bus promises
    (MainRowProvenance.srlPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_srliOfExtractedShape
    (srli_input : PureSpec.SrliInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSrl)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srli_input.r1_val srli_input.shamt srli_input.rd srli_input.PC
        (PureSpec.execute_SHIFTIOP_srli_pure srli_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : srli_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srli_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (OpEnvelope.srliOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srli_input r1 rd shamt providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.srliOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

def OpEnvelope.sraiOfExtractedShape
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : srai_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srai_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    OpEnvelope state m r_main :=
  OpEnvelope.srai srai_input r1 rd shamt providerTable providerRow bus promises
    (MainRowProvenance.sraPins_of_extracted_shape provenance h_op h_external)
    h_component h_table_spec h_provider_row h_match h_input_r1_row
    h_shift_pin_row h_lane_rd

theorem OpEnvelope.aeneasBridgeTrust_sraiOfExtractedShape
    (srai_input : PureSpec.SraiInput) (r1 rd : regidx) (shamt : BitVec 6)
    (providerTable : Air.Flat.Table FGL)
    (providerRow : Array FGL)
    (bus : ZiskFv.Compliance.BusRows)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opSra)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (promises : ZiskFv.EquivCore.Promises.ShiftImmPromises
        state srai_input.r1_val srai_input.shamt srai_input.rd srai_input.PC
        (PureSpec.execute_SHIFTIOP_srai_pure srai_input).nextPC
        r1 rd shamt bus.exec_row bus.e0 bus.e1 bus.e2)
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
    (h_input_r1_row : srai_input.r1_val =
      ZiskFv.AirsClean.BinaryExtension.rowA64
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_shift_pin_row : srai_input.shamt.toNat =
      ZiskFv.AirsClean.BinaryExtension.rowShiftAmount
        (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
          (providerTable.environment providerRow)))
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main bus.e2) :
    (OpEnvelope.sraiOfExtractedShape
      (state := state) (m := m) (r_main := r_main)
      srai_input r1 rd shamt providerTable providerRow bus provenance h_op
      h_external promises h_component h_table_spec h_provider_row h_match
      h_input_r1_row h_shift_pin_row h_lane_rd).aeneasBridgeTrust := by
  unfold OpEnvelope.sraiOfExtractedShape OpEnvelope.aeneasBridgeTrust
  exact ⟨h_input_r1_row, h_shift_pin_row⟩

/-- **Aeneas row-lowering bridge trust axiom.**

The generated Aeneas extraction is checked in CI, but generated Aeneas Lean is
not yet imported to prove these bridge facts inside the main Lake theorem. -/
axiom aeneas_bridge_trust
    (env : OpEnvelope state m r_main) :
    env.aeneasBridgeTrust

end ZiskFv.Compliance
