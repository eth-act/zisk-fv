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

/-- **Aeneas row-lowering bridge trust axiom.**

The generated Aeneas extraction is checked in CI, but generated Aeneas Lean is
not yet imported to prove these bridge facts inside the main Lake theorem. -/
axiom aeneas_bridge_trust
    (env : OpEnvelope state m r_main) :
    env.aeneasBridgeTrust

end ZiskFv.Compliance
