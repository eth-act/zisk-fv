import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.AeneasBridgeTrust.Base

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- Construct the BEQ branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.beqOfExtractedShape
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.beq beq_input ops promises

/-- The BEQ bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_beqOfExtractedShape
    (beq_input : PureSpec.BeqInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
        ops.misa_val
        (PureSpec.execute_BEQ_pure beq_input).nextPC
        (PureSpec.execute_BEQ_pure beq_input).throws
        (PureSpec.execute_BEQ_pure beq_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.beqOfExtractedShape
      beq_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset2 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.beqOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.eqPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset2_of_extracted_shape provenance h_jmp_offset2⟩

/-- Construct the BNE branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bneOfExtractedShape
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bne bne_input ops promises

/-- The BNE bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bneOfExtractedShape
    (bne_input : PureSpec.BneInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opEq)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
        ops.misa_val
        (PureSpec.execute_BNE_pure bne_input).nextPC
        (PureSpec.execute_BNE_pure bne_input).throws
        (PureSpec.execute_BNE_pure bne_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bneOfExtractedShape
      bne_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset1 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bneOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.eqPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset1_of_extracted_shape provenance h_jmp_offset1⟩

/-- Construct the BLT branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bltOfExtractedShape
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.blt blt_input ops promises

/-- The BLT bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bltOfExtractedShape
    (blt_input : PureSpec.BltInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
        ops.misa_val
        (PureSpec.execute_BLT_pure blt_input).nextPC
        (PureSpec.execute_BLT_pure blt_input).throws
        (PureSpec.execute_BLT_pure blt_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bltOfExtractedShape
      blt_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset2 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bltOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset2_of_extracted_shape provenance h_jmp_offset2⟩

/-- Construct the BGE branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bgeOfExtractedShape
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bge bge_input ops promises

/-- The BGE bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bgeOfExtractedShape
    (bge_input : PureSpec.BgeInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLt)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
        ops.misa_val
        (PureSpec.execute_BGE_pure bge_input).nextPC
        (PureSpec.execute_BGE_pure bge_input).throws
        (PureSpec.execute_BGE_pure bge_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bgeOfExtractedShape
      bge_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset1 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bgeOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset1_of_extracted_shape provenance h_jmp_offset1⟩

/-- Construct the BLTU branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bltuOfExtractedShape
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bltu bltu_input ops promises

/-- The BLTU bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bltuOfExtractedShape
    (bltu_input : PureSpec.BltuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
        ops.misa_val
        (PureSpec.execute_BLTU_pure bltu_input).nextPC
        (PureSpec.execute_BLTU_pure bltu_input).throws
        (PureSpec.execute_BLTU_pure bltu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bltuOfExtractedShape
      bltu_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset2 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bltuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset2_of_extracted_shape provenance h_jmp_offset2⟩

/-- Construct the BGEU branch envelope while deriving its branch row-shape facts
from extracted-row equalities. -/
def OpEnvelope.bgeuOfExtractedShape
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (_h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (_h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    OpEnvelope state m r_main :=
  OpEnvelope.bgeu bgeu_input ops promises

/-- The BGEU bridge predicate is derivable from extracted branch row-shape
equalities. -/
theorem OpEnvelope.aeneasBridgeTrust_bgeuOfExtractedShape
    (bgeu_input : PureSpec.BgeuInput)
    (ops : ZiskFv.Compliance.BranchInstrOperands)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opLtu)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (promises : ZiskFv.EquivCore.Promises.BranchPromises
        state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
        ops.misa_val
        (PureSpec.execute_BGEU_pure bgeu_input).nextPC
        (PureSpec.execute_BGEU_pure bgeu_input).throws
        (PureSpec.execute_BGEU_pure bgeu_input).success
        ops.imm ops.r1 ops.r2 ops.exec_row) :
    (OpEnvelope.bgeuOfExtractedShape
      bgeu_input ops provenance h_op h_external h_m32 h_set_pc h_store_pc
      h_jmp_offset1 promises).aeneasBridgeTrust := by
  unfold OpEnvelope.bgeuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.ltuPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.branchControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2,
    MainRowProvenance.jmpOffset1_of_extracted_shape provenance h_jmp_offset1⟩


end ZiskFv.Compliance
