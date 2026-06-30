import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.AeneasBridgeTrust.Base

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- Construct the MUL ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulOfExtractedShape
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMul)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.mul mul_input r1 r2 rd srs1 srs2 bus v r_a
    (MainRowProvenance.mulPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value

/-- The MUL bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulOfExtractedShape
    (mul_input : PureSpec.MulInput) (r1 r2 rd : regidx)
    (srs1 srs2 : Signedness)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMul)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mul_input.r1_val mul_input.r2_val mul_input.rd mul_input.PC
        (PureSpec.execute_MULH_mul_pure mul_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mul_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mul_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.mulOfExtractedShape
      mul_input r1 r2 rd srs1 srs2 bus v r_a provenance h_op h_external
      h_m32 h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULH ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulhOfExtractedShape
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulh mulh_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulHPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value

/-- The MULH bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulhOfExtractedShape
    (mulh_input : PureSpec.MulhInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
        (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.mulhOfExtractedShape
      mulh_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulhOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulHPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULHU ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulhuOfExtractedShape
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulhu mulhu_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulUHPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value

/-- The MULHU bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulhuOfExtractedShape
    (mulhu_input : PureSpec.MulhuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhu_input.r1_val mulhu_input.r2_val mulhu_input.rd mulhu_input.PC
        (PureSpec.execute_MULH_mulhu_pure mulhu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.mulhuOfExtractedShape
      mulhu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulhuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulUHPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULHSU ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulhsuOfExtractedShape
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulSUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhsu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhsu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulhsu mulhsu_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulSUHPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_rs1_value h_rs2_value

/-- The MULHSU bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulhsuOfExtractedShape
    (mulhsu_input : PureSpec.MulhsuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulSUH)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
        (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_rs1_value : mulhsu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.a_0 r_a).val (v.a_1 r_a).val
          (v.a_2 r_a).val (v.a_3 r_a).val)
    (h_rs2_value : mulhsu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.mulhsuOfExtractedShape
      mulhsu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulhsuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulSUHPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the MULW ArithMul-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.mulwOfExtractedShape
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    OpEnvelope state m r_main :=
  OpEnvelope.mulw mulw_input r1 r2 rd bus v r_a
    (MainRowProvenance.mulWPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_a23 h_b23 h_sext_choice
    h_rs1_value h_rs2_value

/-- The MULW bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithMul facts. -/
theorem OpEnvelope.aeneasBridgeTrust_mulwOfExtractedShape
    (mulw_input : PureSpec.MulwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opMulW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithMul.opBus_row_Arith v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state mulw_input.r1_val mulw_input.r2_val mulw_input.rd mulw_input.PC
        (PureSpec.execute_MULW_pure mulw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithMul.mul_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithMulTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithMulChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithMulSignedCarryRangeWitness v r_a)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.c_0 r_a).val + (v.c_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb mulw_input.r1_val 31 0).toInt
        = ((v.a_0 r_a).val + (v.a_1 r_a).val * 65536 : ℤ)
            - (v.na r_a).val * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb mulw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - (v.nb r_a).val * (2:ℤ)^32) :
    (OpEnvelope.mulwOfExtractedShape
      mulw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_a23 h_b23 h_sext_choice h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.mulwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.mulWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.mulControl_of_extracted_shape provenance h_m32 h_set_pc
      h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩


end ZiskFv.Compliance
