import ZiskFv.Compliance.OpEnvelope
import ZiskFv.Compliance.AeneasBridgeTrust.Base

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Airs.Main (Valid_Main)

variable {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
variable {m : Valid_Main FGL FGL} {r_main : Nat}

/-- Construct the DIV ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divOfExtractedShape
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDiv)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.div div_input r1 r2 rd bus v r_a
    (MainRowProvenance.divPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints h_boundary
    arith_table arith_chunk_ranges arith_carry_ranges
    h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
    h_r_le h_r_sign

/-- The DIV bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divOfExtractedShape
    (div_input : PureSpec.DivInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDiv)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state div_input.r1_val div_input.r2_val div_input.rd div_input.PC
        (PureSpec.execute_DIVREM_div_pure div_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ div_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt) :
    (OpEnvelope.divOfExtractedShape
      div_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints h_boundary arith_table
      arith_chunk_ranges arith_carry_ranges
      h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
      h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.divOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIVU ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divuOfExtractedShape
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : divu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : divu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.divu divu_input r1 r2 rd bus v r_a
    (MainRowProvenance.divUPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_rs1_value h_rs2_value

/-- The DIVU bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divuOfExtractedShape
    (divu_input : PureSpec.DivuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divu_input.r1_val divu_input.r2_val divu_input.rd divu_input.PC
        (PureSpec.execute_DIVREM_divu_pure divu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : divu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : divu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.divuOfExtractedShape
      divu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.divuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divUPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIVW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divwOfExtractedShape
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.divw divw_input r1 r2 rd bus v r_a
    (MainRowProvenance.divWPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints h_boundary arith_table
    arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
    h_rs1_value h_rs2_value h_r_le h_r_sign

/-- The DIVW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divwOfExtractedShape
    (divw_input : PureSpec.DivwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divw_input.r1_val divw_input.r2_val divw_input.rd divw_input.PC
        (PureSpec.execute_DIVREM_divw_pure divw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_boundary :
      ZiskFv.Airs.ArithDiv.div_boundary_constraints v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
          ≤ (Sail.BitVec.extractLsb divw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb divw_input.r1_val 31 0).toInt) :
    (OpEnvelope.divwOfExtractedShape
      divw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary
      promises arith_mem bounds h_row_constraints h_boundary arith_table arith_chunk_ranges
      arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
      h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
      h_rs1_value h_rs2_value h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.divwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the DIVUW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.divuwOfExtractedShape
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    OpEnvelope state m r_main :=
  OpEnvelope.divuw divuw_input r1 r2 rd bus v r_a
    (MainRowProvenance.divUWPins_of_extracted_shape provenance h_op h_external)
    h_match_primary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_b23 h_c23
    h_sext_choice h_rs1_value h_rs2_value

/-- The DIVUW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_divuwOfExtractedShape
    (divuw_input : PureSpec.DivuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opDivUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_primary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state divuw_input.r1_val divuw_input.r2_val divuw_input.rd divuw_input.PC
        (PureSpec.execute_DIVREM_divuw_pure divuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb divuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb divuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (OpEnvelope.divuwOfExtractedShape
      divuw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_primary promises
      arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_b23 h_c23 h_sext_choice h_rs1_value
      h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.divuwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.divUWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REM ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remOfExtractedShape
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRem)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      rem_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      rem_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ rem_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * rem_input.r1_val.toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.rem rem_input r1 r2 rd bus v r_a
    (MainRowProvenance.remPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints
    arith_table arith_chunk_ranges arith_carry_ranges
    h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
    h_r_le h_r_sign

/-- The REM bridge predicate is derivable from extracted row-shape equalities
and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remOfExtractedShape
    (rem_input : PureSpec.RemInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRem)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state rem_input.r1_val rem_input.r2_val rem_input.rd rem_input.PC
        (PureSpec.execute_DIVREM_rem_pure rem_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ (ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_0 r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_1 r_a) * 65536
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_2 r_a) * (65536 * 65536)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.a_3 r_a)
                * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_rs1_value :
      rem_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_rs2_value :
      rem_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64)
    (h_r_le :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs ≤ rem_input.r2_val.toInt.natAbs)
    (h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * rem_input.r1_val.toInt) :
    (OpEnvelope.remOfExtractedShape
      rem_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary promises
      arith_mem bounds h_row_constraints arith_table
      arith_chunk_ranges arith_carry_ranges h_na_bool
      h_nb_bool h_nr_bool h_np_xor h_nr_pin h_rs1_value h_rs2_value
      h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.remOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REMU ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remuOfExtractedShape
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = false)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    OpEnvelope state m r_main :=
  OpEnvelope.remu remu_input r1 r2 rd bus v r_a
    (MainRowProvenance.remUPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_rs1_value h_rs2_value

/-- The REMU bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remuOfExtractedShape
    (remu_input : PureSpec.RemuInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemU)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = false)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_rs1_value : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.c_0 r_a).val (v.c_1 r_a).val
          (v.c_2 r_a).val (v.c_3 r_a).val)
    (h_rs2_value : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (v.b_0 r_a).val (v.b_1 r_a).val
          (v.b_2 r_a).val (v.b_3 r_a).val) :
    (OpEnvelope.remuOfExtractedShape
      remu_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_rs1_value h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.remuOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remUPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REMW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remwOfExtractedShape
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt) :
    OpEnvelope state m r_main :=
  OpEnvelope.remw remw_input r1 r2 rd bus v r_a
    (MainRowProvenance.remWPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
    h_rs1_value h_rs2_value h_r_le h_r_sign

/-- The REMW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remwOfExtractedShape
    (remw_input : PureSpec.RemwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remw_input.r1_val remw_input.r2_val remw_input.rd remw_input.PC
        (PureSpec.execute_DIVREM_remw_pure remw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges : ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
            + ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a)
            - 2 * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.na r_a)
              * ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a))
    (h_nr_pin :
      ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a)
          = ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a)
        ∨ ((v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0))
    (h_m32_pin : v.m32 r_a = 1) (h_div_pin : v.div r_a = 1)
    (h_a23 : (v.a_2 r_a).val = 0 ∧ (v.a_3 r_a).val = 0)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_d23 : (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_byte_lo :
      (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 0).val
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 1).val * 256
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 2).val * 65536
          + (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 3).val * 16777216
        = (v.d_0 r_a).val + (v.d_1 r_a).val * 65536)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value :
      (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt
        = ((v.c_0 r_a).val + (v.c_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.np r_a) * (2:ℤ)^32)
    (h_rs2_value :
      (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt
        = ((v.b_0 r_a).val + (v.b_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nb r_a) * (2:ℤ)^32)
    (h_r_le :
      (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
        - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32).natAbs
        ≤ (Sail.BitVec.extractLsb remw_input.r2_val 31 0).toInt.natAbs)
    (h_r_sign :
      0 ≤ (((v.d_0 r_a).val + (v.d_1 r_a).val * 65536 : ℤ)
            - ZiskFv.PackedBitVec.SignedChunkLift.toIntZ (v.nr r_a) * (2:ℤ)^32)
          * (Sail.BitVec.extractLsb remw_input.r1_val 31 0).toInt) :
    (OpEnvelope.remwOfExtractedShape
      remw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
      h_m32_pin h_div_pin h_a23 h_b23 h_d23 h_c23 h_byte_lo h_sext_choice
      h_rs1_value h_rs2_value h_r_le h_r_sign).aeneasBridgeTrust := by
  unfold OpEnvelope.remwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩

/-- Construct the REMUW ArithDiv-provider envelope while deriving its Main
activation/opcode pins from production-extracted row-shape equalities. -/
def OpEnvelope.remuwOfExtractedShape
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (_h_m32 : provenance.extractedRow.m32 = true)
    (_h_set_pc : provenance.extractedRow.setPc = false)
    (_h_store_pc : provenance.extractedRow.storePc = false)
    (_h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (_h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    OpEnvelope state m r_main :=
  OpEnvelope.remuw remuw_input r1 r2 rd bus v r_a
    (MainRowProvenance.remUWPins_of_extracted_shape provenance h_op h_external)
    h_match_secondary promises arith_mem bounds h_row_constraints arith_table
    arith_chunk_ranges arith_carry_ranges remainder_bound h_b23 h_c23
    h_sext_choice h_rs1_value h_rs2_value

/-- The REMUW bridge predicate is derivable from extracted row-shape
equalities and the remaining dynamic ArithDiv facts. -/
theorem OpEnvelope.aeneasBridgeTrust_remuwOfExtractedShape
    (remuw_input : PureSpec.RemuwInput) (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r_a : ℕ)
    (provenance : ZiskFv.Compliance.MainRowProvenance m r_main)
    (h_op : provenance.extractedRow.op = ExtractedConst.opRemUW)
    (h_external : provenance.extractedRow.isExternalOp = true)
    (h_m32 : provenance.extractedRow.m32 = true)
    (h_set_pc : provenance.extractedRow.setPc = false)
    (h_store_pc : provenance.extractedRow.storePc = false)
    (h_jmp_offset1 : provenance.extractedRow.jmpOffset1 = 4)
    (h_jmp_offset2 : provenance.extractedRow.jmpOffset2 = 4)
    (h_match_secondary :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary v r_a))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (arith_table : ZiskFv.Compliance.ArithDivTableWitness v r_a)
    (arith_chunk_ranges : ZiskFv.Compliance.ArithDivChunkRangeWitness v r_a)
    (arith_carry_ranges :
      ZiskFv.Compliance.ArithDivSignedCarryRangeWitness v r_a)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness v r_a)
    (h_b23 : (v.b_2 r_a).val = 0 ∧ (v.b_3 r_a).val = 0)
    (h_c23 : (v.c_2 r_a).val = 0 ∧ (v.c_3 r_a).val = 0)
    (h_sext_choice :
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 0 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 0) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 < 2147483648) ∨
      (((ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 4).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 5).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 6).val = 255 ∧
          (ZiskFv.Channels.MemoryBusBytes.byteAt bus.e2 7).val = 255) ∧
        (v.d_0 r_a).val + (v.d_1 r_a).val * 65536 ≥ 2147483648))
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
              = (v.c_0 r_a).val + (v.c_1 r_a).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
              = (v.b_0 r_a).val + (v.b_1 r_a).val * 65536) :
    (OpEnvelope.remuwOfExtractedShape
      remuw_input r1 r2 rd bus v r_a provenance h_op h_external h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2 h_match_secondary
      promises arith_mem bounds h_row_constraints arith_table arith_chunk_ranges
      arith_carry_ranges remainder_bound h_b23 h_c23 h_sext_choice h_rs1_value
      h_rs2_value).aeneasBridgeTrust := by
  unfold OpEnvelope.remuwOfExtractedShape OpEnvelope.aeneasBridgeTrust
  let pins := MainRowProvenance.remUWPins_of_extracted_shape provenance h_op h_external
  let controls :=
    MainRowProvenance.externalFallthroughControl_of_extracted_shape provenance h_m32
      h_set_pc h_store_pc h_jmp_offset1 h_jmp_offset2
  exact ⟨pins.main_active, pins.main_op, controls.1, controls.2.1,
    controls.2.2.1, controls.2.2.2.1, controls.2.2.2.2⟩


end ZiskFv.Compliance
