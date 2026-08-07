import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingCopyb
import ZiskFv.Compliance.SingleAddWitness

/-!
# Raw-program binding non-vacuity

This module proves that the binding is inhabited by the independently
hand-authored and verifier-accepted `add x1, x1, x1` witness. The committed ROM
row is a literal witness input, not defined through `romMessageOfRaw`.
-/

open Goldilocks

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Compliance.SingleAddWitness
open Aeneas Aeneas.Std Result zisk_core

private theorem fromInstFullPins (zi : zisk_inst.ZiskInst) :
    ∃ row, aeneas_extract.ZiskInstExtract.from_inst zi = ok row ∧
      row.op = zi.op ∧ row.is_external_op = zi.is_external_op ∧ row.m32 = zi.m32 ∧
      row.set_pc = zi.set_pc ∧ row.store_pc = zi.store_pc ∧
      row.jmp_offset1 = zi.jmp_offset1 ∧ row.jmp_offset2 = zi.jmp_offset2 ∧
      row.a_src = zi.a_src ∧ row.a_use_sp_imm1 = zi.a_use_sp_imm1 ∧
      row.a_offset_imm0 = zi.a_offset_imm0 ∧ row.b_src = zi.b_src ∧
      row.b_use_sp_imm1 = zi.b_use_sp_imm1 ∧ row.b_offset_imm0 = zi.b_offset_imm0 ∧
      row.ind_width = zi.ind_width ∧ row.store = zi.store ∧
      row.store_offset = zi.store_offset ∧ row.is_precompiled = zi.is_precompiled := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

set_option maxHeartbeats 2000000 in
private theorem createRegisterAddX1FullPins
    (input : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : input.rd.val = 1) (hrs1 : input.rs1.val = 1) (hrs2 : input.rs2.val = 1)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed
      { Extraction.defCtx with extract_marker := (), input_precompile := none }
      input zisk_ops.ZiskOp.Add 4#u64 = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.a_src = zisk_inst.SRC_REG ∧ zib.i.a_use_sp_imm1 = 0#u64 ∧
      zib.i.a_offset_imm0.val = 1 ∧ zib.i.b_src = zisk_inst.SRC_REG ∧
      zib.i.b_use_sp_imm1 = 0#u64 ∧ zib.i.b_offset_imm0.val = 1 ∧
      zib.i.ind_width = 0#u64 ∧ zib.i.store = zisk_inst.STORE_REG ∧
      zib.i.store_offset.val = 1 ∧ zib.i.is_precompiled = false := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code, zisk_ops.ZiskOp.is_m32,
    zisk_ops.ZiskOp.input_size, core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_inst_builder.ZiskInstBuilder.j, zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    zisk_inst.SRC_REG, zisk_inst.STORE_REG, lift, Bind.bind, bind_ok] at h
  have ca := Extraction.cast_u32_u64_val input.rs1
  have cb := Extraction.cast_u32_u64_val input.rs2
  have cs := Extraction.hcast_u32_i64_val input.rd
  have eu1 := Extraction.cast_one_u64
  have eu31 := Extraction.cast_31_u64
  have ei1 := Extraction.cast_one_i64
  have ei31 := Extraction.cast_31_i64
  split_ifs at h <;> (try scalar_tac)
  all_goals
    simp only [bind_ok, Bind.bind] at h
    rw [Result.ok.injEq] at h
    subst ctx
    refine ⟨_, rfl, ?_⟩
    simp [zisk_inst.SRC_REG, zisk_inst.STORE_REG, ca, cb, cs, hrd, hrs1, hrs2]

private theorem transpileAddX1FullPins
    (ext : aeneas_extract.Rv64imTranspileExtract)
    (hext : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32
        (Completeness.Rv64imShapes.rawRType 0 1 1 0 1 0x33)) = ok ext) :
    ext.row.a_src = zisk_inst.SRC_REG ∧ ext.row.a_use_sp_imm1 = 0#u64 ∧
      ext.row.a_offset_imm0.val = 1 ∧ ext.row.b_src = zisk_inst.SRC_REG ∧
      ext.row.b_use_sp_imm1 = 0#u64 ∧ ext.row.b_offset_imm0.val = 1 ∧
      ext.row.ind_width = 0#u64 ∧ ext.row.store = zisk_inst.STORE_REG ∧
      ext.row.store_offset.val = 1 ∧ ext.row.is_precompiled = false := by
  let raw := ZiskFv.Compliance.Decode.toU32
    (Completeness.Rv64imShapes.rawRType 0 1 1 0 1 0x33)
  have hdec : aeneas_extract.rv64im_decode.decode_32_core raw =
      aeneas_extract.rv64im_decode.decode_r raw
        aeneas_extract.rv64im_decode.RiscvOpcode.Add := by
    simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc,
      Bind.bind, bind_ok, ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.toU32_and7, ZiskFv.Compliance.Decode.toU32_shr12,
      ZiskFv.Compliance.Decode.toU32_shr25,
      ZiskFv.Compliance.Decode.rawRType_opcode 0 1 1 0 1 0x33 (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct3 0 1 1 0 1 0x33
        (by norm_num) (by norm_num) (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct7 0 1 1 0 1 0x33
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    rfl
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, hrs2b⟩ :=
    Extraction.decode_r_bounds raw aeneas_extract.rv64im_decode.RiscvOpcode.Add
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded :=
    hdec.trans hdecoded
  obtain ⟨decoded', hdecoded', hrdbv, hrs1bv, hrs2bv⟩ :=
    decode_r_fields raw aeneas_extract.rv64im_decode.RiscvOpcode.Add
  have hdd : decoded = decoded' := Result.ok.inj (hdecoded.symm.trans hdecoded')
  subst decoded'
  have hrd : decoded.rd.val = 1 := by
    have hm := rawRType_rd 0 1 1 0 1 0x33 (by norm_num) (by norm_num) (by norm_num)
    have hm' : (raw &&& 3968#u32).bv >>> 7 = 1#32 := by simpa [raw] using hm
    exact congrArg BitVec.toNat (hrdbv.trans hm')
  have hrs1 : decoded.rs1.val = 1 := by
    have hm := rawRType_rs1 0 1 1 0 1 0x33
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hm' : (raw &&& 1015808#u32).bv >>> 15 = 1#32 := by simpa [raw] using hm
    exact congrArg BitVec.toNat (hrs1bv.trans hm')
  have hrs2 : decoded.rs2.val = 1 := by
    have hm := rawRType_rs2 0 1 1 0 1 0x33
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hm' : (raw &&& 32505856#u32).bv >>> 20 = 1#32 := by simpa [raw] using hm
    exact congrArg BitVec.toNat (hrs2bv.trans hm')
  have hrdeq : decoded.rd = 1#u32 := by
    apply UScalar.eq_of_val_eq
    simpa using hrd
  have hrs1eq : decoded.rs1 = 1#u32 := by
    apply UScalar.eq_of_val_eq
    simpa using hrs1
  have hrs2eq : decoded.rs2 = 1#u32 := by
    apply UScalar.eq_of_val_eq
    simpa using hrs2
  let input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm }
  obtain ⟨ctx0, hctx0⟩ := Extraction.create_register_op_typed_ok
    { Extraction.defCtx with extract_marker := (), input_precompile := none }
    input zisk_ops.ZiskOp.Add 4#u64
    (by simp [input, hrs1]) (by simp [input, hrs2]) (by simp [input, hrd])
  obtain ⟨zib, hzib, ha, hau, hao, hb, hbu, hbo, hiw, hs, hso, hip⟩ :=
    createRegisterAddX1FullPins input ctx0
      (by simp [input, hrd]) (by simp [input, hrs1]) (by simp [input, hrs2]) hctx0
  obtain ⟨dext, hdext⟩ := Extraction.decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, hra, hrau, hraoff,
    hrb, hrbu, hrboff, hriw, hrs, hrso, hrip⟩ := fromInstFullPins zib.i
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
        Extraction.defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Add false =
          ok { ctx0 with extract_marker := () } := by
    simp only [input, hrdeq, hrs1eq, hrs2eq] at hctx0
    rw [show
      { Extraction.defCtx with extract_marker := (), input_precompile := none } =
        Extraction.defCtx from rfl] at hctx0
    have hprec : Extraction.defCtx.input_precompile = none := rfl
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      hprec, riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR, Bind.bind, bind_ok]
    simp [input, ne_eq, hrdeq, hrs1eq, hrs2eq,
      show ((0#u32 : Std.U32) = 2068#u32) = False from by decide]
    rw [show
      { Extraction.defCtx with extract_marker := (), input_precompile := none } =
        Extraction.defCtx from rfl, hctx0]
    rfl
  have hext' : aeneas_extract.extract_transpile_rv64im_raw raw =
      ok { accepted := true, decode := dext, row := row } := by
    rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, input,
      show aeneas_extract.lowering_opcode
        aeneas_extract.rv64im_decode.RiscvOpcode.Add =
          ok (some riscv2zisk_single_row.Rv64imSingleRowOpcode.Add) from rfl]
    change
      (do
        let ctx ← riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          Extraction.defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Add false
        let zib : zisk_inst_builder.ZiskInstBuilder ←
          core.option.Option.unwrap ctx.extract_inst
        let row : aeneas_extract.ZiskInstExtract ←
          aeneas_extract.ZiskInstExtract.from_inst zib.i
        ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) =
      ok { accepted := true, decode := dext, row := row }
    simp only [hlower, Bind.bind, bind_ok, hzib, core.option.Option.unwrap,
      Result.ofOption, hrow]
  have he : ext = { accepted := true, decode := dext, row := row } :=
    Result.ok.inj (hext.symm.trans (by simpa [raw] using hext'))
  have herow : ext.row = row := congrArg aeneas_extract.Rv64imTranspileExtract.row he
  rw [herow, hra, hrau, hraoff, hrb, hrbu, hrboff, hriw, hrs, hrso, hrip]
  exact ⟨ha, hau, hao, hb, hbu, hbo, hiw, hs, hso, hip⟩

def singleAddAddr : Fin singleAddAcceptedTrace.programLength → FGL := fun _ => 0

def singleAddRawProgram : Fin singleAddAcceptedTrace.programLength → BitVec 32 :=
  fun _ => 0x001080b3

theorem singleAddProgramBinding :
    ProgramBinding singleAddAcceptedTrace singleAddAddr singleAddRawProgram := by
  constructor
  · intro k k' h
    fin_cases k
    fin_cases k'
    simp at h
  · intro k
    fin_cases k
    change RegisterMemBusBalance.addX1ProgramRow = romMessageOfRaw 0 0x001080b3
    obtain ⟨ext, hext, hstatic⟩ := transpile_add 1 1 1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have hraw : (Completeness.Rv64imShapes.rawRType 0 1 1 0 1 0x33 : BitVec 32)
        = 0x001080b3 := by decide
    rw [hraw] at hext
    obtain ⟨ha, hau, hao, hb, hbu, hbo, hiw, hs, hso, hip⟩ :=
      transpileAddX1FullPins ext (by simpa [hraw] using hext)
    obtain ⟨hop, hie, hm32, hset, hstorepc, hj1, hj2⟩ := hstatic
    have hcast4 : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = 4 := by decide
    have haeq : ext.row.a_offset_imm0 = 1#u64 := UScalar.eq_of_val_eq hao
    have hbeq : ext.row.b_offset_imm0 = 1#u64 := UScalar.eq_of_val_eq hbo
    rw [romMessageOfRaw, hext]
    congr 1 <;>
      simp [RegisterMemBusBalance.addX1ProgramRow, romRowOf, signedOffset, sourceImmediate,
        romOpcode, romFlagBitsOfExtract, ZiskFv.AirsClean.Main.packFlags,
        ha, hau, hao, haeq, hb, hbu, hbo, hbeq, hiw, hs, hso, hip,
        hop, hie, hm32, hset, hstorepc, hj1, hj2, hcast4,
        zisk_inst.SRC_IMM, zisk_inst.SRC_MEM, zisk_inst.SRC_IND,
        zisk_inst.SRC_REG, zisk_inst.STORE_MEM, zisk_inst.STORE_IND,
        zisk_inst.STORE_REG, ZiskFv.AirsClean.boolF]

#print axioms singleAddProgramBinding

/-- Identity embedding of architectural raw-word indices into physical ROM
    rows: the single-ADD witness has one raw word and one physical row. -/
def singleAddStart :
    Fin singleAddAcceptedTrace.programLength → Fin singleAddAcceptedTrace.programLength :=
  id

theorem singleAddProgramRowsBinding :
    ProgramRowsBinding singleAddAcceptedTrace singleAddStart singleAddAddr
      singleAddRawProgram := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k k' h
    fin_cases k
    fin_cases k'
    simp at h
  · intro k
    fin_cases k
    decide
  · intro k
    fin_cases k
    decide
  · intro k k' h
    fin_cases k
    fin_cases k'
    simp at h
  · intro k
    fin_cases k
    simp only [singleAddStart, id_eq, singleAddAddr, singleAddRawProgram]
    obtain ⟨ext, hext, hstatic⟩ := transpile_add 1 1 1 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    have hraw : (Completeness.Rv64imShapes.rawRType 0 1 1 0 1 0x33 : BitVec 32)
        = 0x001080b3 := by decide
    rw [hraw] at hext
    have hnon : (ZiskFv.Compliance.Decode.toU32 (0x001080b3 : BitVec 32) &&& 127#u32)
        ≠ 103#u32 := by decide
    have hsnd : (romMessagesOfRaw (0 : FGL) (0x001080b3 : BitVec 32)).2 = none := by
      unfold romMessagesOfRaw
      rw [aeneas_extract.extract_transpile_rv64im_rows_raw, hext]
      simp only [lift, Bind.bind, bind_ok, hnon]
      rfl
    refine ⟨?_, ?_⟩
    · rw [romMessagesOfRaw_fst_of_non_jalr _ _ ext hext hnon]
      exact singleAddProgramBinding.2 _
    · rw [hsnd]
      trivial
  · intro j
    fin_cases j
    exact ⟨⟨0, Nat.zero_lt_one⟩, Or.inl rfl⟩

#print axioms singleAddProgramRowsBinding

end ZiskFv.Compliance.RawProgramBinding
