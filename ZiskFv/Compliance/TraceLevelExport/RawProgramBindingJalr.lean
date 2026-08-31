import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingControl
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.JalrRows

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Compliance
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open Aeneas Aeneas.Std Result zisk_core
open ZiskFv.Compliance.Extraction

set_option maxHeartbeats 800000

private theorem from_inst_store_use_sp
    (zi : zisk_inst.ZiskInst) (e : aeneas_extract.ZiskInstExtract)
    (h : aeneas_extract.ZiskInstExtract.from_inst zi = .ok e) :
    e.store_use_sp = zi.store_use_sp := by
  unfold aeneas_extract.ZiskInstExtract.from_inst at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst e
  rfl

private theorem signExtend64_signExtend32 (v : BitVec 12) :
    BitVec.signExtend 64 (BitVec.signExtend 32 v) = BitVec.signExtend 64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 64
  · interval_cases k <;>
      simp [BitVec.getElem_signExtend,
        BitVec.msb_signExtend]
  · simp [BitVec.getLsbD_signExtend, hk]

private theorem jalr_signExtend64_signExtend32 (v : BitVec 12) :
    BitVec.signExtend 64 (BitVec.signExtend 32 v) = BitVec.signExtend 64 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 64
  · interval_cases k <;>
      simp [BitVec.getElem_signExtend,
        BitVec.msb_signExtend]
  · simp [BitVec.getLsbD_signExtend, hk]

private theorem jalr_immediate_rom_value
    (imm : BitVec 12) (d : riscv2zisk_single_row.Rv64imLoweringInput)
    (hdimm : d.imm.bv = BitVec.signExtend 32 imm)
    (row : aeneas_extract.ZiskInstExtract)
    (hsrc : row.a_src = zisk_inst.SRC_IMM)
    (hhi : row.a_use_sp_imm1.val =
      (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296)
    (hlo : row.a_offset_imm0.val =
      (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296) :
    BitVec.signExtend 64 imm =
      BitVec.ofNat 64
        ((romRowOf (0 : FGL) row).a_offset_imm0.val +
          (romRowOf (0 : FGL) row).a_imm1.val * 4294967296) := by
  have hv :
      (IScalar.hcast UScalarTy.U64 d.imm).val =
        (BitVec.signExtend 64 imm).toNat := by
    change (BitVec.signExtend 64 d.imm.bv).toNat =
      (BitVec.signExtend 64 imm).toNat
    rw [hdimm, jalr_signExtend64_signExtend32]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [romRowOf, hsrc, if_pos, UScalar.val]
  have hloBound : row.a_offset_imm0.bv.toNat < 2 ^ 32 := by
    rw [show row.a_offset_imm0.bv.toNat =
      (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 by
        simpa only [UScalar.val] using hlo]
    exact Nat.mod_lt _ (by norm_num)
  have hsigned : (signedOffset row.a_offset_imm0).val =
      row.a_offset_imm0.bv.toNat := by
    have hnonneg : 2 * row.a_offset_imm0.val < 18446744073709551616 := by
      change 2 * row.a_offset_imm0.bv.toNat < 18446744073709551616
      norm_num at hloBound ⊢
      omega
    have hsignedF : signedOffset row.a_offset_imm0 =
        (row.a_offset_imm0.bv.toNat : FGL) := by
      simp [signedOffset, BitVec.toInt, if_pos hnonneg]
    rw [hsignedF]
    exact Nat.mod_eq_of_lt (lt_trans hloBound (by norm_num))
  rw [hsigned]
  have hhi' : row.a_use_sp_imm1.bv.toNat =
      (IScalar.hcast UScalarTy.U64 d.imm).val / 4294967296 := by
    simpa only [UScalar.val] using hhi
  have hlo' : row.a_offset_imm0.bv.toNat =
      (IScalar.hcast UScalarTy.U64 d.imm).val % 4294967296 := by
    simpa only [UScalar.val] using hlo
  rw [hhi', hlo', hv]
  have hhigh :
      (((BitVec.signExtend 64 imm).toNat / 4294967296 : Nat) : FGL).val =
        (BitVec.signExtend 64 imm).toNat / 4294967296 := by
    exact Nat.mod_eq_of_lt (by
      have := (BitVec.signExtend 64 imm).isLt
      norm_num at this ⊢
      exact Nat.div_lt_of_lt_mul (by omega))
  rw [hhigh]
  rw [Nat.mod_add_div']
  exact (Nat.mod_eq_of_lt (BitVec.isLt _)).symm

private theorem jalr_raw_rows
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
    ∃ (rows : aeneas_extract.Rv64imTranspileRowsExtract)
        (input : riscv2zisk_single_row.Rv64imLoweringInput),
      aeneas_extract.extract_transpile_rv64im_rows_raw
          (ZiskFv.Compliance.Decode.toU32
            (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) =
        .ok rows ∧
      input.rd.val = rd ∧ input.rs1.val = rs1 ∧
      input.imm.bv = BitVec.signExtend 32 (BitVec.ofNat 12 imm) ∧
      ((rows.row_count = 1#u32 ∧
          ZiskFv.Compliance.Extraction.JalrAlignedRowPins input
            { paddr := rows.last_row.paddr, store_pc := rows.last_row.store_pc,
              store_use_sp := rows.last_row.store_use_sp, store := rows.last_row.store,
              store_offset := rows.last_row.store_offset, set_pc := rows.last_row.set_pc,
              is_precompiled := rows.last_row.is_precompiled,
              ind_width := rows.last_row.ind_width, «end» := rows.last_row.end,
              a_src := rows.last_row.a_src, a_use_sp_imm1 := rows.last_row.a_use_sp_imm1,
              a_offset_imm0 := rows.last_row.a_offset_imm0, b_src := rows.last_row.b_src,
              b_use_sp_imm1 := rows.last_row.b_use_sp_imm1,
              b_offset_imm0 := rows.last_row.b_offset_imm0,
              jmp_offset1 := rows.last_row.jmp_offset1,
              jmp_offset2 := rows.last_row.jmp_offset2,
              is_external_op := rows.last_row.is_external_op, op := rows.last_row.op,
              op_type := zisk_inst.ZiskOperationType.None, m32 := rows.last_row.m32,
              input_size := rows.last_row.input_size,
              sorted_pc_list_index := rows.last_row.sorted_pc_list_index }) ∨
        (rows.row_count = 2#u32 ∧
          ZiskFv.Compliance.Extraction.JalrUnalignedFirstRowPins input rows.first_row ∧
          ZiskFv.Compliance.Extraction.JalrUnalignedSuccessorRowPins input
            { paddr := rows.last_row.paddr, store_pc := rows.last_row.store_pc,
              store_use_sp := rows.last_row.store_use_sp, store := rows.last_row.store,
              store_offset := rows.last_row.store_offset, set_pc := rows.last_row.set_pc,
              is_precompiled := rows.last_row.is_precompiled,
              ind_width := rows.last_row.ind_width, «end» := rows.last_row.end,
              a_src := rows.last_row.a_src, a_use_sp_imm1 := rows.last_row.a_use_sp_imm1,
              a_offset_imm0 := rows.last_row.a_offset_imm0, b_src := rows.last_row.b_src,
              b_use_sp_imm1 := rows.last_row.b_use_sp_imm1,
              b_offset_imm0 := rows.last_row.b_offset_imm0,
              jmp_offset1 := rows.last_row.jmp_offset1,
              jmp_offset2 := rows.last_row.jmp_offset2,
              is_external_op := rows.last_row.is_external_op, op := rows.last_row.op,
              op_type := zisk_inst.ZiskOperationType.None, m32 := rows.last_row.m32,
              input_size := rows.last_row.input_size,
              sorted_pc_list_index := rows.last_row.sorted_pc_list_index })) := by
  let raw := ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (ZiskFv.Compliance.Decode.toU32 raw) =
      aeneas_extract.rv64im_decode.decode_i
        (ZiskFv.Compliance.Decode.toU32 raw)
          aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false := by
    simp only [raw, aeneas_extract.rv64im_decode.decode_32_core, lift,
      Bind.bind, bind_ok, ZiskFv.Compliance.Decode.toU32_and127,
      ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x67 (by norm_num)]
    all_goals rfl
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ :=
    decode_i_bounds (ZiskFv.Compliance.Decode.toU32 raw)
      aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok decoded := hdec.trans hdecoded
  let input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1,
      rs2 := decoded.rs2, imm := decoded.imm }
  obtain ⟨ctx, hctx⟩ := jalr_ok { defCtx with extract_marker := () } input
    (by simpa only [input] using hrs1b) (by simpa only [input] using hrdb) rfl
  have hpins := jalr_production_expanded_row_pins input ctx
    (by simpa only [input] using hrdb) (by simpa only [input] using hrs1b) hctx
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  have hdext' := hdext
  unfold aeneas_extract.decode_extract_from_decoded at hdext'
  obtain ⟨_, _, hdext'⟩ := bind_eq_ok_imp hdext'
  obtain ⟨_, _, hdext'⟩ := bind_eq_ok_imp hdext'
  obtain ⟨_, _, hdext'⟩ := bind_eq_ok_imp hdext'
  rw [Result.ok.injEq] at hdext'
  have hdextimm : dext.imm = decoded.imm := by rw [← hdext']
  have hdextrd : dext.rd = decoded.rd := by rw [← hdext']
  have hdextrs1 : dext.rs1 = decoded.rs1 := by rw [← hdext']
  have hdextrs2 : dext.rs2 = decoded.rs2 := by rw [← hdext']
  obtain ⟨hrdbv, hrs1bv, himm64⟩ :=
    decode_i_rawIType_fields imm rs1 0 rd 0x67 hrs1 (by norm_num) hrd
      (by norm_num) aeneas_extract.rv64im_decode.RiscvOpcode.Jalr decoded
      (by simpa only [raw] using hdecoded)
  have hrdval : input.rd.val = rd := by
    change decoded.rd.bv.toNat = rd
    rw [hrdbv]
    simp [BitVec.toNat_ofNat]
    omega
  have hrs1val : input.rs1.val = rs1 := by
    change decoded.rs1.bv.toNat = rs1
    rw [hrs1bv]
    simp [BitVec.toNat_ofNat]
    omega
  have himm : input.imm.bv = BitVec.signExtend 32 (BitVec.ofNat 12 imm) := by
    simp only [input]
    exact decode_i_rawIType_imm imm rs1 0 rd 0x67 hrs1 (by norm_num) hrd
      (by norm_num) aeneas_extract.rv64im_decode.RiscvOpcode.Jalr decoded
        (by simpa only [raw] using hdecoded)
  have hlower :
      riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
          defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false =
        .ok { ctx with extract_marker := () } := by
    change (do
      let s ← riscv2zisk_context.Riscv2ZiskContext.jalr
        { defCtx with extract_marker := () } input 4#u64
      .ok { s with extract_marker := () }) = _
    rw [hctx]
    rfl
  rcases hpins with haligned | hunaligned
  · obtain ⟨hrem, hfirst, last, hlast, hpins⟩ := haligned
    obtain ⟨lastRow, hfrom, haSrc, haHi, haLo, hbSrc, hbHi, hbLo, hwidth,
      hop, hstore, hstoreOffset, hj1, hj2, hsetpc, hstorepc, hieo, hm32⟩ :=
      from_inst_full_fields last.i
    have hstoreUseSp := from_inst_store_use_sp last.i lastRow hfrom
    let terminal : aeneas_extract.Rv64imTranspileExtract :=
      { accepted := true, decode := dext, row := lastRow }
    have hterminal :
        aeneas_extract.extract_transpile_rv64im_raw
            (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal := by
      rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
      simp only [bind_ok, Bind.bind, hdext, hopd]
      change (do
        let input' ← riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
          decoded.rd decoded.rs1 decoded.rs2 decoded.imm
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input' riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      simp only [riscv2zisk_single_row.Rv64imLoweringInput.new]
      change (do
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      rw [hlower]
      simp only [Bind.bind]
      simp only [hlast, core.option.Option.unwrap, Result.ofOption, bind_ok]
      rw [hfrom]
      rfl
    let rows : aeneas_extract.Rv64imTranspileRowsExtract :=
      { accepted := true, decode := dext, row_count := 1#u32,
        first_row := lastRow, last_row := lastRow }
    refine ⟨rows, input, ?_, hrdval, hrs1val, himm, Or.inl ⟨rfl, ?_⟩⟩
    · unfold aeneas_extract.extract_transpile_rv64im_rows_raw
      rw [hterminal]
      simp only [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x67 (by norm_num)]
      norm_num [terminal, rows, raw, input, hdextimm, hrem, lift, Bind.bind,
        ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode]
    · unfold JalrAlignedRowPins JalrDestinationPins
        JalrRegisterOrX0SourcePins at hpins ⊢
      simpa [rows, hbSrc, hbHi, hbLo, hop, hstore, hstoreOffset, hstoreUseSp,
        hj1, hj2, hsetpc, hstorepc, hieo, hm32] using hpins
  · obtain ⟨rem, hrem, hrem0, first, last, hfirst, hlast, hfirstPins,
      hlastPins⟩ := hunaligned
    obtain ⟨lastRow, hfrom, haSrc, haHi, haLo, hbSrc, hbHi, hbLo, hwidth,
      hop, hstore, hstoreOffset, hj1, hj2, hsetpc, hstorepc, hieo, hm32⟩ :=
      from_inst_full_fields last.i
    have hstoreUseSp := from_inst_store_use_sp last.i lastRow hfrom
    let terminal : aeneas_extract.Rv64imTranspileExtract :=
      { accepted := true, decode := dext, row := lastRow }
    have hterminal :
        aeneas_extract.extract_transpile_rv64im_raw
            (ZiskFv.Compliance.Decode.toU32 raw) = .ok terminal := by
      rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
      simp only [bind_ok, Bind.bind, hdext, hopd]
      change (do
        let input' ← riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64
          decoded.rd decoded.rs1 decoded.rs2 decoded.imm
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input' riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      simp only [riscv2zisk_single_row.Rv64imLoweringInput.new]
      change (do
        let ctx' ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input
            defCtx input riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
        let zib ← core.option.Option.unwrap ctx'.extract_inst
        let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
        .ok ({ accepted := true, decode := dext, row := row } :
          aeneas_extract.Rv64imTranspileExtract)) = _
      rw [hlower]
      simp only [Bind.bind]
      simp only [hlast, core.option.Option.unwrap, Result.ofOption, bind_ok]
      rw [hfrom]
      rfl
    let rows : aeneas_extract.Rv64imTranspileRowsExtract :=
      { accepted := true, decode := dext, row_count := 2#u32,
        first_row := first, last_row := lastRow }
    refine ⟨rows, input, ?_, hrdval, hrs1val, himm,
      Or.inr ⟨rfl, hfirstPins, ?_⟩⟩
    · unfold aeneas_extract.extract_transpile_rv64im_rows_raw
      rw [hterminal]
      simp only [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x67 (by norm_num)]
      have hremval : rem.val ≠ 0 := by
        intro hz
        apply hrem0
        apply IScalar.eq_of_val_eq
        simpa using hz
      have hinputNew :
          riscv2zisk_single_row.Rv64imLoweringInput.new 0#u64 decoded.rd
              decoded.rs1 decoded.rs2 decoded.imm = .ok input := rfl
      have hremDecoded :
          (decoded.imm % 4#i32 : Result Std.I32) = Result.ok rem := by
        simpa only [input] using hrem
      norm_num [terminal, raw, hdextrd, hdextrs1, hdextrs2, hdextimm, hrem,
        hremDecoded, hremval, lift, Bind.bind, hinputNew, hlower, hfirst, rows,
        core.option.Option.unwrap, Result.ofOption]
      rw [if_pos (by decide)]
      simp only [defCtx] at hlower
      rw [hlower]
      simp [hfirst]
    · unfold JalrUnalignedSuccessorRowPins JalrDestinationPins at hlastPins ⊢
      simpa [rows, hbSrc, hbHi, hbLo, hop, hstore, hstoreOffset, hstoreUseSp,
        hj1, hj2, hsetpc, hstorepc, hieo, hm32] using hlastPins

/-- A data-carrying certificate for the row count selected by the production
    extractor. Keeping the extracted rows as data permits elimination into the
    `ProgramDecode_jalr` bundle while the equalities remain proof fields. -/
structure JalrRawRowsCertificate (raw : BitVec 32) (count : Std.U32) : Type where
  rows : aeneas_extract.Rv64imTranspileRowsExtract
  h_extract :
    aeneas_extract.extract_transpile_rv64im_rows_raw
        (ZiskFv.Compliance.Decode.toU32 raw) = .ok rows
  h_count : rows.row_count = count

set_option maxHeartbeats 800000 in
/-- Raw-program evidence for JALR's production-selected one- or two-row
    lowering. The two constructors carry exactly the Main/ROM correspondences
    consumed by their matching committed-program decode bundle. -/
structure RawProgramDecodeJalrAligned {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) : Type where
  raw : BitVec 32
  h_raw : raw = ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
    (regidx_to_fin c.rs1).val 0 (regidx_to_fin c.rd).val 0x67
  h_rows : JalrRawRowsCertificate raw 1#u32
  h_offset_aligned : c.offset_bv = BitVec.signExtend 64 c.imm
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_flag : (mainOfTable trace.program trace.mainTable).flag i.val = 0
  h_a_mask_lo : (mainOfTable trace.program trace.mainTable).a_0 i.val = 4294967294
  h_a_mask_hi : (mainOfTable trace.program trace.mainTable).a_1 i.val = 4294967295
  h_c1_zero : (mainOfTable trace.program trace.mainTable).c_1 i.val = 0
  h_offset_even : c.offset_bv &&& 1#64 = 0#64
  h_target_nonneg :
    0 ≤ (((mainOfTable trace.program trace.mainTable).c_0 i.val).val : Int) +
      c.offset_bv.toInt
  h_target_lt :
    (((mainOfTable trace.program trace.mainTable).c_0 i.val).val : Int) +
      c.offset_bv.toInt < GL_prime
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        start k = j ∧ addr k = (trace.program j).line ∧
          rawProgram k = raw

set_option maxHeartbeats 800000 in
structure RawProgramDecodeJalrUnaligned {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) : Type where
  raw : BitVec 32
  h_raw : raw = ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
    (regidx_to_fin c.rs1).val 0 (regidx_to_fin c.rd).val 0x67
  h_rows : JalrRawRowsCertificate raw 2#u32
  h_offset_zero : c.offset_bv = 0#64
  h_idx2 : i.val + 2 < trace.mainTable.table.length
  h_flag_add : (mainOfTable trace.program trace.mainTable).flag i.val = 0
  h_flag : (mainOfTable trace.program trace.mainTable).flag (i.val + 1) = 0
  h_a_mask_lo :
    (mainOfTable trace.program trace.mainTable).a_0 (i.val + 1) = 4294967294
  h_a_mask_hi :
    (mainOfTable trace.program trace.mainTable).a_1 (i.val + 1) = 4294967295
  h_c1_zero : (mainOfTable trace.program trace.mainTable).c_1 (i.val + 1) = 0
  h_offset_even : c.offset_bv &&& 1#64 = 0#64
  h_target_nonneg :
    0 ≤ (((mainOfTable trace.program trace.mainTable).c_0 (i.val + 1)).val : Int) +
      c.offset_bv.toInt
  h_target_lt :
    (((mainOfTable trace.program trace.mainTable).c_0 (i.val + 1)).val : Int) +
      c.offset_bv.toInt < GL_prime
  hLineAdd : ∀ j : Fin trace.programLength,
    (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        start k = j ∧ addr k = (trace.program j).line ∧
          rawProgram k = raw
  hLineAnd : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (mainOfTable trace.program trace.mainTable).pc (i.val + 1) →
      ∃ k : Fin rawLength,
        j.val = (start k).val + 1 ∧
          addr k + 1 = (trace.program j).line ∧
            rawProgram k = raw

inductive RawProgramDecode_jalr {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32) : Type where
  | aligned (evidence : RawProgramDecodeJalrAligned trace i c start addr rawProgram)
  | unaligned (evidence : RawProgramDecodeJalrUnaligned trace i c start addr rawProgram)

set_option maxHeartbeats 8000000 in
noncomputable def ProgramDecode_jalr_from_rawProgram {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions)
    (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_jalr trace i c start addr rawProgram) :
    ProgramDecode_jalr trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let rs1 := (regidx_to_fin c.rs1).val
  let imm := c.imm.toNat
  let hex := jalr_raw_rows rd rs1 imm (regidx_to_fin c.rd).isLt
    (regidx_to_fin c.rs1).isLt
  let rows := Classical.choose hex
  let hexInput := Classical.choose_spec hex
  let input := Classical.choose hexInput
  have hspec := Classical.choose_spec hexInput
  have hrows := hspec.1
  have hrd := hspec.2.1
  have hrs1 := hspec.2.2.1
  have himm := hspec.2.2.2.1
  have hmode := hspec.2.2.2.2
  change input.rd.val = (regidx_to_fin c.rd).val at hrd
  change input.rs1.val = (regidx_to_fin c.rs1).val at hrs1
  change input.imm.bv = BitVec.signExtend 32 (BitVec.ofNat 12 imm) at himm
  have himmC : input.imm.bv = BitVec.signExtend 32 c.imm := by
    simpa [imm] using himm
  have himmInt :
      input.imm.val = (BitVec.signExtend 64 c.imm).toInt := by
    rw [show input.imm.val = input.imm.bv.toInt by rfl, himm]
    have himmBv : BitVec.ofNat 12 imm = c.imm := by simp [imm]
    rw [himmBv]
    rw [BitVec.toInt_signExtend, BitVec.toInt_signExtend]
    norm_num
  cases rawDecode with
  | aligned evidence =>
      obtain ⟨raw, hrawEncoded, hcert, hOffset, hidx, hflag, haLo, haHi, hc1,
        heven, hnonneg, hlt, hLine⟩ := evidence
      subst raw
      obtain ⟨certRows, hcertRows, hcount⟩ := hcert
      have hcertEq : certRows = rows :=
        Result.ok.inj (hcertRows.symm.trans (by simpa only [rd, rs1, imm] using hrows))
      have hcount' : rows.row_count = 1#u32 := by
        rw [← hcertEq]
        exact hcount
      have hpins : JalrAlignedRowPins input
          { paddr := rows.last_row.paddr, store_pc := rows.last_row.store_pc,
            store_use_sp := rows.last_row.store_use_sp, store := rows.last_row.store,
            store_offset := rows.last_row.store_offset, set_pc := rows.last_row.set_pc,
            is_precompiled := rows.last_row.is_precompiled,
            ind_width := rows.last_row.ind_width, «end» := rows.last_row.end,
            a_src := rows.last_row.a_src, a_use_sp_imm1 := rows.last_row.a_use_sp_imm1,
            a_offset_imm0 := rows.last_row.a_offset_imm0, b_src := rows.last_row.b_src,
            b_use_sp_imm1 := rows.last_row.b_use_sp_imm1,
            b_offset_imm0 := rows.last_row.b_offset_imm0,
            jmp_offset1 := rows.last_row.jmp_offset1,
            jmp_offset2 := rows.last_row.jmp_offset2,
            is_external_op := rows.last_row.is_external_op, op := rows.last_row.op,
            op_type := zisk_inst.ZiskOperationType.None, m32 := rows.last_row.m32,
            input_size := rows.last_row.input_size,
            sorted_pc_list_index := rows.last_row.sorted_pc_list_index } := by
        rcases hmode with ⟨_, hpins⟩ | ⟨hcountTwo, _, _⟩
        · exact hpins
        · rw [hcount'] at hcountTwo
          norm_num at hcountTwo
      let bits := romFlagBitsOfExtract rows.last_row
      unfold JalrAlignedRowPins at hpins
      rcases hpins with ⟨hop, hj1, hj2, hdest, hsrc, hieo, hm32, hsetpc⟩
      simp only at hop hj1 hj2 hdest hsrc hieo hm32 hsetpc
      refine .aligned
          { h_offset_aligned := hOffset
            h_idx := hidx
            h_flag := hflag
            h_a_mask_lo := haLo
            h_a_mask_hi := haHi
            h_c1_zero := hc1
            h_offset_even := heven
            h_target_nonneg := hnonneg
            h_target_lt := hlt
            bits := bits
            h_bits_ieo := ?_
            h_bits_m32 := ?_
            h_bits_set_pc := ?_
            h_bits_store_pc := ?_
            h_bits_store_ind := ?_
            h_bits_store_reg := ?_
            h_prog := ?_ }
      · exact hieo
      · exact hm32
      · exact hsetpc
      · unfold JalrDestinationPins at hdest
        rcases hdest with hzero | hnonzero
        · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
              rows.last_row.store_offset = 0#i64 ∧ rows.last_row.store_use_sp = false ∧
              rows.last_row.store_pc = false at hzero
          have hrdZero : (regidx_to_fin c.rd).val = 0 := by
            rw [← show input.rd.val = (regidx_to_fin c.rd).val by simpa [rd] using hrd]
            exact congrArg UScalar.val hzero.1
          simp [bits, romFlagBitsOfExtract, hzero.2.2.2.2, hrdZero]
        · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
              rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
              rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hnonzero
          have hrdNonzero : (regidx_to_fin c.rd).val ≠ 0 := by
            intro hz
            apply hnonzero.1
            apply UScalar.eq_of_val_eq
            simpa [rd, hz] using hrd.symm
          simp [bits, romFlagBitsOfExtract, hnonzero.2.2.2.2, hrdNonzero]
      · unfold JalrDestinationPins at hdest
        rcases hdest with hzero | hnonzero
        · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
              rows.last_row.store_offset = 0#i64 ∧ rows.last_row.store_use_sp = false ∧
              rows.last_row.store_pc = false at hzero
          exact decide_eq_false (by
            rw [hzero.2.1]
            simp [zisk_inst.STORE_IND])
        · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
              rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
              rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hnonzero
          exact decide_eq_false (by
            rw [hnonzero.2.1]
            simp [zisk_inst.STORE_REG, zisk_inst.STORE_IND])
      · rcases hdest with hzero | hnonzero
        · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
              rows.last_row.store_offset = 0#i64 ∧ rows.last_row.store_use_sp = false ∧
              rows.last_row.store_pc = false at hzero
          have hrdZero : (regidx_to_fin c.rd).val = 0 := by
            rw [← show input.rd.val = (regidx_to_fin c.rd).val by simpa [rd] using hrd]
            exact congrArg UScalar.val hzero.1
          simp [bits, romFlagBitsOfExtract, hzero.2.1, hrdZero, zisk_inst.STORE_REG]
        · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
              rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
              rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hnonzero
          have hrdNonzero : (regidx_to_fin c.rd).val ≠ 0 := by
            intro hz
            apply hnonzero.1
            apply UScalar.eq_of_val_eq
            simpa [rd, hz] using hrd.symm
          simp [bits, romFlagBitsOfExtract, hnonzero.2.1, hrdNonzero]
      · intro j hline
        obtain ⟨k, hk, haddr, hraw⟩ := hLine j hline
        have hprimary := primary_row_of_programRowsBinding hbind
          ⟨k, hk, haddr, hraw⟩
        have hmsg : trace.program j = romRowOf (addr k) rows.last_row := by
          rw [hprimary]
          unfold romMessagesOfRaw
          rw [show aeneas_extract.extract_transpile_rv64im_rows_raw
              (ZiskFv.Compliance.Decode.toU32
                (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                  (regidx_to_fin c.rs1).val 0 (regidx_to_fin c.rd).val 0x67)) =
                .ok rows by simpa only [rd, rs1, imm] using hrows]
          simp [hcount', haddr]
        unfold JalrDestinationPins at hdest
        rcases hdest with hzero | hnonzero
        · have hrdZero : (regidx_to_fin c.rd).val = 0 := by
            rw [← hrd]
            exact congrArg UScalar.val hzero.1
          have hstoreZero := congrArg IScalar.val hzero.2.2.1
          simp [hmsg, romRowOf, hop, hj1, hj2, bits, hrdZero,
            himmInt, hstoreZero]
        · have hrdNonzero : (regidx_to_fin c.rd).val ≠ 0 := by
            intro hzero
            apply hnonzero.1
            apply UScalar.eq_of_val_eq
            simpa [hzero] using hrd.symm
          have hstoreVal := congrArg IScalar.val hnonzero.2.2.1
          have hstoreOffset :
              ((rows.last_row.store_offset.val : Int) : FGL) =
                Transpiler.ind (regidx_to_fin c.rd) := by
            have hrdPrime : (regidx_to_fin c.rd).val < GL_prime :=
              lt_trans (regidx_to_fin c.rd).isLt (by norm_num)
            apply Fin.ext
            simp [hstoreVal, hcast_u32_i64_val, hrd, Transpiler.ind, hrdPrime]
          simp [hmsg, romRowOf, hop, hj1, hj2, bits, hrdNonzero,
            himmInt, hstoreOffset]
  | unaligned evidence =>
      obtain ⟨raw, hrawEncoded, hcert, hOffset, hidx, hflagAdd, hflag, haLo, haHi,
        hc1, heven, hnonneg, hlt, hLineAdd, hLineAnd⟩ := evidence
      subst raw
      obtain ⟨certRows, hcertRows, hcount⟩ := hcert
      have hcertEq : certRows = rows :=
        Result.ok.inj (hcertRows.symm.trans (by simpa only [rd, rs1, imm] using hrows))
      have hcount' : rows.row_count = 2#u32 := by
        rw [← hcertEq]
        exact hcount
      have hpins : JalrUnalignedFirstRowPins input rows.first_row ∧
          JalrUnalignedSuccessorRowPins input
            { paddr := rows.last_row.paddr, store_pc := rows.last_row.store_pc,
              store_use_sp := rows.last_row.store_use_sp, store := rows.last_row.store,
              store_offset := rows.last_row.store_offset, set_pc := rows.last_row.set_pc,
              is_precompiled := rows.last_row.is_precompiled,
              ind_width := rows.last_row.ind_width, «end» := rows.last_row.end,
              a_src := rows.last_row.a_src, a_use_sp_imm1 := rows.last_row.a_use_sp_imm1,
              a_offset_imm0 := rows.last_row.a_offset_imm0, b_src := rows.last_row.b_src,
              b_use_sp_imm1 := rows.last_row.b_use_sp_imm1,
              b_offset_imm0 := rows.last_row.b_offset_imm0,
              jmp_offset1 := rows.last_row.jmp_offset1,
              jmp_offset2 := rows.last_row.jmp_offset2,
              is_external_op := rows.last_row.is_external_op, op := rows.last_row.op,
              op_type := zisk_inst.ZiskOperationType.None, m32 := rows.last_row.m32,
              input_size := rows.last_row.input_size,
              sorted_pc_list_index := rows.last_row.sorted_pc_list_index } := by
        rcases hmode with ⟨hcountOne, _⟩ | ⟨_, hfirst, hlast⟩
        · rw [hcount'] at hcountOne
          norm_num at hcountOne
        · exact ⟨hfirst, hlast⟩
      let addBits := romFlagBitsOfExtract rows.first_row
      let andBits := romFlagBitsOfExtract rows.last_row
      unfold JalrUnalignedFirstRowPins JalrUnalignedSuccessorRowPins at hpins
      rcases hpins with
        ⟨⟨haddOp, haddJ1, haddJ2, haddASrc, haddHi, haddLo, haddSrc, haddIeo,
            haddM32, haddSetPc, haddStorePc, haddStore⟩,
          ⟨handOp, handJ1, handJ2, handDest, handBSrc, handBUse, handBOffset,
            handIeo, handM32, handSetPc⟩⟩
      change rows.first_row.op = 10#u8 at haddOp
      change rows.first_row.jmp_offset1 = 1#i64 at haddJ1
      change rows.first_row.jmp_offset2 = 1#i64 at haddJ2
      change rows.first_row.a_src = zisk_inst.SRC_IMM at haddASrc
      change rows.first_row.a_use_sp_imm1.val =
        (IScalar.hcast UScalarTy.U64 input.imm).val / 2 ^ 32 at haddHi
      change rows.first_row.a_offset_imm0.val =
        (IScalar.hcast UScalarTy.U64 input.imm).val % 2 ^ 32 at haddLo
      change rows.last_row.op = 14#u8 at handOp
      change rows.last_row.jmp_offset1 = 0#i64 at handJ1
      change rows.last_row.jmp_offset2 = 3#i64 at handJ2
      change rows.last_row.b_src = zisk_inst.SRC_C at handBSrc
      refine .unaligned
        { h_offset_zero := hOffset
          h_idx2 := hidx
          h_flag_add := hflagAdd
          h_flag := hflag
          h_a_mask_lo := haLo
          h_a_mask_hi := haHi
          h_c1_zero := hc1
          h_offset_even := heven
          h_target_nonneg := hnonneg
          h_target_lt := hlt
          addBits := addBits
          h_add_ieo := by
            exact haddIeo
          h_add_m32 := by
            exact haddM32
          h_add_set_pc := by
            exact haddSetPc
          h_add_store_reg := by
            change decide (rows.first_row.store = zisk_inst.STORE_REG) = false
            exact decide_eq_false (by
              rw [haddStore]
              simp [zisk_inst.STORE_REG])
          h_add_a_src_imm := by
            exact decide_eq_true haddASrc
          h_add_b_src_imm := by
            change decide (rows.first_row.b_src = zisk_inst.SRC_IMM) =
              decide ((regidx_to_fin c.rs1).val = 0)
            unfold JalrRegisterOrX0SourcePins at haddSrc
            rcases haddSrc with hz | hn
            · change input.rs1 = 0#u32 ∧ rows.first_row.b_src = zisk_inst.SRC_IMM ∧
                  rows.first_row.b_use_sp_imm1 = 0#u64 ∧
                  rows.first_row.b_offset_imm0 = 0#u64 at hz
              have hrs1Zero : (regidx_to_fin c.rs1).val = 0 := by
                rw [← show input.rs1.val = (regidx_to_fin c.rs1).val by
                  simpa [rs1] using hrs1]
                exact congrArg UScalar.val hz.1
              rw [decide_eq_true hrs1Zero]
              exact decide_eq_true hz.2.1
            · change input.rs1 ≠ 0#u32 ∧ rows.first_row.b_src = zisk_inst.SRC_REG ∧
                  rows.first_row.b_use_sp_imm1 = 0#u64 ∧
                  rows.first_row.b_offset_imm0 = UScalar.cast UScalarTy.U64 input.rs1 at hn
              have hrs1Nonzero : (regidx_to_fin c.rs1).val ≠ 0 := by
                intro hzero
                apply hn.1
                apply UScalar.eq_of_val_eq
                simpa [rs1, hzero] using hrs1.symm
              rw [decide_eq_false hrs1Nonzero]
              exact decide_eq_false (by
                rw [hn.2.1]
                simp [zisk_inst.SRC_REG, zisk_inst.SRC_IMM])
          h_add_b_src_reg := by
            change decide (rows.first_row.b_src = zisk_inst.SRC_REG) =
              decide ((regidx_to_fin c.rs1).val ≠ 0)
            unfold JalrRegisterOrX0SourcePins at haddSrc
            rcases haddSrc with hz | hn
            · change input.rs1 = 0#u32 ∧ rows.first_row.b_src = zisk_inst.SRC_IMM ∧
                  rows.first_row.b_use_sp_imm1 = 0#u64 ∧
                  rows.first_row.b_offset_imm0 = 0#u64 at hz
              have hrs1Zero : (regidx_to_fin c.rs1).val = 0 := by
                rw [← show input.rs1.val = (regidx_to_fin c.rs1).val by
                  simpa [rs1] using hrs1]
                exact congrArg UScalar.val hz.1
              have hnot : ¬((regidx_to_fin c.rs1).val ≠ 0) := by
                intro hne
                exact hne hrs1Zero
              rw [decide_eq_false hnot]
              exact decide_eq_false (by
                intro heq
                have hbad := hz.2.1.symm.trans heq
                simp [zisk_inst.SRC_IMM, zisk_inst.SRC_REG] at hbad)
            · change input.rs1 ≠ 0#u32 ∧ rows.first_row.b_src = zisk_inst.SRC_REG ∧
                  rows.first_row.b_use_sp_imm1 = 0#u64 ∧
                  rows.first_row.b_offset_imm0 = UScalar.cast UScalarTy.U64 input.rs1 at hn
              have hrs1Nonzero : (regidx_to_fin c.rs1).val ≠ 0 := by
                intro hzero
                apply hn.1
                apply UScalar.eq_of_val_eq
                simpa [rs1, hzero] using hrs1.symm
              rw [decide_eq_true hrs1Nonzero]
              exact decide_eq_true hn.2.1
          andBits := andBits
          h_and_ieo := by
            exact handIeo
          h_and_m32 := by
            exact handM32
          h_and_set_pc := by
            exact handSetPc
          h_and_store_pc := by
            change rows.last_row.store_pc =
              decide ((regidx_to_fin c.rd).val ≠ 0)
            unfold JalrDestinationPins at handDest
            rcases handDest with hz | hn
            · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
                  rows.last_row.store_offset = 0#i64 ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = false at hz
              have hrdZero : (regidx_to_fin c.rd).val = 0 := by
                rw [← hrd]
                exact congrArg UScalar.val hz.1
              simp [hz.2.2.2.2, hrdZero]
            · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
                  rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hn
              have hrdNonzero : (regidx_to_fin c.rd).val ≠ 0 := by
                intro hzero
                apply hn.1
                apply UScalar.eq_of_val_eq
                simpa [hzero] using hrd.symm
              simp [hn.2.2.2.2, hrdNonzero]
          h_and_store_ind := by
            unfold JalrDestinationPins at handDest
            rcases handDest with hz | hn
            · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
                  rows.last_row.store_offset = 0#i64 ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = false at hz
              exact decide_eq_false (by
                rw [hz.2.1]
                simp [zisk_inst.STORE_IND])
            · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
                  rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hn
              exact decide_eq_false (by
                rw [hn.2.1]
                simp [zisk_inst.STORE_REG, zisk_inst.STORE_IND])
          h_and_store_reg := by
            change decide (rows.last_row.store = zisk_inst.STORE_REG) =
              decide ((regidx_to_fin c.rd).val ≠ 0)
            unfold JalrDestinationPins at handDest
            rcases handDest with hz | hn
            · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
                  rows.last_row.store_offset = 0#i64 ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = false at hz
              have hrdZero : (regidx_to_fin c.rd).val = 0 := by
                rw [← hrd]
                exact congrArg UScalar.val hz.1
              rw [decide_eq_false (by omega : ¬(regidx_to_fin c.rd).val ≠ 0)]
              exact decide_eq_false (by
                rw [hz.2.1]
                simp [zisk_inst.STORE_REG])
            · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
                  rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hn
              have hrdNonzero : (regidx_to_fin c.rd).val ≠ 0 := by
                intro hzero
                apply hn.1
                apply UScalar.eq_of_val_eq
                simpa [hzero] using hrd.symm
              rw [decide_eq_true hrdNonzero]
              exact decide_eq_true hn.2.1
          h_and_b_src_imm := by
            simp [andBits, romFlagBitsOfExtract, handBSrc, zisk_inst.SRC_C,
              zisk_inst.SRC_IMM]
          h_and_b_src_mem := by
            simp [andBits, romFlagBitsOfExtract, handBSrc, zisk_inst.SRC_C,
              zisk_inst.SRC_MEM]
          h_and_b_src_ind := by
            simp [andBits, romFlagBitsOfExtract, handBSrc, zisk_inst.SRC_C,
              zisk_inst.SRC_IND]
          h_and_b_src_reg := by
            simp [andBits, romFlagBitsOfExtract, handBSrc, zisk_inst.SRC_C,
              zisk_inst.SRC_REG]
          h_prog_add := by
            intro j hline
            obtain ⟨k, hk, haddr, hraw⟩ := hLineAdd j hline
            have hprimary := primary_row_of_programRowsBinding hbind
              ⟨k, hk, haddr, hraw⟩
            have hmsg : trace.program j = romRowOf (addr k) rows.first_row := by
              rw [hprimary]
              unfold romMessagesOfRaw
              rw [show aeneas_extract.extract_transpile_rv64im_rows_raw
                  (ZiskFv.Compliance.Decode.toU32
                    (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                      (regidx_to_fin c.rs1).val 0 (regidx_to_fin c.rd).val 0x67)) =
                    .ok rows by simpa only [rd, rs1, imm] using hrows]
              simp [hcount']
              rw [← haddr]
            have himmRow := jalr_immediate_rom_value c.imm input himmC
              rows.first_row haddASrc haddHi haddLo
            simp [hmsg, romRowOf, haddOp, haddJ2, haddASrc, haddHi,
              addBits, himmRow]
          h_prog_and := by
            intro j hline
            obtain ⟨k, hj, haddr, hraw⟩ := hLineAnd j hline
            have hprimary : RawAtProgramStart start addr rawProgram (start k) (addr k)
                (rawProgram k) := ⟨k, rfl, rfl, rfl⟩
            have hsecond : (romMessagesOfRaw (addr k) (rawProgram k)).2 =
                some (romRowOf (addr k + 1) rows.last_row) := by
              rw [hraw]
              unfold romMessagesOfRaw
              rw [show aeneas_extract.extract_transpile_rv64im_rows_raw
                  (ZiskFv.Compliance.Decode.toU32
                    (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
                      (regidx_to_fin c.rs1).val 0 (regidx_to_fin c.rd).val 0x67)) =
                    .ok rows by simpa only [rd, rs1, imm] using hrows]
              simp [hcount']
            obtain ⟨hsucc, hmsg⟩ :=
              successor_row_of_programRowsBinding hbind hprimary hsecond
            have hjEq : j = ⟨(start k).val + 1, hsucc⟩ := Fin.ext hj
            subst j
            unfold JalrDestinationPins at handDest
            rcases handDest with hz | hn
            · change input.rd = 0#u32 ∧ rows.last_row.store = 0#u64 ∧
                  rows.last_row.store_offset = 0#i64 ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = false at hz
              have hrdZero : (regidx_to_fin c.rd).val = 0 := by
                rw [← hrd]
                exact congrArg UScalar.val hz.1
              have hstoreZero := congrArg IScalar.val hz.2.2.1
              simp [hmsg, romRowOf, handOp, handJ1, handJ2,
                hz, andBits, hrdZero]
            · change input.rd ≠ 0#u32 ∧ rows.last_row.store = zisk_inst.STORE_REG ∧
                  rows.last_row.store_offset = UScalar.hcast IScalarTy.I64 input.rd ∧
                  rows.last_row.store_use_sp = false ∧ rows.last_row.store_pc = true at hn
              have hrdNonzero : (regidx_to_fin c.rd).val ≠ 0 := by
                intro hzero
                apply hn.1
                apply UScalar.eq_of_val_eq
                simpa [hzero] using hrd.symm
              have hstoreVal := congrArg IScalar.val hn.2.2.1
              have hstoreOffset :
                  ((rows.last_row.store_offset.val : Int) : FGL) =
                    Transpiler.ind (regidx_to_fin c.rd) := by
                have hrdPrime : (regidx_to_fin c.rd).val < GL_prime :=
                  lt_trans (regidx_to_fin c.rd).isLt (by norm_num)
                apply Fin.ext
                simp [hstoreVal, hcast_u32_i64_val, hrd, Transpiler.ind, hrdPrime]
              simp [hmsg, romRowOf, handOp, handJ1, handJ2,
                hn, andBits, hrdNonzero]
              simpa only [hstoreVal] using hstoreOffset }

end ZiskFv.Compliance.RawProgramBinding
