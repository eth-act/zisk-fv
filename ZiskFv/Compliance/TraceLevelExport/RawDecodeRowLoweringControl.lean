import ZiskFv.Compliance.TraceLevelExport.RawDecodeRowLoweringBase

/-!
# Source widths for the existing control raw-decode evidence

The non-JALR proofs reuse the terminal source theorems in
`RawProgramBindingControl`; acceptance follows from a proved live row pin.
For JALR, the existing certificate supplies the actual rows computation and
count. Acceptance is recovered from the real encoder/decoder and supported
JALR lowering tag, including `rd = x0`, without a new caller premise.
Source: ZisK `9ca88b5`, `core/src/aeneas_extract.rs:361–412`.
-/

namespace ZiskFv.Compliance.RawDecodeRowLowering

open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

set_option maxHeartbeats 8000000

theorem sourceWidth_beq {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_beq trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_beq trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_beq
    (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val c.imm.toNat
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
      (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawBType_opcode, Decode.toU32_ofNat]
    decide

theorem sourceWidth_bne {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_bne trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_bne trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_bne
    (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val c.imm.toNat
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
      (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 1) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawBType_opcode, Decode.toU32_ofNat]
    decide

theorem sourceWidth_blt {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_blt trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_blt trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_blt
    (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val c.imm.toNat
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
      (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 4) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawBType_opcode, Decode.toU32_ofNat]
    decide

theorem sourceWidth_bge {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_bge trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_bge trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_bge
    (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val c.imm.toNat
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
      (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 5) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawBType_opcode, Decode.toU32_ofNat]
    decide

theorem sourceWidth_bltu {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_bltu trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_bltu trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_bltu
    (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val c.imm.toNat
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
      (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 6) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawBType_opcode, Decode.toU32_ofNat]
    decide

theorem sourceWidth_bgeu {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_bgeu trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_bgeu trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_bgeu
    (regidx_to_fin c.r1).val (regidx_to_fin c.r2).val c.imm.toNat
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
      (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 7) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawBType_opcode, Decode.toU32_ofNat]
    decide

theorem sourceWidth_lui {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_lui trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_lui trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, hop, _⟩ := transpile_lui
    (regidx_to_fin c.rd).val ((c.imm ++ (0 : BitVec 12)).toNat)
    (regidx_to_fin c.rd).isLt
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inl (by rw [hop]; decide))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawUType (c.imm ++ (0 : BitVec 12)).toNat
      (regidx_to_fin c.rd).val 0x37) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawUType_opcode ((c.imm ++ (0 : BitVec 12)).toNat) (regidx_to_fin c.rd).val 0x37 (by norm_num),
      Decode.toU32_ofNat]
    decide

theorem sourceWidth_auipc {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_auipc trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_auipc trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, _, _, _, _, hstorepc, _⟩ := transpile_auipc
    (regidx_to_fin c.rd).val ((c.imm ++ (0 : BitVec 12)).toNat)
    (regidx_to_fin c.rd).isLt rawDecode.h_rd_ne_zero
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inr (Or.inr hstorepc))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawUType (c.imm ++ (0 : BitVec 12)).toNat
      (regidx_to_fin c.rd).val 0x17) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawUType_opcode ((c.imm ++ (0 : BitVec 12)).toNat) (regidx_to_fin c.rd).val 0x17 (by norm_num),
      Decode.toU32_ofNat]
    decide

theorem sourceWidth_jal {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_jal trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_jal trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, _, _, _, _, hstorepc, _⟩ := transpile_jal
    (regidx_to_fin c.rd).val (c.imm.toNat)
    (regidx_to_fin c.rd).isLt rawDecode.h_rd_ne_zero
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inr (Or.inr hstorepc))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawJType c.imm.toNat
      (regidx_to_fin c.rd).val) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawJType_opcode,
      Decode.toU32_ofNat]
    decide

theorem sourceWidth_fence {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_fence trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecode_fence trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  obtain ⟨terminal, source, _, _, _, _, _, hjump, _⟩ :=
    transpile_fence c.fenceP.toNat c.fenceS.toNat
      (by have h := c.fenceP.isLt; norm_num at h ⊢; exact h)
      (by have h := c.fenceS.isLt; norm_num at h ⊢; exact h)
  have accepted := accepted_of_live_terminal _ terminal source
    (Or.inr (Or.inl (by rw [hjump]; decide)))
  refine at_pc_of_word trace i addr rawProgram
    (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence
      c.fenceP.toNat c.fenceS.toNat) 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨oneOfTerminal terminal source accepted ?_, rfl⟩
    rw [Decode.toU32_and127, Decode.rawSupportedFence_opcode,
      Decode.toU32_ofNat]
    decide

/-- The rows certificate did not store acceptance. Recover it from the
supported JALR tag in the actual source computation, not from `rd ≠ 0`. -/
private theorem accepted_of_jalr_rows (rd rs1 imm : Nat)
    (_hrd : rd < 32) (_hrs1 : rs1 < 32)
    (rows : aeneas_extract.Rv64imTranspileRowsExtract)
    (source : aeneas_extract.extract_transpile_rv64im_rows_raw
      (Decode.toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType
        imm rs1 0 rd 0x67)) = .ok rows) : rows.accepted = true := by
  let raw := ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67
  have htag : (Decode.toU32 raw &&& 127#u32) = 103#u32 := by
    rw [Decode.toU32_and127,
      Decode.rawIType_opcode imm rs1 0 rd 0x67 (by norm_num)]
    rfl
  have hdec : aeneas_extract.rv64im_decode.decode_32_core (Decode.toU32 raw) =
      aeneas_extract.rv64im_decode.decode_i (Decode.toU32 raw)
        aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift,
      Bind.bind, bind_ok, htag]
    rfl
  obtain ⟨decoded, hdecoded, hopd, _⟩ := Extraction.decode_i_bounds
    (Decode.toU32 raw) aeneas_extract.rv64im_decode.RiscvOpcode.Jalr false
  have terminalAccepted (terminal : aeneas_extract.Rv64imTranspileExtract)
      (hsource : aeneas_extract.extract_transpile_rv64im_raw
        (Decode.toU32 raw) = .ok terminal) : terminal.accepted = true := by
    unfold aeneas_extract.extract_transpile_rv64im_raw at hsource
    rw [hdec, hdecoded] at hsource
    simp only [Bind.bind, bind_ok] at hsource
    obtain ⟨_, _, hsource⟩ := Extraction.bind_eq_ok_imp hsource
    rw [hopd] at hsource
    simp only [aeneas_extract.lowering_opcode, Bind.bind, bind_ok] at hsource
    obtain ⟨_, _, hsource⟩ := Extraction.bind_eq_ok_imp hsource
    obtain ⟨_, _, hsource⟩ := Extraction.bind_eq_ok_imp hsource
    obtain ⟨_, _, hsource⟩ := Extraction.bind_eq_ok_imp hsource
    obtain ⟨_, _, hsource⟩ := Extraction.bind_eq_ok_imp hsource
    exact (congrArg aeneas_extract.Rv64imTranspileExtract.accepted
      (Result.ok.inj hsource)).symm
  change aeneas_extract.extract_transpile_rv64im_rows_raw
    (Decode.toU32 raw) = .ok rows at source
  unfold aeneas_extract.extract_transpile_rv64im_rows_raw at source
  obtain ⟨terminal, hterminal, source⟩ := Extraction.bind_eq_ok_imp source
  have accepted := terminalAccepted terminal hterminal
  simp only [lift, Bind.bind, bind_ok, htag, accepted, if_true] at source
  obtain ⟨_, _, source⟩ := Extraction.bind_eq_ok_imp source
  split at source
  · obtain ⟨_, _, source⟩ := Extraction.bind_eq_ok_imp source
    obtain ⟨_, _, source⟩ := Extraction.bind_eq_ok_imp source
    obtain ⟨_, _, source⟩ := Extraction.bind_eq_ok_imp source
    exact (congrArg aeneas_extract.Rv64imTranspileRowsExtract.accepted
      (Result.ok.inj source)).symm
  · exact (congrArg aeneas_extract.Rv64imTranspileRowsExtract.accepted
      (Result.ok.inj source)).symm

/-- The aligned old certificate already pins the actual source width to one. -/
theorem sourceWidth_jalr_aligned {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecodeJalrAligned trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 1 := by
  have accepted : rawDecode.h_rows.rows.accepted = true := by
    apply accepted_of_jalr_rows (regidx_to_fin c.rd).val
      (regidx_to_fin c.rs1).val c.imm.toNat
      (regidx_to_fin c.rd).isLt (regidx_to_fin c.rs1).isLt
    rw [← rawDecode.h_raw]
    exact rawDecode.h_rows.h_extract
  refine at_pc_of_word trace i addr rawProgram rawDecode.raw 1 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLine j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨⟨rawDecode.h_rows.rows, rawDecode.h_rows.h_extract, accepted⟩, ?_⟩
    change rawDecode.h_rows.rows.row_count.val = 1
    rw [rawDecode.h_rows.h_count]
    rfl

/-- The expanded old certificate already pins the actual source width to two. -/
theorem sourceWidth_jalr_unaligned {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (rawDecode : RawProgramDecodeJalrUnaligned trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram 2 := by
  have accepted : rawDecode.h_rows.rows.accepted = true := by
    apply accepted_of_jalr_rows (regidx_to_fin c.rd).val
      (regidx_to_fin c.rs1).val c.imm.toNat
      (regidx_to_fin c.rd).isLt (regidx_to_fin c.rs1).isLt
    rw [← rawDecode.h_raw]
    exact rawDecode.h_rows.h_extract
  refine at_pc_of_word trace i addr rawProgram rawDecode.raw 2 ?_ ?_
  · intro j hj
    obtain ⟨k, _, haddr, hword⟩ := rawDecode.hLineAdd j hj
    exact ⟨k, haddr, hword⟩
  · refine ⟨⟨rawDecode.h_rows.rows, rawDecode.h_rows.h_extract, accepted⟩, ?_⟩
    change rawDecode.h_rows.rows.row_count.val = 2
    rw [rawDecode.h_rows.h_count]
    rfl

/-- Exact agreement with the producer selected by the existing raw → program
→ row decode construction. No alignment or source-success premise is added. -/
theorem sourceWidth_jalr {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : Claim_jalr trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_jalr trace i c start addr rawProgram) :
    SourceWidthAt trace i addr rawProgram
      (stepProducerRow i (.jalr c)
        (rowDecode_of_programDecode trace i
          (programDecode_of_rawProgramDecode trace i (.jalr c) start addr
            rawProgram hbind ⟨⟨rawDecode⟩⟩)) + 1 - i.val) := by
  cases rawDecode with
  | aligned evidence =>
      have producer : stepProducerRow i (.jalr c)
          (rowDecode_of_programDecode trace i
            (programDecode_of_rawProgramDecode trace i (.jalr c) start addr
              rawProgram hbind ⟨⟨.aligned evidence⟩⟩)) = i.val := by
        rcases evidence with ⟨raw, hraw, cert, hOffset, hidx, hflag, haLo, haHi,
          hc1, heven, hnonneg, hlt, hLine⟩
        subst raw
        rcases cert with ⟨rows, hsource, hcount⟩
        simp only [programDecode_of_rawProgramDecode, ProgramDecode_jalr_from_rawProgram]
        generalize_proofs
        casesm* _ ∧ _
        rfl
      rw [producer]
      simpa only [Nat.add_sub_cancel_left] using
        sourceWidth_jalr_aligned trace i c start addr rawProgram evidence
  | unaligned evidence =>
      have producer : stepProducerRow i (.jalr c)
          (rowDecode_of_programDecode trace i
            (programDecode_of_rawProgramDecode trace i (.jalr c) start addr
              rawProgram hbind ⟨⟨.unaligned evidence⟩⟩)) = i.val + 1 := by
        rcases evidence with ⟨raw, hraw, cert, hOffset, hidx, hflagAdd, hflag,
          haLo, haHi, hc1, heven, hnonneg, hlt, hLineAdd, hLineAnd⟩
        subst raw
        rcases cert with ⟨rows, hsource, hcount⟩
        simp only [programDecode_of_rawProgramDecode, ProgramDecode_jalr_from_rawProgram]
        generalize_proofs
        casesm* _ ∧ _
        rfl
      rw [producer]
      have width : i.val + 1 + 1 - i.val = 2 := by omega
      rw [width]
      exact sourceWidth_jalr_unaligned trace i c start addr rawProgram evidence

end ZiskFv.Compliance.RawDecodeRowLowering
