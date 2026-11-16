import ZiskFv.Compliance.TraceLevelExport.RawProgramDecode

/-!
# Load A-slot pins from the committed production lowering

The accepted Main ROM lookup, the existing architectural raw-word lookup, and
`ProgramRowsBinding` identify one and the same serialized production row. Main
flag Booleanity and `packFlags_inj` then recover its A-source columns. These are
outputs of the existing root evidence, not additional decode or caller fields.
Architectural x0 is the production lowerer's immediate-zero case; only nonzero
registers use the register source.
-/

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks

namespace ZiskFv.Compliance.LoadOperandBinding

open ZiskFv.Compliance.RawProgramBinding
open ZiskFv.Compliance.RomDecodeBinding
open ZiskFv.AirsClean.FullEnsemble (mainOfTable mainOfTable_pc)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags romFlags romMessage)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

/-- Actual Main A-slot columns, including the real immediate-zero optimization.
The register index is the decoded five-bit index, not a register-file value. -/
structure LoadMainASourcePins {n : Nat} (trace : AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (rs1 : Nat) : Prop where
  h_a_src_imm : (mainRowWithRomLd trace i).rom.a_src_imm =
    ZiskFv.AirsClean.boolF (decide (rs1 = 0))
  h_a_src_reg : (mainRowWithRomLd trace i).rom.a_src_reg =
    ZiskFv.AirsClean.boolF (decide (rs1 ≠ 0))
  h_a_src_mem : (mainRowWithRomLd trace i).rom.a_src_mem = 0
  h_a_offset_imm0 : (mainRowWithRomLd trace i).rom.a_offset_imm0 = (rs1 : FGL)
  h_a_imm1 : (mainRowWithRomLd trace i).rom.a_imm1 = 0
  h_is_precompiled : (mainRowWithRomLd trace i).rom.is_precompiled = 0

private theorem bool_of_booleanity {col : FGL} (h : col * (1 - col) = 0) :
    ∃ b : Bool, col = ZiskFv.AirsClean.boolF b := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨false, by simpa [ZiskFv.AirsClean.boolF] using h0⟩
  · exact ⟨true, by
      simp only [ZiskFv.AirsClean.boolF_true]
      exact (sub_eq_zero.mp h1).symm⟩

/-- Extend the existing source-column projections to the A-memory and
precompiled columns, using the same Booleanity and flag-packing injectivity. -/
private theorem loadAFlagColumns_of_packFlags {n : Nat}
    (trace : AcceptedZiskTrace n) (i : Fin trace.numInstructions)
    (bits : RomFlagBits)
    (h : romFlags (mainRowWithRomLd trace i) = packFlags bits) :
    (mainRowWithRomLd trace i).rom.a_src_imm = ZiskFv.AirsClean.boolF bits.a_src_imm ∧
    (mainRowWithRomLd trace i).rom.a_src_reg = ZiskFv.AirsClean.boolF bits.a_src_reg ∧
    (mainRowWithRomLd trace i).rom.a_src_mem = ZiskFv.AirsClean.boolF bits.a_src_mem ∧
    (mainRowWithRomLd trace i).rom.is_precompiled =
      ZiskFv.AirsClean.boolF bits.is_precompiled := by
  obtain ⟨hb_ieo, hb_m32, hb_set_pc, hb_store_pc, hb_a_src_imm, hb_a_src_mem,
    hb_is_precompiled, hb_b_src_imm, hb_b_src_mem, hb_store_mem, hb_store_ind,
    hb_b_src_ind, hb_a_src_reg, hb_b_src_reg, hb_store_reg⟩ :=
    mainRow_flags_boolean trace ⟨i.val, trace.mainTable_index i⟩
  obtain ⟨d_ieo, e_ieo⟩ := bool_of_booleanity hb_ieo
  obtain ⟨d_m32, e_m32⟩ := bool_of_booleanity hb_m32
  obtain ⟨d_set_pc, e_set_pc⟩ := bool_of_booleanity hb_set_pc
  obtain ⟨d_store_pc, e_store_pc⟩ := bool_of_booleanity hb_store_pc
  obtain ⟨d_a_src_imm, e_a_src_imm⟩ := bool_of_booleanity hb_a_src_imm
  obtain ⟨d_a_src_mem, e_a_src_mem⟩ := bool_of_booleanity hb_a_src_mem
  obtain ⟨d_is_precompiled, e_is_precompiled⟩ := bool_of_booleanity hb_is_precompiled
  obtain ⟨d_b_src_imm, e_b_src_imm⟩ := bool_of_booleanity hb_b_src_imm
  obtain ⟨d_b_src_mem, e_b_src_mem⟩ := bool_of_booleanity hb_b_src_mem
  obtain ⟨d_store_mem, e_store_mem⟩ := bool_of_booleanity hb_store_mem
  obtain ⟨d_store_ind, e_store_ind⟩ := bool_of_booleanity hb_store_ind
  obtain ⟨d_b_src_ind, e_b_src_ind⟩ := bool_of_booleanity hb_b_src_ind
  obtain ⟨d_a_src_reg, e_a_src_reg⟩ := bool_of_booleanity hb_a_src_reg
  obtain ⟨d_b_src_reg, e_b_src_reg⟩ := bool_of_booleanity hb_b_src_reg
  obtain ⟨d_store_reg, e_store_reg⟩ := bool_of_booleanity hb_store_reg
  have hpack : romFlags (mainRowWithRomLd trace i) =
      packFlags ⟨d_a_src_imm, d_a_src_mem, d_is_precompiled, d_b_src_imm,
        d_b_src_mem, d_ieo, d_store_pc, d_store_mem, d_store_ind, d_set_pc,
        d_m32, d_b_src_ind, d_a_src_reg, d_b_src_reg, d_store_reg⟩ := by
    simp only [mainRowWithRomLd, romFlags, packFlags, e_ieo, e_m32, e_set_pc,
      e_store_pc, e_a_src_imm, e_a_src_mem, e_is_precompiled, e_b_src_imm,
      e_b_src_mem, e_store_mem, e_store_ind, e_b_src_ind, e_a_src_reg,
      e_b_src_reg, e_store_reg]
  have hbits := packFlags_inj (hpack.symm.trans h)
  subst hbits
  exact ⟨e_a_src_imm, e_a_src_reg, e_a_src_mem, e_is_precompiled⟩

private theorem signedOffset_eq_loadIndex (x : Std.U64) (rs1 : Nat)
    (hrs1 : rs1 < 32) (h : x.val = rs1) : signedOffset x = (rs1 : FGL) := by
  have hnonneg : 2 * x.val < 18446744073709551616 := by
    rw [h]
    omega
  have hsigned : signedOffset x = (x.bv.toNat : FGL) := by
    simp [signedOffset, BitVec.toInt, if_pos hnonneg]
  have hx : x.bv.toNat = rs1 := by simpa only [UScalar.val] using h
  exact hsigned.trans (congrArg (fun v : Nat => (v : FGL)) hx)

/-- A private composition of the existing same-world certificates. In particular,
`hLine` is precisely the existing `RawProgramDecode_<op>.hLine` projection. -/
private theorem loadMainASourcePins_of_lowering {n rawLength : Nat}
    (trace : AcceptedZiskTrace n) (i : Fin trace.numInstructions)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (raw : BitVec 32) (ext : aeneas_extract.Rv64imTranspileExtract)
    (rs1 : Nat) (hrs1 : rs1 < 32)
    (hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line = (mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength, addr k = (trace.program j).line ∧ rawProgram k = raw)
    (hok : aeneas_extract.extract_transpile_rv64im_raw
      (ZiskFv.Compliance.Decode.toU32 raw) = .ok ext)
    (hnon : (ZiskFv.Compliance.Decode.toU32 raw &&& 127#u32) ≠ 103#u32)
    (hpins : LoadASourcePins ext.row rs1) : LoadMainASourcePins trace i rs1 := by
  obtain ⟨j, hj⟩ := mainRomMessage_at_eq_program trace
    ⟨i.val, trace.mainTable_index i⟩
  have hline : (trace.program j).line =
      (mainOfTable trace.program trace.mainTable).pc i.val := by
    simp only [← hj, romMessage, mainOfTable_pc]
  have hser := serialized_of_raw_program_binding trace i start addr rawProgram
    raw ext hbind hLine hok hnon j hline
  have hrom : romMessage (mainRowWithRomLd trace i) =
      serializeExtract (trace.program j).line ext.row := hj.trans hser
  have hflags : romFlags (mainRowWithRomLd trace i) =
      packFlags (romFlagBitsOfExtract ext.row) :=
    congrArg (fun msg : ZiskRomMessage FGL => msg.flags) hrom
  obtain ⟨himm, hreg, hmem, hpre⟩ :=
    loadAFlagColumns_of_packFlags trace i (romFlagBitsOfExtract ext.row) hflags
  obtain ⟨hsrc, hoff, hsp, hpc⟩ := hpins
  have hbimm : (romFlagBitsOfExtract ext.row).a_src_imm = decide (rs1 = 0) := by
    by_cases hz : rs1 = 0 <;>
      simp [romFlagBitsOfExtract, hsrc, hz, zisk_inst.SRC_IMM, zisk_inst.SRC_REG]
  have hbreg : (romFlagBitsOfExtract ext.row).a_src_reg = decide (rs1 ≠ 0) := by
    by_cases hz : rs1 = 0 <;>
      simp [romFlagBitsOfExtract, hsrc, hz, zisk_inst.SRC_IMM, zisk_inst.SRC_REG]
  have hbmem : (romFlagBitsOfExtract ext.row).a_src_mem = false := by
    by_cases hz : rs1 = 0 <;>
      simp [romFlagBitsOfExtract, hsrc, hz, zisk_inst.SRC_IMM,
        zisk_inst.SRC_REG, zisk_inst.SRC_MEM]
  refine
    { h_a_src_imm := by rw [himm, hbimm]
      h_a_src_reg := by rw [hreg, hbreg]
      h_a_src_mem := by rw [hmem, hbmem, ZiskFv.AirsClean.boolF_false]
      h_a_offset_imm0 := ?_
      h_a_imm1 := ?_
      h_is_precompiled := by
        simpa only [romFlagBitsOfExtract, hpc, ZiskFv.AirsClean.boolF_false] using hpre }
  · have heq := congrArg (fun msg : ZiskRomMessage FGL => msg.a_offset_imm0) hrom
    change (mainRowWithRomLd trace i).rom.a_offset_imm0 =
      signedOffset ext.row.a_offset_imm0 at heq
    exact heq.trans (signedOffset_eq_loadIndex ext.row.a_offset_imm0 rs1 hrs1 hoff)
  · have heq := congrArg (fun msg : ZiskRomMessage FGL => msg.a_imm1) hrom
    change (mainRowWithRomLd trace i).rom.a_imm1 =
      sourceImmediate ext.row.a_src ext.row.a_use_sp_imm1 at heq
    rw [heq]
    rw [hsp]
    unfold sourceImmediate
    split <;> rfl

/-- Each public constructor consumes only its existing same-world raw decode and
program binding. Success and A-source pins come from the actual production
lowering, including the x0 immediate branch. -/
local macro "load_main_a_source" nm:ident "," f3:term : command => do
  let s := nm.getId.toString
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple
    ("loadMainASource_" ++ s ++ "_of_rawProgramDecode"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let rawName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("RawProgramDecode_" ++ s))
  let transpileName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("transpile_" ++ s))
  let pinsName := Lean.mkIdent ((`ZiskFv.Compliance.RawProgramBinding).str
    ("transpile_" ++ s ++ "_a_source_pins"))
  `(theorem $ctorName {n rawLength : Nat}
      (trace : AcceptedZiskTrace n) (i : Fin trace.numInstructions)
      (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      LoadMainASourcePins trace i (storeRegBits c.r1).toNat := by
    obtain ⟨ext, hok, _⟩ := $transpileName
      (storeRegBits c.rd).toNat (storeRegBits c.r1).toNat c.imm.toNat
      (storeRegBits c.rd).isLt (storeRegBits c.r1).isLt
    refine loadMainASourcePins_of_lowering trace i start addr rawProgram hbind
      (ZiskFv.Completeness.Rv64imShapes.rawIType c.imm.toNat
        (storeRegBits c.r1).toNat $f3 (storeRegBits c.rd).toNat 0x03)
      ext (storeRegBits c.r1).toNat (storeRegBits c.r1).isLt
      rawDecode.hLine hok ?_ ?_
    · rw [ZiskFv.Compliance.Decode.toU32_and127,
        ZiskFv.Compliance.Decode.rawIType_opcode]
      all_goals decide
    · exact $pinsName
        (storeRegBits c.rd).toNat (storeRegBits c.r1).toNat c.imm.toNat
        (storeRegBits c.rd).isLt (storeRegBits c.r1).isLt ext hok)

load_main_a_source ld, 3
load_main_a_source lbu, 4
load_main_a_source lhu, 5
load_main_a_source lwu, 6
load_main_a_source lb, 0
load_main_a_source lh, 1
load_main_a_source lw, 2

end ZiskFv.Compliance.LoadOperandBinding
