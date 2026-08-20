import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister

/-!
# Raw-program decode bridge — M-extension family (issue #159, BLOCK 3)

The twelve remaining RV64IM M-extension opcodes (MUL, MULH, MULHSU, MULHU,
DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW, REMUW; MULW already lives in the
register family).  All are register-register R-type ops with `funct7 = 1`, so
they route UNCONDITIONALLY to `create_register_op_typed` — the same lowering
shape as the base ALU register ops.  Their decode/transpile/decode-field
bridges therefore reuse the generic register lemmas verbatim:

  * `transpile_<op>` — reuses `transpile_register_of` (#159 block-3
    `RawProgramBindingRegister`), discharging the static op-type pins by `rfl`
    (`ZiskOp.code`/`is_m32`/`op_type`) and the decode classification by the
    `rawRType_{opcode,funct3,funct7}` masks (`funct7 = 1`).
  * `<op>_decode_fields_of_binding` — reuses `register_decode_fields_of_binding`.
  * `ProgramDecode_<op>_from_rawProgram` — rebuilds the committed-program decode
    bundle from `rawProgram` + `ProgramRowsBinding` + the `<op>`-shaped raw-word
    hypothesis + `h_idx`, with NO per-op ROM decode premise.

**Bespoke part.**  Unlike the base ALU ops, each M-ext `Decode_<op>_of_program`
carries HETEROGENEOUS non-ROM operand/arith-side witnesses that are OUTSIDE the
ROM decode-from-raw scope (they belong to block 2 / pre-existing arith trust
classes).  They are threaded VERBATIM as caller hypotheses on
`Decode_<op>_from_rawProgram`, exactly as the signed loads thread their
`BinaryExtension` witnesses.  Three witness shapes occur:

  * group A (`arith_mem` + `bounds` over `c.bus.e2`): MUL, MULH, MULHSU;
  * group B (`pins` + `arith_mem` + `bounds`): DIV, REM, DIVW, REMW;
  * group C (`bounds` over `(busSub …).e2`): MULHU, DIVU, DIVUW, REMU, REMUW.

The defect-gating (`h_not_forge`) is NOT a `Decode` field — it lives in the
compliance/wrapper layer — so it is not threaded here.

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).
-/

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open Goldilocks
open ZiskFv.Compliance.Extraction
  (defCtx decode_r_bounds create_register_op_typed_ok decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem mextRawRTypeRd (funct7 rs2 rs1 funct3 rd opcode : Nat)
    (hrd : rd < 32) (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode) >>> 7)
        &&& 31#32 = BitVec.ofNat 32 rd := by
  simp only [ZiskFv.Completeness.Rv64imShapes.rawRType,
    ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro bit hbit
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (7 + bit ≥ 25) := by omega
  have e20 : ¬ (7 + bit ≥ 20) := by omega
  have e15 : ¬ (7 + bit ≥ 15) := by omega
  have e12 : ¬ (7 + bit ≥ 12) := by omega
  have e7 : 7 + bit ≥ 7 := by omega
  have hop' : opcode.testBit (7 + bit) = false :=
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hop
      (by calc (128 : Nat) = 2 ^ 7 := rfl
           _ ≤ 2 ^ (7 + bit) := Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [e25, e20, e15, e12, e7, hop', show 7 + bit - 7 = bit from by omega]

private theorem mextAnd3968Ushift7 (x : BitVec 32) :
    (x &&& 3968#32) >>> 7 = (x >>> 7) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : (i : Nat) < 32
  · interval_cases i <;>
      simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
        BitVec.getLsbD_ofNat, Nat.testBit]
  · have hi7 : ¬(i : Nat) + 7 < 32 := by omega
    simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and,
      BitVec.getLsbD_ofNat, hi, hi7]

/-! ## Shared transpile + decode-field lemmas (op-agnostic, register family).

    Emitted by every group macro; identical in body to the register macro's
    first two theorems (no witness dependence). -/

local macro "mext_lemmas" nm:ident "," f7:term "," f3:term "," opw:term "," rop:term ","
    srop:term "," zop:term "," opU8:term "," m32:term "," ot:term "," opc:ident : command => do
    let s := nm.getId.toString
    let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
    let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
    let t1 ← `(theorem $tName (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
          ∃ ext, extract_transpile_rv64im_raw
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw)) = ok ext
            ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
            ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
            ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
            ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
            ∧ ext.row.store_offset.val = rd
            ∧ ext.row.store ≠ zisk_inst.STORE_IND
            ∧ (rd ≠ 0 → ext.row.store = zisk_inst.STORE_REG) := by
        refine transpile_register_of _ $rop $srop $zop $opU8 $m32 $ot rd ?_ ?_ rfl
          (by intro self input; rfl)
          rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
        · intro d hd
          rw [aeneas_extract.rv64im_decode.decode_r] at hd
          simp only [aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_ok,
            Bind.bind] at hd
          obtain ⟨i1, hi1, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
          obtain ⟨i3, hi3, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
          obtain ⟨i5, hi5, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
          obtain ⟨i7, hi7, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
          obtain ⟨i9, hi9, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
          rw [Result.ok.injEq] at hd
          subst d
          have hi3' : i3 = toU32 (BitVec.ofNat 32 rd) := by
            have hcalc :
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType
                      $f7 rs2 rs1 $f3 rd $opw) &&& 3968#u32) >>> 7#i32 =
                  ok (toU32 (BitVec.ofNat 32 rd)) := by
              change (toU32
                  (ZiskFv.Completeness.Rv64imShapes.rawRType
                    $f7 rs2 rs1 $f3 rd $opw &&& 3968#32)) >>> 7#i32 =
                ok (toU32 (BitVec.ofNat 32 rd))
              rw [show (toU32
                    (ZiskFv.Completeness.Rv64imShapes.rawRType
                      $f7 rs2 rs1 $f3 rd $opw &&& 3968#32)) >>> 7#i32 =
                  ok (toU32
                    ((ZiskFv.Completeness.Rv64imShapes.rawRType
                      $f7 rs2 rs1 $f3 rd $opw &&& 3968#32) >>> 7)) by rfl]
              rw [mextAnd3968Ushift7,
                mextRawRTypeRd $f7 rs2 rs1 $f3 rd $opw hrd (by norm_num)]
            rw [hcalc] at hi3
            exact (Result.ok.inj hi3).symm
          rw [hi3']
          simp only [UScalar.val, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (lt_trans hrd (by norm_num))
        simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
          ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
          ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr25,
          ZiskFv.Compliance.Decode.rawRType_opcode $f7 rs2 rs1 $f3 rd $opw (by norm_num),
          ZiskFv.Compliance.Decode.rawRType_funct3 $f7 rs2 rs1 $f3 rd $opw (by norm_num) hrd (by norm_num),
          ZiskFv.Compliance.Decode.rawRType_funct7 $f7 rs2 rs1 $f3 rd $opw (by norm_num) hrs2 hrs1
            (by norm_num) hrd (by norm_num)]
        rfl)
    let t2 ← `(theorem $dfName (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
          (line : FGL) (msg : ZiskRomMessage FGL)
          (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw)) :
          msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
            ∧ msg.store_offset = (rd : FGL)
            ∧ ∃ ext, extract_transpile_rv64im_raw
                  (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw)) = ok ext
                ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
                ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
                ∧ (romFlagBitsOfExtract ext.row).store_ind = false
                ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
        obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
            hstoreOffset, hstoreInd, _⟩ := $tName rd rs1 rs2 hrd hrs1 hrs2
        obtain ⟨ho, hjo1, hjo2, hso, hsi, hf⟩ :=
          register_decode_fields_of_binding line msg _ $opU8 $opc rd ext
            (by simp [romOpcode, $opc:term]) hok hop hj1 hj2 hstoreOffset hstoreInd hbind
        exact ⟨ho, hjo1, hjo2, hso, ext, hok, hieo, hm32, hsetpc, hstorepc, hsi, hf⟩)
    return ⟨Lean.mkNullNode #[t1, t2]⟩

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

/-! ## Group A: MUL / MULH / MULHSU (`arith_mem` + `bounds` over `c.bus.e2`). -/

mext_lemmas mul, 1, 0, 0x33, RiscvOpcode.Mul, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mul, zisk_ops.ZiskOp.Mul, 180#u8, false, zisk_ops.OpType.ArithAm32, OP_MUL

mext_lemmas mulh, 1, 1, 0x33, RiscvOpcode.Mulh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulh, zisk_ops.ZiskOp.Mulh, 181#u8, false, zisk_ops.OpType.ArithAm32, OP_MULH

mext_lemmas mulhsu, 1, 2, 0x33, RiscvOpcode.Mulhsu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhsu, zisk_ops.ZiskOp.Mulsuh, 179#u8, false, zisk_ops.OpType.ArithAm32, OP_MULSUH

/-! ## Group B: DIV / REM / DIVW / REMW (`pins` + `arith_mem` + `bounds`). -/

mext_lemmas div, 1, 4, 0x33, RiscvOpcode.Div, riscv2zisk_single_row.Rv64imSingleRowOpcode.Div, zisk_ops.ZiskOp.Div, 186#u8, false, zisk_ops.OpType.ArithAm32, OP_DIV

mext_lemmas rem, 1, 6, 0x33, RiscvOpcode.Rem, riscv2zisk_single_row.Rv64imSingleRowOpcode.Rem, zisk_ops.ZiskOp.Rem, 187#u8, false, zisk_ops.OpType.ArithAm32, OP_REM

mext_lemmas divw, 1, 4, 0x3b, RiscvOpcode.Divw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divw, zisk_ops.ZiskOp.DivW, 190#u8, true, zisk_ops.OpType.ArithA32, OP_DIV_W

mext_lemmas remw, 1, 6, 0x3b, RiscvOpcode.Remw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remw, zisk_ops.ZiskOp.RemW, 191#u8, true, zisk_ops.OpType.ArithA32, OP_REM_W

/-! ## Group C: MULHU / DIVU / DIVUW / REMU / REMUW (`bounds` over `(busSub …).e2`). -/

mext_lemmas mulhu, 1, 3, 0x33, RiscvOpcode.Mulhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhu, zisk_ops.ZiskOp.Muluh, 177#u8, false, zisk_ops.OpType.ArithAm32, OP_MULUH

mext_lemmas divu, 1, 5, 0x33, RiscvOpcode.Divu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divu, zisk_ops.ZiskOp.Divu, 184#u8, false, zisk_ops.OpType.ArithAm32, OP_DIVU

mext_lemmas divuw, 1, 5, 0x3b, RiscvOpcode.Divuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divuw, zisk_ops.ZiskOp.DivuW, 188#u8, true, zisk_ops.OpType.ArithA32, OP_DIVU_W

mext_lemmas remu, 1, 7, 0x33, RiscvOpcode.Remu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remu, zisk_ops.ZiskOp.Remu, 185#u8, false, zisk_ops.OpType.ArithAm32, OP_REMU

mext_lemmas remuw, 1, 7, 0x3b, RiscvOpcode.Remuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remuw, zisk_ops.ZiskOp.RemuW, 189#u8, true, zisk_ops.OpType.ArithA32, OP_REMU_W

/-! ## Current `ProgramDecode` constructors. -/

local macro "mext_program_decode_ab" nm:ident "," f3:term "," opw:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName :=
    Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val
      (ZiskFv.Compliance.busSub trace i (ZiskFv.Compliance.Pilot.execRowOf trace i)).e2
    bounds : ZiskFv.Compliance.ByteBounds
      (ZiskFv.Compliance.busSub trace i (ZiskFv.Compliance.Pilot.execRowOf trace i)).e2
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k = ZiskFv.Completeness.Rv64imShapes.rawRType 1
              (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
              (regidx_to_fin c.rd).val $opw)
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      $programName trace i c := by
    let rd := (regidx_to_fin c.rd).val
    let rs1 := (regidx_to_fin c.r1).val
    let rs2 := (regidx_to_fin c.r2).val
    let ext := ($transpileName rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
        hstoreOffset, hstoreInd, _⟩ :=
      ($transpileName rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose_spec
    refine
      { h_idx := rawDecode.h_idx
        arith_mem := rawDecode.arith_mem
        bounds := rawDecode.bounds
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false hstoreInd
        h_prog := ?_ }
    intro j hline
    obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
    have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
    have hbk : trace.program j = romMessageOfRaw (addr k)
        (ZiskFv.Completeness.Rv64imShapes.rawRType 1 rs2 rs1 $f3 rd $opw) := by
      have hok' : aeneas_extract.extract_transpile_rv64im_raw
          (ZiskFv.Compliance.Decode.toU32
            (ZiskFv.Completeness.Rv64imShapes.rawRType 1
              (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
              (regidx_to_fin c.rd).val $opw)) = .ok ext := by
        simpa only [rd, rs1, rs2, ext] using hok
      have hnon :
          (ZiskFv.Compliance.Decode.toU32
              (ZiskFv.Completeness.Rv64imShapes.rawRType 1
                (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
                (regidx_to_fin c.rd).val $opw) &&& 127#u32) ≠ 103#u32 := by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawRType_opcode]
        all_goals decide
      have hp := hprimary.2
      rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
      simpa only [rd, rs1, rs2] using hp
    obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
        hstorepc', hstoreInd', hf⟩ :=
      $fieldsName rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
        (addr k) (trace.program j) hbk
    have hext : ext' = ext :=
      Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
    subst ext'
    refine ⟨ho, hjo1, hjo2, ?_, hf⟩
    rw [hso]
    simp only [rd, Transpiler.ind]
    apply Fin.ext
    change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
    exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)))
  return ⟨Lean.mkNullNode #[t1, t2]⟩

local macro "mext_program_decode_c" nm:ident "," f3:term "," opw:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName :=
    Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    bounds : ZiskFv.Compliance.ByteBounds
      (ZiskFv.Compliance.busSub trace i (ZiskFv.Compliance.Pilot.execRowOf trace i)).e2
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k = ZiskFv.Completeness.Rv64imShapes.rawRType 1
              (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
              (regidx_to_fin c.rd).val $opw)
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      $programName trace i c := by
    let rd := (regidx_to_fin c.rd).val
    let rs1 := (regidx_to_fin c.r1).val
    let rs2 := (regidx_to_fin c.r2).val
    let ext := ($transpileName rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
        hstoreOffset, hstoreInd, _⟩ :=
      ($transpileName rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose_spec
    refine
      { h_idx := rawDecode.h_idx
        bounds := rawDecode.bounds
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false hstoreInd
        h_prog := ?_ }
    intro j hline
    obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
    have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
    have hbk : trace.program j = romMessageOfRaw (addr k)
        (ZiskFv.Completeness.Rv64imShapes.rawRType 1 rs2 rs1 $f3 rd $opw) := by
      have hok' : aeneas_extract.extract_transpile_rv64im_raw
          (ZiskFv.Compliance.Decode.toU32
            (ZiskFv.Completeness.Rv64imShapes.rawRType 1
              (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
              (regidx_to_fin c.rd).val $opw)) = .ok ext := by
        simpa only [rd, rs1, rs2, ext] using hok
      have hnon :
          (ZiskFv.Compliance.Decode.toU32
              (ZiskFv.Completeness.Rv64imShapes.rawRType 1
                (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
                (regidx_to_fin c.rd).val $opw) &&& 127#u32) ≠ 103#u32 := by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawRType_opcode]
        all_goals decide
      have hp := hprimary.2
      rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
      simpa only [rd, rs1, rs2] using hp
    obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
        hstorepc', hstoreInd', hf⟩ :=
      $fieldsName rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
        (addr k) (trace.program j) hbk
    have hext : ext' = ext :=
      Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
    subst ext'
    refine ⟨ho, hjo1, hjo2, ?_, hf⟩
    rw [hso]
    simp only [rd, Transpiler.ind]
    apply Fin.ext
    change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
    exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)))
  return ⟨Lean.mkNullNode #[t1, t2]⟩

mext_program_decode_ab mul, 0, 0x33
mext_program_decode_ab mulh, 1, 0x33
mext_program_decode_ab mulhsu, 2, 0x33
mext_program_decode_ab div, 4, 0x33
mext_program_decode_ab rem, 6, 0x33
mext_program_decode_ab divw, 4, 0x3b
mext_program_decode_ab remw, 6, 0x3b

mext_program_decode_c mulhu, 3, 0x33
mext_program_decode_c divu, 5, 0x33
mext_program_decode_c divuw, 5, 0x3b
mext_program_decode_c remu, 7, 0x33
mext_program_decode_c remuw, 7, 0x3b

section AxiomAudit
#print axioms transpile_mul
#print axioms mul_decode_fields_of_binding
#print axioms ProgramDecode_mul_from_rawProgram
#print axioms ProgramDecode_mulh_from_rawProgram
#print axioms ProgramDecode_mulhsu_from_rawProgram
#print axioms ProgramDecode_mulhu_from_rawProgram
#print axioms ProgramDecode_div_from_rawProgram
#print axioms ProgramDecode_rem_from_rawProgram
#print axioms ProgramDecode_divw_from_rawProgram
#print axioms ProgramDecode_remw_from_rawProgram
#print axioms ProgramDecode_divu_from_rawProgram
#print axioms ProgramDecode_divuw_from_rawProgram
#print axioms ProgramDecode_remu_from_rawProgram
#print axioms ProgramDecode_remuw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
