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
  * `Decode_<op>_from_rawProgram` — rebuilds block-1's `Decode_<op>_of_program`
    from `rawProgram` + `ProgramBinding` + the `<op>`-shaped raw-word hypothesis
    + `h_idx`, with NO per-op ROM decode premise.

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
            ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
        refine transpile_register_of _ $rop $srop $zop $opU8 $m32 $ot ?_ rfl (by intro self input; rfl)
          rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
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
            ∧ ∃ ext, extract_transpile_rv64im_raw
                  (toU32 (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw)) = ok ext
                ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
                ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
                ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
        obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := $tName rd rs1 rs2 hrd hrs1 hrs2
        obtain ⟨ho, hjo1, hjo2, hf⟩ :=
          register_decode_fields_of_binding line msg _ $opU8 $opc ext (by simp [$opc:term]) hok hop hj1 hj2 hbind
        exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
    return ⟨Lean.mkNullNode #[t1, t2]⟩

/-! ## Group A — `arith_mem` + `bounds` over `c.bus.e2` (MUL / MULH / MULHSU). -/

local macro "mext_decode_ab" nm:ident "," f7:term "," f3:term "," opw:term ","
    opU8:term "," opc:ident : command => do
    let s := nm.getId.toString
    let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
    let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
    let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
    let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
    let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
    `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
          (i : Fin trace.numInstructions) (c : $claimT trace i)
          (h_idx : i.val + 1 < trace.mainTable.table.length)
          (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
          (bounds : ZiskFv.Compliance.ByteBounds c.bus.e2)
          (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
          (rawProgram : Fin n → BitVec 32)
          (hbind : ProgramBinding trace rawProgram)
          (hLine : ∀ j : Fin n,
              (trace.program j).line
                = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
              rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :
          $decodeT trace i c := by
        set ext := ($tName rd rs1 rs2 hrd hrs1 hrs2).choose with hext
        obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
          ($tName rd rs1 rs2 hrd hrs1 hrs2).choose_spec
        refine $decodeOf trace i c h_idx arith_mem bounds
          (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
        intro j hline
        have hbk : trace.program j
            = romMessageOfRaw (trace.program j).line
                (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :=
          (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
        obtain ⟨ho, hj1', hj2', hflags⟩ :=
          register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
            (by simp [$opc:term]) hok hop hj1 hj2 hbk
        exact ⟨ho, hj1', hj2', hflags⟩)

/-! ## Group B — `pins` + `arith_mem` + `bounds` (DIV / REM / DIVW / REMW). -/

local macro "mext_decode_pab" nm:ident "," f7:term "," f3:term "," opw:term ","
    opU8:term "," opc:ident : command => do
    let s := nm.getId.toString
    let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
    let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
    let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
    let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
    let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
    `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
          (i : Fin trace.numInstructions) (c : $claimT trace i)
          (h_idx : i.val + 1 < trace.mainTable.table.length)
          (pins : ZiskFv.Compliance.MainRowPins
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val 1 $opc)
          (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val c.bus.e2)
          (bounds : ZiskFv.Compliance.ByteBounds c.bus.e2)
          (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
          (rawProgram : Fin n → BitVec 32)
          (hbind : ProgramBinding trace rawProgram)
          (hLine : ∀ j : Fin n,
              (trace.program j).line
                = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
              rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :
          $decodeT trace i c := by
        set ext := ($tName rd rs1 rs2 hrd hrs1 hrs2).choose with hext
        obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
          ($tName rd rs1 rs2 hrd hrs1 hrs2).choose_spec
        refine $decodeOf trace i c h_idx pins arith_mem bounds
          (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
        intro j hline
        have hbk : trace.program j
            = romMessageOfRaw (trace.program j).line
                (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :=
          (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
        obtain ⟨ho, hj1', hj2', hflags⟩ :=
          register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
            (by simp [$opc:term]) hok hop hj1 hj2 hbk
        exact ⟨ho, hj1', hj2', hflags⟩)

/-! ## Group C — `bounds` over `(busSub …).e2` (MULHU / DIVU / DIVUW / REMU / REMUW). -/

local macro "mext_decode_b" nm:ident "," f7:term "," f3:term "," opw:term ","
    opU8:term "," opc:ident : command => do
    let s := nm.getId.toString
    let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
    let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
    let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
    let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
    let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
    `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
          (i : Fin trace.numInstructions) (c : $claimT trace i)
          (h_idx : i.val + 1 < trace.mainTable.table.length)
          (bounds : ZiskFv.Compliance.ByteBounds
            (ZiskFv.Compliance.busSub trace i (ZiskFv.Compliance.Pilot.execRowOf trace i)).e2)
          (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
          (rawProgram : Fin n → BitVec 32)
          (hbind : ProgramBinding trace rawProgram)
          (hLine : ∀ j : Fin n,
              (trace.program j).line
                = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
              rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :
          $decodeT trace i c := by
        set ext := ($tName rd rs1 rs2 hrd hrs1 hrs2).choose with hext
        obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
          ($tName rd rs1 rs2 hrd hrs1 hrs2).choose_spec
        refine $decodeOf trace i c h_idx bounds
          (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
        intro j hline
        have hbk : trace.program j
            = romMessageOfRaw (trace.program j).line
                (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :=
          (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
        obtain ⟨ho, hj1', hj2', hflags⟩ :=
          register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
            (by simp [$opc:term]) hok hop hj1 hj2 hbk
        exact ⟨ho, hj1', hj2', hflags⟩)

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

/-! ## Group A: MUL / MULH / MULHSU (`arith_mem` + `bounds` over `c.bus.e2`). -/

mext_lemmas mul, 1, 0, 0x33, RiscvOpcode.Mul, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mul, zisk_ops.ZiskOp.Mul, 180#u8, false, zisk_ops.OpType.ArithAm32, OP_MUL
mext_decode_ab mul, 1, 0, 0x33, 180#u8, OP_MUL

mext_lemmas mulh, 1, 1, 0x33, RiscvOpcode.Mulh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulh, zisk_ops.ZiskOp.Mulh, 181#u8, false, zisk_ops.OpType.ArithAm32, OP_MULH
mext_decode_ab mulh, 1, 1, 0x33, 181#u8, OP_MULH

mext_lemmas mulhsu, 1, 2, 0x33, RiscvOpcode.Mulhsu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhsu, zisk_ops.ZiskOp.Mulsuh, 179#u8, false, zisk_ops.OpType.ArithAm32, OP_MULSUH
mext_decode_ab mulhsu, 1, 2, 0x33, 179#u8, OP_MULSUH

/-! ## Group B: DIV / REM / DIVW / REMW (`pins` + `arith_mem` + `bounds`). -/

mext_lemmas div, 1, 4, 0x33, RiscvOpcode.Div, riscv2zisk_single_row.Rv64imSingleRowOpcode.Div, zisk_ops.ZiskOp.Div, 186#u8, false, zisk_ops.OpType.ArithAm32, OP_DIV
mext_decode_pab div, 1, 4, 0x33, 186#u8, OP_DIV

mext_lemmas rem, 1, 6, 0x33, RiscvOpcode.Rem, riscv2zisk_single_row.Rv64imSingleRowOpcode.Rem, zisk_ops.ZiskOp.Rem, 187#u8, false, zisk_ops.OpType.ArithAm32, OP_REM
mext_decode_pab rem, 1, 6, 0x33, 187#u8, OP_REM

mext_lemmas divw, 1, 4, 0x3b, RiscvOpcode.Divw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divw, zisk_ops.ZiskOp.DivW, 190#u8, true, zisk_ops.OpType.ArithA32, OP_DIV_W
mext_decode_pab divw, 1, 4, 0x3b, 190#u8, OP_DIV_W

mext_lemmas remw, 1, 6, 0x3b, RiscvOpcode.Remw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remw, zisk_ops.ZiskOp.RemW, 191#u8, true, zisk_ops.OpType.ArithA32, OP_REM_W
mext_decode_pab remw, 1, 6, 0x3b, 191#u8, OP_REM_W

/-! ## Group C: MULHU / DIVU / DIVUW / REMU / REMUW (`bounds` over `(busSub …).e2`). -/

mext_lemmas mulhu, 1, 3, 0x33, RiscvOpcode.Mulhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulhu, zisk_ops.ZiskOp.Muluh, 177#u8, false, zisk_ops.OpType.ArithAm32, OP_MULUH
mext_decode_b mulhu, 1, 3, 0x33, 177#u8, OP_MULUH

mext_lemmas divu, 1, 5, 0x33, RiscvOpcode.Divu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divu, zisk_ops.ZiskOp.Divu, 184#u8, false, zisk_ops.OpType.ArithAm32, OP_DIVU
mext_decode_b divu, 1, 5, 0x33, 184#u8, OP_DIVU

mext_lemmas divuw, 1, 5, 0x3b, RiscvOpcode.Divuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Divuw, zisk_ops.ZiskOp.DivuW, 188#u8, true, zisk_ops.OpType.ArithA32, OP_DIVU_W
mext_decode_b divuw, 1, 5, 0x3b, 188#u8, OP_DIVU_W

mext_lemmas remu, 1, 7, 0x33, RiscvOpcode.Remu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remu, zisk_ops.ZiskOp.Remu, 185#u8, false, zisk_ops.OpType.ArithAm32, OP_REMU
mext_decode_b remu, 1, 7, 0x33, 185#u8, OP_REMU

mext_lemmas remuw, 1, 7, 0x3b, RiscvOpcode.Remuw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Remuw, zisk_ops.ZiskOp.RemuW, 189#u8, true, zisk_ops.OpType.ArithA32, OP_REMU_W
mext_decode_b remuw, 1, 7, 0x3b, 189#u8, OP_REMU_W

section AxiomAudit
#print axioms transpile_mul
#print axioms mul_decode_fields_of_binding
#print axioms Decode_mul_from_rawProgram
#print axioms Decode_div_from_rawProgram
#print axioms Decode_mulhu_from_rawProgram
#print axioms Decode_remuw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
