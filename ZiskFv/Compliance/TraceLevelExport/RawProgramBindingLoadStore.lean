import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister

/-!
# Raw-program decode bridge — load / store family (issue #159, BLOCK 3)

Mirrors the register / immediate bridges (`RawProgramBinding{Register,Immediate}`)
for the seven loads (LB/LBU/LH/LHU/LW/LWU/LD) and four stores (SB/SH/SW/SD), with
the raw word's `rd`/`rs1`/`rs2`/`imm` SYMBOLIC.  Loads lower through `load_op_typed`
(I-type word, `decode_i … false`); stores through `store_op_typed` (S-type word,
`decode_s`).  Unlike the register/immediate ops the materialized row also carries
the access width `ind_width`, which the in-circuit ROM lookup (`Decode_<op>_of_program`)
reads, so each `transpile_<op>` additionally exposes `ext.row.ind_width = N#u64`
(via the block-2 `load_op_typed_jmp_width` / `store_op_typed_jmp_width` + the
`ind_width_setN` witnesses) and a `loadstore_decode_fields_of_binding` helper
serializes it to `msg.ind_width = (N : FGL)`.  For each op `<op>`:

  * `transpile_<op>` — the REAL Aeneas pipeline `extract_transpile_rv64im_raw` on
    the symbolic I-type / S-type word reduces to the op's decode-field pins.  Decode
    classification reuses #164's `rawIType_{opcode,funct3}` / `rawSType_{opcode,funct3}`
    masks; lowering TOTALITY reuses `Extraction.{load,store}_op_typed_ok` (#159
    block-3 `Totality.lean`); the field pins reuse #111 `{load,store}_static_pins_of`
    + block-2 `{load,store}_op_typed_jmp_width`.
  * `<op>_decode_fields_of_binding` — the committed message's decode fields (now
    incl. `ind_width`), derived from its raw word + the op-agnostic `romMessageOfRaw`
    binding.
  * `Decode_<op>_from_rawProgram` — rebuilds block-1's `Decode_<op>` from
    `rawProgram` + `ProgramBinding` + the `<op>`-shaped raw-word hypothesis +
    `h_idx`, with NO per-op decode premise.  The SIGNEXTEND loads (LB/LH/LW) carry
    the genuine `BinaryExtension` operand-bus witnesses (`v`/`r_binary`/`offset`/
    `env`/`h_static`/`h_match`) that `Decode_<op>_of_program` requires — these are
    real operand-side obligations OUTSIDE the ROM decode-from-raw scope, threaded
    as caller hypotheses (NOT invented).

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).
-/

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open Goldilocks
open ZiskFv.Compliance.Extraction
  (defCtx extBit decode_i_bounds decode_s_bounds load_op_typed_ok store_op_typed_ok
   load_op_typed_jmp_width store_op_typed_jmp_width decode_extract_ok from_inst_ok
   ind_width_set1 ind_width_set2 ind_width_set4 ind_width_set8)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Generic load / store decode-field bridge (adds `ind_width` to the register one). -/

/-- The committed message's load/store decode fields (incl. `ind_width`), from its
    raw word binding.  Extends `register_decode_fields_of_binding` with the access
    width that the load/store ROM lookup reads. -/
theorem loadstore_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (wU64 : Std.U64) (wF : FGL)
    (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : (opc.val : FGL) = opF)
    (hwF : (wU64.val : FGL) = wF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hiw : ext.row.ind_width = wU64)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4 ∧ msg.ind_width = wF
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg raw opc opF ext hopF hok hop hj1 hj2 hbind
  refine ⟨ho, hjo1, hjo2, ?_, hf⟩
  have hmsg : msg = serializeExtract line ext.row := by rw [hbind, romMessageOfRaw, hok]
  rw [hmsg]; show (ext.row.ind_width.val : FGL) = wF; rw [hiw]; exact hwF

/-! ## Generic load-family transpile reduction (I-type word, `decode_i … false`). -/

/-- The REAL transpile pipeline on a load raw word `raw` reduces to the op's
    decode-field pins (incl. `ind_width = wval`), given: the decode classifies to
    `decode_i raw rop false`; `rop` lowers to the single-row opcode `srop`; the
    dispatcher routes `srop` to `load_op_typed … zop W 4`; the `ind_width` builder
    accepts `W` (`hwtot`) with value `wval` (`hiw`); and the static op-type facts. -/
theorem transpile_load_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v extv : Bool) (otv : zisk_ops.OpType)
    (W wval : Std.U64)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_i raw rop false)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (hwtot : ∀ s : zisk_inst_builder.ZiskInstBuilder,
        ∃ z, zisk_inst_builder.ZiskInstBuilder.ind_width s W = ok z)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
        zisk_inst_builder.ZiskInstBuilder.ind_width s W = ok z → z.i.ind_width = wval)
    (harm : ∀ (self : riscv2zisk_context.Riscv2ZiskContext)
        (input : riscv2zisk_single_row.Rv64imLoweringInput),
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input self input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.load_op_typed
                  { self with extract_marker := () } input zop W 4#u64
                ok { s with extract_marker := () }))
    (hcode : zisk_ops.ZiskOp.code zop = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 zop = ok m32v)
    (hot : zisk_ops.ZiskOp.op_type zop = ok otv) (hextv : extBit otv = extv) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = extv ∧ ext.row.m32 = m32v
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.ind_width = wval
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ := decode_i_bounds raw rop false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  obtain ⟨ctx0, hctx0⟩ := load_op_typed_ok { defCtx with extract_marker := () } input zop W 4#u64
    hwtot (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.load_static_pins_of { defCtx with extract_marker := () }
      input zop W 4#u64 ctx0 opc m32v extv otv hcode hm32 hot hextv hctx0
  obtain ⟨zib', hzib', hiw', hj1, hj2⟩ :=
    load_op_typed_jmp_width { defCtx with extract_marker := () } input zop W 4#u64 ctx0 wval hiw hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hiw' hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, hriw⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = opc; rw [hrop]; exact hop2
  · show row.is_external_op = extv; rw [hrext]; exact hext2
  · show row.m32 = m32v; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · show row.ind_width = wval; rw [hriw]; exact hiw'
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

/-! ## Per-op macro (COPYB loads: LBU/LHU/LWU/LD): emits the triple.  These route
    to the `Internal`/`CopyB` `Decode_<op>_of_program` (no operand-bus witness). -/

local macro "load_copyb_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    width:term "," wF:term "," iwlem:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let t1 ← `(theorem $tName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) = ok ext
          ∧ ext.row.op = 1#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.ind_width = $width
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
      refine transpile_load_of _ $rop $srop zisk_ops.ZiskOp.CopyB 1#u8 false false
        zisk_ops.OpType.Internal $width $width ?_ rfl (fun _ => ⟨_, rfl⟩) $iwlem
        (by intro self input; rfl) rfl rfl rfl rfl
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 $f3 rd 0x03 (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 $f3 rd 0x03 (by norm_num) hrd (by norm_num)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4 ∧ msg.ind_width = $wF
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) = ok ext
              ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2⟩ := $tName rd rs1 imm hrd hrs1
      obtain ⟨ho, hjo1, hjo2, hiwF, hf⟩ :=
        loadstore_decode_fields_of_binding line msg _ 1#u8 $opc $width $wF ext (by simp [$opc:term])
          (by simp) hok hop hiw hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, hiwF, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03) :
        $decodeT trace i c := by
      set ext := ($tName rd rs1 imm hrd hrs1).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2⟩ :=
        ($tName rd rs1 imm hrd hrs1).choose_spec
      refine $decodeOf trace i c h_idx (romFlagBitsOfExtract ext.row) hieo hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hj2', hiwF, hflags⟩ :=
        loadstore_decode_fields_of_binding (trace.program j).line (trace.program j) _ 1#u8 $opc $width $wF ext
          (by simp [$opc:term]) (by simp) hok hop hiw hj1 hj2 hbk
      exact ⟨ho, hj1', hj2', hiwF, hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

load_copyb_op lbu, 4, RiscvOpcode.Lbu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lbu, 1#u64, (1 : FGL), ind_width_set1, OP_COPYB
load_copyb_op lhu, 5, RiscvOpcode.Lhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lhu, 2#u64, (2 : FGL), ind_width_set2, OP_COPYB
load_copyb_op lwu, 6, RiscvOpcode.Lwu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lwu, 4#u64, (4 : FGL), ind_width_set4, OP_COPYB
load_copyb_op ld,  3, RiscvOpcode.Ld,  riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld,  8#u64, (8 : FGL), ind_width_set8, OP_COPYB

/-! ## SIGNEXTEND loads (LB/LH/LW, issue #159 block 3).  These lower to the
    `BinaryE`/`SignExtend*` op (external, `is_external_op = true`), so their ROM
    decode (`Decode_<op>_of_program`) additionally consumes a `BinaryExtension`
    operand-bus witness (`v`/`r_binary`/`offset`/`env`/`h_static`/`h_match`) — a
    genuine operand-side soundness obligation OUTSIDE the ROM decode-from-raw scope,
    threaded as caller hypotheses.  `transpile_<op>` / the field bridge are
    op-agnostic; only the block-1 integration `Decode_<op>_from_rawProgram` carries
    them. -/

local macro "load_sext_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    zop:term "," opU8:term "," m32:term "," width:term "," wF:term "," iwlem:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let t1 ← `(theorem $tName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.ind_width = $width
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
      refine transpile_load_of _ $rop $srop $zop $opU8 $m32 true
        zisk_ops.OpType.BinaryE $width $width ?_ rfl (fun _ => ⟨_, rfl⟩) $iwlem
        (by intro self input; rfl) rfl rfl rfl rfl
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 $f3 rd 0x03 (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 $f3 rd 0x03 (by norm_num) hrd (by norm_num)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4 ∧ msg.ind_width = $wF
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2⟩ := $tName rd rs1 imm hrd hrs1
      obtain ⟨ho, hjo1, hjo2, hiwF, hf⟩ :=
        loadstore_decode_fields_of_binding line msg _ $opU8 $opc $width $wF ext (by simp [$opc:term])
          (by simp) hok hop hiw hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, hiwF, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
        (r_binary : ℕ) (offset : ℕ) (env : Environment FGL)
        (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
        (h_match : ZiskFv.Airs.OperationBus.matches_entry
          (ZiskFv.Airs.OperationBus.opBus_row_Main
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val)
          (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary))
        (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03) :
        $decodeT trace i c := by
      set ext := ($tName rd rs1 imm hrd hrs1).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2⟩ :=
        ($tName rd rs1 imm hrd hrs1).choose_spec
      refine $decodeOf trace i c h_idx v r_binary offset env h_static h_match
        (romFlagBitsOfExtract ext.row) hieo hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hj2', hiwF, hflags⟩ :=
        loadstore_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc $width $wF ext
          (by simp [$opc:term]) (by simp) hok hop hiw hj1 hj2 hbk
      exact ⟨ho, hj1', hj2', hiwF, hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

load_sext_op lb, 0, RiscvOpcode.Lb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lb, zisk_ops.ZiskOp.SignExtendB, 39#u8, false, 1#u64, (1 : FGL), ind_width_set1, OP_SIGNEXTEND_B
load_sext_op lh, 1, RiscvOpcode.Lh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lh, zisk_ops.ZiskOp.SignExtendH, 40#u8, false, 2#u64, (2 : FGL), ind_width_set2, OP_SIGNEXTEND_H
load_sext_op lw, 2, RiscvOpcode.Lw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lw, zisk_ops.ZiskOp.SignExtendW, 41#u8, true, 4#u64, (4 : FGL), ind_width_set4, OP_SIGNEXTEND_W

section AxiomAudit
#print axioms transpile_lbu
#print axioms lbu_decode_fields_of_binding
#print axioms Decode_lbu_from_rawProgram
#print axioms transpile_ld
#print axioms Decode_ld_from_rawProgram
#print axioms transpile_lb
#print axioms Decode_lb_from_rawProgram
#print axioms transpile_lw
#print axioms Decode_lw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
