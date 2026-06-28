import ZiskFv.Compliance.TraceLevelExport.RawProgramBinding
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Totality

/-!
# Raw-program decode bridge — register-register ALU / M family (issue #159, BLOCK 3)

Generalizes the ADD pilot (`RawProgramBinding`) to the register-register family,
with the raw word's `rd`/`rs1`/`rs2` SYMBOLIC (the decode fields op / flags /
jmp_offset are register-INDEPENDENT).  For each op `<op>`:

  * `transpile_<op>` — the REAL Aeneas pipeline `extract_transpile_rv64im_raw` on
    the symbolic R-type word `rawRType <funct7> rs2 rs1 <funct3> rd <opcode>`
    reduces to the op's decode-field pins.  Decode classification reuses #164's
    `rawRType_{opcode,funct3,funct7}` masks (register-independent); lowering
    TOTALITY reuses `Extraction.create_register_op_typed_ok` (#159 block-3
    `Totality.lean`); the field pins reuse #111 `register_static_pins_of` +
    block-2 `create_register_op_typed_dynamic_pins`.
  * `<op>_decode_fields_of_binding` — the committed message's decode fields,
    derived from its raw word + the op-agnostic `romMessageOfRaw` binding.
  * `Decode_<op>_from_rawProgram` — rebuilds block-1's `Decode_<op>` from
    `rawProgram` + `ProgramBinding` + the `<op>`-shaped raw-word hypothesis +
    `h_idx`, with NO per-op decode premise.

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

/-! ## Generic register-family transpile reduction. -/

/-- The REAL transpile pipeline on a register-op raw word `raw` reduces to the
    op's decode-field pins, given: the decode classifies to `decode_r raw rop`;
    `rop` lowers to the single-row opcode `srop`; the dispatcher routes `srop`
    unconditionally to `create_register_op_typed … zop 4`; and the static op-type
    facts (`code`/`is_m32`/`op_type`, external). -/
theorem transpile_register_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw = aeneas_extract.rv64im_decode.decode_r raw rop)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (self : riscv2zisk_context.Riscv2ZiskContext)
        (input : riscv2zisk_single_row.Rv64imLoweringInput),
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input self input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed
                  { self with extract_marker := () } input zop 4#u64
                ok { s with extract_marker := () }))
    (hcode : zisk_ops.ZiskOp.code zop = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 zop = ok m32v)
    (hot : zisk_ops.ZiskOp.op_type zop = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = true ∧ ext.row.m32 = m32v
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, hrs2b⟩ := decode_r_bounds raw rop
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  obtain ⟨ctx0, hctx0⟩ := create_register_op_typed_ok { defCtx with extract_marker := () } input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.register_static_pins_of { defCtx with extract_marker := () }
      input zop 4#u64 ctx0 opc m32v otv hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    ZiskFv.Compliance.Extraction.create_register_op_typed_dynamic_pins
      { defCtx with extract_marker := () } input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = opc; rw [hrop]; exact hop2
  · show row.is_external_op = true; rw [hrext]; exact hext2
  · show row.m32 = m32v; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2

/-! ## Generic decode-field bridge for register ops. -/

private theorem hcast4 : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-- The committed message's register-op decode fields, from its raw word binding. -/
theorem register_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : (opc.val : FGL) = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by rw [hbind, romMessageOfRaw, hok]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmsg]; show (ext.row.op.val : FGL) = opF; rw [hop, ← hopF]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4; rw [hj1]; norm_num [hcast4]
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4; rw [hj2]; norm_num [hcast4]
  · rw [hmsg]; rfl

/-! ## Per-op macro: emits `transpile_<op>` + `<op>_decode_fields_of_binding`
    + `Decode_<op>_from_rawProgram` for an unconditional register-register op. -/

local macro "reg_op" nm:ident "," f7:term "," f3:term "," opw:term ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
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
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
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
      refine $decodeOf trace i c h_idx (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hj2', hflags⟩ :=
        register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
          (by simp [$opc:term]) hok hop hj1 hj2 hbk
      exact ⟨ho, hj1', hj2', hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

reg_op sub, 32, 0, 0x33, RiscvOpcode.Sub, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sub, zisk_ops.ZiskOp.Sub, 11#u8, false, zisk_ops.OpType.Binary, OP_SUB
reg_op and, 0, 7, 0x33, RiscvOpcode.And, riscv2zisk_single_row.Rv64imSingleRowOpcode.And, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary, OP_AND
reg_op xor, 0, 4, 0x33, RiscvOpcode.Xor, riscv2zisk_single_row.Rv64imSingleRowOpcode.Xor, zisk_ops.ZiskOp.Xor, 16#u8, false, zisk_ops.OpType.Binary, OP_XOR
reg_op slt, 0, 2, 0x33, RiscvOpcode.Slt, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slt, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary, OP_LT
reg_op sltu, 0, 3, 0x33, RiscvOpcode.Sltu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary, OP_LTU
reg_op sll, 0, 1, 0x33, RiscvOpcode.Sll, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sll, zisk_ops.ZiskOp.Sll, 33#u8, false, zisk_ops.OpType.BinaryE, OP_SLL
reg_op srl, 0, 5, 0x33, RiscvOpcode.Srl, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srl, zisk_ops.ZiskOp.Srl, 34#u8, false, zisk_ops.OpType.BinaryE, OP_SRL
reg_op sra, 32, 5, 0x33, RiscvOpcode.Sra, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sra, zisk_ops.ZiskOp.Sra, 35#u8, false, zisk_ops.OpType.BinaryE, OP_SRA
reg_op addw, 0, 0, 0x3b, RiscvOpcode.Addw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Addw, zisk_ops.ZiskOp.AddW, 26#u8, true, zisk_ops.OpType.Binary, OP_ADD_W
reg_op subw, 32, 0, 0x3b, RiscvOpcode.Subw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Subw, zisk_ops.ZiskOp.SubW, 27#u8, true, zisk_ops.OpType.Binary, OP_SUB_W
reg_op sllw, 0, 1, 0x3b, RiscvOpcode.Sllw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sllw, zisk_ops.ZiskOp.SllW, 36#u8, true, zisk_ops.OpType.BinaryE, OP_SLL_W
reg_op srlw, 0, 5, 0x3b, RiscvOpcode.Srlw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srlw, zisk_ops.ZiskOp.SrlW, 37#u8, true, zisk_ops.OpType.BinaryE, OP_SRL_W
reg_op sraw, 32, 5, 0x3b, RiscvOpcode.Sraw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraw, zisk_ops.ZiskOp.SraW, 38#u8, true, zisk_ops.OpType.BinaryE, OP_SRA_W
-- MULW is the one M-ext op whose `Decode_<op>_of_program` takes `bits` directly
-- (no extra arith/bound/pin witness), so it fits the register template.
reg_op mulw, 1, 0, 0x3b, RiscvOpcode.Mulw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Mulw, zisk_ops.ZiskOp.MulW, 182#u8, true, zisk_ops.OpType.ArithAm32, OP_MUL_W

section AxiomAudit
#print axioms transpile_sub
#print axioms sub_decode_fields_of_binding
#print axioms Decode_sub_from_rawProgram
#print axioms Decode_sraw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
