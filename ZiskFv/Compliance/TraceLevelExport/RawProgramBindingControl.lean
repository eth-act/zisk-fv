import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister

/-!
# Raw-program decode bridge — branch + control family (issue #159, BLOCK 3)

Mirrors the register / immediate / load-store bridges
(`RawProgramBinding{Register,Immediate,LoadStore}`) for the six RV64I branches
(BEQ/BNE/BLT/BGE/BLTU/BGEU) and the five control ops (LUI/AUIPC/JAL/JALR/FENCE),
with the raw word's register / immediate fields SYMBOLIC.

  * BRANCHES (B-type word `rawBType`, `decode_b`) lower through
    `create_branch_op_typed`.  `neg` flips the two `j` offsets: the CONSTANT
    fall-through slot is `jmp_offset2` for the `neg = false` ops (BEQ/BLT/BLTU)
    and `jmp_offset1` for the `neg = true` ops (BNE/BGE/BGEU).  The imm-target
    slot is OUT of decode scope and not a decode pin (skipped).
  * LUI / AUIPC (U-type word `rawUType`, `decode_u`) lower through `lui` /
    `auipc`.  AUIPC's `store_pc = true` needs `rd ≠ 0` (the nop-guard disproof,
    matching `auipc_static_pins_full`); the decode-relevant constant slot is
    `jmp_offset1 = 4` (jmp_offset2 carries the imm target, skipped).
  * JAL (J-type word `rawJType`, `decode_j`) lowers through `jal`; `store_pc =
    true` needs `rd ≠ 0`.  The constant slot is `jmp_offset2 = 4` (jmp_offset1
    carries the imm target, skipped).
  * JALR (I-type word `rawIType … 0x67`, `decode_i … false`) lowers through
    `jalr`, whose `i.imm % 4` TWO-ROW split makes `jmp_offset` a per-row
    disjunction; `Decode_jalr_of_program` pins NO jmp_offset, so the bridge
    threads only `op` / `flags` plus the genuine operand-side JALR witnesses
    (a/c masks, flag, offset bridge/even/no-wrap) as caller hypotheses.
  * FENCE (supported-FENCE word `rawSupportedFence`, `decode_fence`) lowers
    through `nop`; both jump slots are the constant fall-through (`= 4`).  The
    claim-side `fm = 0` / `rs = x0` / `rd = x0` are threaded as caller
    hypotheses (the FENCE defect scope, matching `Decode_fence_of_program`).

For each op `<op>` the triple is:
  * `transpile_<op>` — the REAL Aeneas pipeline `extract_transpile_rv64im_raw`
    reduces to the op's decode-field pins.
  * `<op>_decode_fields_of_binding` — the committed message's decode fields,
    from its raw word + the op-agnostic `romMessageOfRaw` binding.
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
  (defCtx decode_b_bounds create_branch_op_typed_ok decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem hcast4' : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-! ## Generic branch-family transpile reduction (B-type word, `decode_b`).

`create_branch_op_typed` writes only `rs1` / `rs2` (no `rd`); the constant
fall-through jump slot is `jmp_offset2` for `neg = false`, `jmp_offset1` for
`neg = true`. -/

theorem transpile_branch_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (op : zisk_ops.ZiskOp) (neg : Bool) (opc : Std.U8)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_b raw rop)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (self : riscv2zisk_context.Riscv2ZiskContext)
        (input : riscv2zisk_single_row.Rv64imLoweringInput),
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input self input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
                  { self with extract_marker := () } input op neg 4#u64
                ok { s with extract_marker := () }))
    (hcode : zisk_ops.ZiskOp.code op = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 op = ok false)
    (hot : zisk_ops.ZiskOp.op_type op = ok zisk_ops.OpType.Binary) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ (neg = false → ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
      ∧ (neg = true  → ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64) := by
  obtain ⟨decoded, hdecoded, hopd, hrs1b, hrs2b⟩ := decode_b_bounds raw rop
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  obtain ⟨ctx0, hctx0⟩ := create_branch_op_typed_ok { defCtx with extract_marker := () } input op neg 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.branch_static_pins_of { defCtx with extract_marker := () }
      input op neg 4#u64 ctx0 opc hcode hm32 hot hctx0
  obtain ⟨zib', hzib', hjf, hjt⟩ :=
    ZiskFv.Compliance.Extraction.create_branch_op_typed_dynamic_pins
      { defCtx with extract_marker := () } input op neg 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hjf hjt
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = opc; rw [hrop]; exact hop2
  · show row.is_external_op = true; rw [hrext]; exact hext2
  · show row.m32 = false; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · intro hf; show row.jmp_offset2 = _; rw [hrj2]; exact hjf hf
  · intro ht; show row.jmp_offset1 = _; rw [hrj1]; exact hjt ht

/-! ## Branch decode-field bridges (one constant jump slot, op, flags). -/

/-- `neg = false` branch (BEQ/BLT/BLTU): the committed message's `op` /
`jmp_offset2` / `flags`, from its raw word binding. -/
theorem branch_decode_fields_false
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : (opc.val : FGL) = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset2 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by rw [hbind, romMessageOfRaw, hok]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmsg]; show (ext.row.op.val : FGL) = opF; rw [hop, ← hopF]
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4; rw [hj2]; norm_num [hcast4']
  · rw [hmsg]; rfl

/-- `neg = true` branch (BNE/BGE/BGEU): the committed message's `op` /
`jmp_offset1` / `flags`, from its raw word binding. -/
theorem branch_decode_fields_true
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : (opc.val : FGL) = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by rw [hbind, romMessageOfRaw, hok]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmsg]; show (ext.row.op.val : FGL) = opF; rw [hop, ← hopF]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4; rw [hj1]; norm_num [hcast4']
  · rw [hmsg]; rfl

/-! ## Per-op macros for the branch family. -/

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

/-- macro (neg = false branch: BEQ/BLT/BLTU; constant slot `jmp_offset2`). -/
local macro "branch_false_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    op:term "," opU8:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let t1 ← `(theorem $tName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
      have hdec : aeneas_extract.rv64im_decode.decode_32_core
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3))
          = aeneas_extract.rv64im_decode.decode_b
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) $rop := by
        simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
          ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
          ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
          ZiskFv.Compliance.Decode.rawBType_opcode imm rs2 rs1 $f3,
          ZiskFv.Compliance.Decode.rawBType_funct3 imm rs2 rs1 $f3 (by norm_num)]
        all_goals rfl
      obtain ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hjf, _⟩ :=
        transpile_branch_of _ $rop $srop $op false $opU8 hdec rfl (by intro self input; rfl) rfl rfl rfl
      exact ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hjf rfl⟩)
  let t2 ← `(theorem $dfName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) :
        msg.op = $opc ∧ msg.jmp_offset2 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj2⟩ := $tName rs1 rs2 imm hrs1 hrs2
      obtain ⟨ho, hjo2, hf⟩ :=
        branch_decode_fields_false line msg _ $opU8 $opc ext (by simp [$opc:term]) hok hop hj2 hbind
      exact ⟨ho, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3) :
        $decodeT trace i c := by
      set ext := ($tName rs1 rs2 imm hrs1 hrs2).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj2⟩ :=
        ($tName rs1 rs2 imm hrs1 hrs2).choose_spec
      refine $decodeOf trace i c h_idx (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj2', hflags⟩ :=
        branch_decode_fields_false (trace.program j).line (trace.program j) _ $opU8 $opc ext
          (by simp [$opc:term]) hok hop hj2 hbk
      exact ⟨ho, hj2', hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

/-- macro (neg = true branch: BNE/BGE/BGEU; constant slot `jmp_offset1`). -/
local macro "branch_true_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    op:term "," opU8:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let t1 ← `(theorem $tName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64 := by
      have hdec : aeneas_extract.rv64im_decode.decode_32_core
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3))
          = aeneas_extract.rv64im_decode.decode_b
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) $rop := by
        simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
          ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
          ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
          ZiskFv.Compliance.Decode.rawBType_opcode imm rs2 rs1 $f3,
          ZiskFv.Compliance.Decode.rawBType_funct3 imm rs2 rs1 $f3 (by norm_num)]
        all_goals rfl
      obtain ⟨ext, hok, hop, hieo, hm32, hsp, hstp, _, hjt⟩ :=
        transpile_branch_of _ $rop $srop $op true $opU8 hdec rfl (by intro self input; rfl) rfl rfl rfl
      exact ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hjt rfl⟩)
  let t2 ← `(theorem $dfName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1⟩ := $tName rs1 rs2 imm hrs1 hrs2
      obtain ⟨ho, hjo1, hf⟩ :=
        branch_decode_fields_true line msg _ $opU8 $opc ext (by simp [$opc:term]) hok hop hj1 hbind
      exact ⟨ho, hjo1, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3) :
        $decodeT trace i c := by
      set ext := ($tName rs1 rs2 imm hrs1 hrs2).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1⟩ :=
        ($tName rs1 rs2 imm hrs1 hrs2).choose_spec
      refine $decodeOf trace i c h_idx (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hflags⟩ :=
        branch_decode_fields_true (trace.program j).line (trace.program j) _ $opU8 $opc ext
          (by simp [$opc:term]) hok hop hj1 hbk
      exact ⟨ho, hj1', hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

branch_false_op beq,  0, RiscvOpcode.Beq,  riscv2zisk_single_row.Rv64imSingleRowOpcode.Beq,  zisk_ops.ZiskOp.Eq,  9#u8, OP_EQ
branch_true_op  bne,  1, RiscvOpcode.Bne,  riscv2zisk_single_row.Rv64imSingleRowOpcode.Bne,  zisk_ops.ZiskOp.Eq,  9#u8, OP_EQ
branch_false_op blt,  4, RiscvOpcode.Blt,  riscv2zisk_single_row.Rv64imSingleRowOpcode.Blt,  zisk_ops.ZiskOp.Lt,  7#u8, OP_LT
branch_true_op  bge,  5, RiscvOpcode.Bge,  riscv2zisk_single_row.Rv64imSingleRowOpcode.Bge,  zisk_ops.ZiskOp.Lt,  7#u8, OP_LT
branch_false_op bltu, 6, RiscvOpcode.Bltu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bltu, zisk_ops.ZiskOp.Ltu, 6#u8, OP_LTU
branch_true_op  bgeu, 7, RiscvOpcode.Bgeu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Bgeu, zisk_ops.ZiskOp.Ltu, 6#u8, OP_LTU

section AxiomAudit
#print axioms transpile_beq
#print axioms beq_decode_fields_of_binding
#print axioms Decode_beq_from_rawProgram
#print axioms Decode_bne_from_rawProgram
#print axioms Decode_bgeu_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
