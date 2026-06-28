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
  (defCtx decode_b_bounds decode_u_bounds decode_j_bounds decode_i_bounds
   create_branch_op_typed_ok lui_ok auipc_ok jal_ok jalr_ok nop_ok
   decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private theorem hcast4' : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-! ## Decoder `rd`-field recovery (`[7,11]` bits) and the symbolic `rd ≠ 0`
derivations, for the AUIPC / JAL / JALR `store_pc = true` nop-guard.  All
kernel-sound (`ofNat32_shift_mask_eq`, no native_decide). -/

private theorem and3968_shr7 (x : BitVec 32) : (x &&& 3968#32) >>> 7 = (x >>> 7) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    show (3968:Nat) = 31 <<< 7 by decide, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · rw [decide_eq_true (show 7 + i < 32 by omega), decide_eq_true (show i < 32 by omega)]
    simp [show (7 : Nat) ≤ 7 + i by omega, show 7 + i - 7 = i by omega]
  · rw [ZiskFv.Compliance.Decode.tbf (show (31:Nat) < 2 ^ 5 by norm_num) (show 5 ≤ 7 + i - 7 by omega),
      ZiskFv.Compliance.Decode.tbf (show (31:Nat) < 2 ^ 5 by norm_num) (show 5 ≤ i by omega)]
    simp

private theorem rawUType_rd (imm rd opcode : Nat) (hrd : rd < 32) (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawUType imm rd opcode) &&& 3968#32) >>> 7
      = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawUType, ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  have hmask : (4294963200).testBit (7 + i) = false := by interval_cases i <;> decide
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and]
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e7, hop', hmask, show 7 + i - 7 = i from by omega]

private theorem rawJType_rd (imm rd : Nat) (hrd : rd < 32) :
    ((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawJType, ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and]
  have e7 : (7 ≤ 7 + i) := by omega
  have h12 : ¬ (12 ≤ 7 + i) := by omega
  have h20 : ¬ (20 ≤ 7 + i) := by omega
  have h21 : ¬ (21 ≤ 7 + i) := by omega
  have h31 : ¬ (31 ≤ 7 + i) := by omega
  have h6f : (111).testBit (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show 111 < 2 ^ 7 by norm_num) (by omega)
  simp [e7, h12, h20, h21, h31, h6f, show 7 + i - 7 = i from by omega]

private theorem rawIType_rd (imm rs1 funct3 rd opcode : Nat) (hrd : rd < 32) (hf3 : funct3 < 8)
    (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 funct3 rd opcode) &&& 3968#32) >>> 7
      = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawIType, ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 7 + i) := by omega
  have e15 : ¬ (15 ≤ 7 + i) := by omega
  have e12 : ¬ (12 ≤ 7 + i) := by omega
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hop', show 7 + i - 7 = i from by omega]

private theorem rd_ne_zero_u32 (drd : Std.U32) (rd : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (hbv : drd.bv = BitVec.ofNat 32 rd) : drd ≠ 0#u32 := by
  intro hc
  rw [hc] at hbv
  have hz : (0 : Nat) = rd % 2 ^ 32 := by
    have := congrArg BitVec.toNat hbv
    simpa [BitVec.toNat_ofNat] using this
  omega

private theorem rd_ne_zero_i64 (drd : Std.U32) (rd : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (hbv : drd.bv = BitVec.ofNat 32 rd) : (UScalar.hcast IScalarTy.I64 drd : Std.I64) ≠ 0#i64 := by
  intro hc
  have hval : (UScalar.hcast IScalarTy.I64 drd : Std.I64).val = drd.val :=
    ZiskFv.Compliance.Extraction.hcast_u32_i64_val drd
  rw [hc] at hval
  have hz : drd.bv.toNat = 0 := by
    have h1 : ((drd.val : Int)) = 0 := by rw [← hval]; decide
    have h2 : drd.val = 0 := by exact_mod_cast h1
    exact h2
  rw [hbv, BitVec.toNat_ofNat] at hz
  omega

/-- op + flags only (no jump pin), for JALR. -/
theorem op_flags_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : (opc.val : FGL) = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by rw [hbind, romMessageOfRaw, hok]
  refine ⟨?_, ?_⟩
  · rw [hmsg]; show (ext.row.op.val : FGL) = opF; rw [hop, ← hopF]
  · rw [hmsg]; rfl

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

/-! ## LUI (U-type word, `decode_u` → `lui` → `OP_COPYB`).  Both jump slots are
the constant fall-through; the operand-side `b_0`/`b_1` immediate bridges are
threaded as caller hypotheses (matching `Decode_lui_of_program`). -/

theorem transpile_lui (rd imm : Nat) (hrd : rd < 32) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) = ok ext
      ∧ ext.row.op = 1#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37))
      = aeneas_extract.rv64im_decode.decode_u
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) RiscvOpcode.Lui := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawUType_opcode imm rd 0x37 (by norm_num)]
    all_goals rfl
  obtain ⟨decoded, hdecoded, hopd, hrdb, _⟩ :=
    decode_u_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) RiscvOpcode.Lui
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  obtain ⟨ctx0, hctx0⟩ := lui_ok { defCtx with extract_marker := () } input 4#u64 (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.lui_static_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    ZiskFv.Compliance.Extraction.lui_dynamic_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have harm : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
        riscv2zisk_single_row.Rv64imSingleRowOpcode.Lui false
      = (do let s ← riscv2zisk_context.Riscv2ZiskContext.lui { defCtx with extract_marker := () } input 4#u64
            ok { s with extract_marker := () }) := rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
      riscv2zisk_single_row.Rv64imSingleRowOpcode.Lui false = ok { ctx0 with extract_marker := () } := by
    rw [harm, hctx0]; rfl
  have hlowop : aeneas_extract.lowering_opcode RiscvOpcode.Lui
      = ok (some riscv2zisk_single_row.Rv64imSingleRowOpcode.Lui) := rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = 1#u8; rw [hrop]; exact hop2
  · show row.is_external_op = false; rw [hrext]; exact hext2
  · show row.m32 = false; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2

theorem lui_decode_fields_of_binding (rd imm : Nat) (hrd : rd < 32)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) :
    msg.op = OP_COPYB ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := transpile_lui rd imm hrd
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 1#u8 OP_COPYB ext (by simp [OP_COPYB]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_lui_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_lui trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_imm_lo_nat : ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (c.imm ++ (0 : BitVec 12)).toNat)
    (h_imm_hi_nat : ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat / 4294967296)
    (rd imm : Nat) (hrd : rd < 32)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37) :
    ZiskFv.Compliance.Decode_lui trace i c := by
  set ext := (transpile_lui rd imm hrd).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := (transpile_lui rd imm hrd).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_lui_of_program trace i c h_idx h_imm_lo_nat h_imm_hi_nat
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 1#u8 OP_COPYB ext
      (by simp [OP_COPYB]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

/-! ## AUIPC (U-type word, `decode_u` → `auipc` → `OP_FLAG`, `store_pc = true`).
The constant slot is `jmp_offset1 = 4` (`= 4#i64`, defeq `hcast 4#u64`); the
`store_pc = true` needs `rd ≠ 0`.  jmp_offset2 is the imm target (skipped). -/

theorem transpile_auipc (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) = ok ext
      ∧ ext.row.op = 0#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64 := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17))
      = aeneas_extract.rv64im_decode.decode_u
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) RiscvOpcode.Auipc := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawUType_opcode imm rd 0x17 (by norm_num)]
    all_goals rfl
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrdbv⟩ :=
    decode_u_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) RiscvOpcode.Auipc
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hbveq : decoded.rd.bv = BitVec.ofNat 32 rd := by
    rw [hrdbv]
    show ((ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd
    exact rawUType_rd imm rd 0x17 hrd (by norm_num)
  have hrd_ne : (UScalar.hcast IScalarTy.I64 input.rd : Std.I64) ≠ 0#i64 := by
    rw [hinput]; exact rd_ne_zero_i64 decoded.rd rd hrd hrd0 hbveq
  obtain ⟨ctx0, hctx0⟩ := auipc_ok { defCtx with extract_marker := () } input (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.auipc_static_pins_full { defCtx with extract_marker := () } input ctx0 hrd_ne hctx0
  obtain ⟨zib', hzib', hj1⟩ :=
    ZiskFv.Compliance.Extraction.auipc_dynamic_pins { defCtx with extract_marker := () } input ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have harm : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
        riscv2zisk_single_row.Rv64imSingleRowOpcode.Auipc false
      = (do let s ← riscv2zisk_context.Riscv2ZiskContext.auipc { defCtx with extract_marker := () } input
            ok { s with extract_marker := () }) := rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
      riscv2zisk_single_row.Rv64imSingleRowOpcode.Auipc false = ok { ctx0 with extract_marker := () } := by
    rw [harm, hctx0]; rfl
  have hlowop : aeneas_extract.lowering_opcode RiscvOpcode.Auipc
      = ok (some riscv2zisk_single_row.Rv64imSingleRowOpcode.Auipc) := rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = 0#u8; rw [hrop]; exact hop2
  · show row.is_external_op = false; rw [hrext]; exact hext2
  · show row.m32 = false; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = true; rw [hrstp]; exact hstp2
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1

theorem auipc_decode_fields_of_binding (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) :
    msg.op = OP_FLAG ∧ msg.jmp_offset1 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1⟩ := transpile_auipc rd imm hrd hrd0
  obtain ⟨ho, hjo1, hf⟩ :=
    branch_decode_fields_true line msg _ 0#u8 OP_FLAG ext (by simp [OP_FLAG]) hok hop hj1 hbind
  exact ⟨ho, hjo1, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_auipc_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_auipc trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17) :
    ZiskFv.Compliance.Decode_auipc trace i c := by
  set ext := (transpile_auipc rd imm hrd hrd0).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1⟩ := (transpile_auipc rd imm hrd hrd0).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_auipc_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hflags⟩ :=
    branch_decode_fields_true (trace.program j).line (trace.program j) _ 0#u8 OP_FLAG ext
      (by simp [OP_FLAG]) hok hop hj1 hbk
  exact ⟨ho, hj1', hflags⟩

/-! ## JAL (J-type word, `decode_j` → `jal` → `OP_FLAG`, `store_pc = true`).
Constant slot `jmp_offset2 = 4`; `store_pc = true` needs `rd ≠ 0`.  jmp_offset1
is the imm target (skipped). -/

theorem transpile_jal (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) = ok ext
      ∧ ext.row.op = 0#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd))
      = aeneas_extract.rv64im_decode.decode_j
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) RiscvOpcode.Jal := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawJType_opcode imm rd]
    all_goals rfl
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrdbv⟩ :=
    decode_j_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) RiscvOpcode.Jal
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hbveq : decoded.rd.bv = BitVec.ofNat 32 rd := by
    rw [hrdbv]
    show ((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd
    exact rawJType_rd imm rd hrd
  have hrd_ne : (UScalar.hcast IScalarTy.I64 input.rd : Std.I64) ≠ 0#i64 := by
    rw [hinput]; exact rd_ne_zero_i64 decoded.rd rd hrd hrd0 hbveq
  obtain ⟨ctx0, hctx0⟩ := jal_ok { defCtx with extract_marker := () } input 4#u64 (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2cond⟩ :=
    ZiskFv.Compliance.Extraction.jal_static_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  obtain ⟨zib', hzib', _, hj2⟩ :=
    ZiskFv.Compliance.Extraction.jal_dynamic_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have harm : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
        riscv2zisk_single_row.Rv64imSingleRowOpcode.Jal false
      = (do let s ← riscv2zisk_context.Riscv2ZiskContext.jal { defCtx with extract_marker := () } input 4#u64
            ok { s with extract_marker := () }) := rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
      riscv2zisk_single_row.Rv64imSingleRowOpcode.Jal false = ok { ctx0 with extract_marker := () } := by
    rw [harm, hctx0]; rfl
  have hlowop : aeneas_extract.lowering_opcode RiscvOpcode.Jal
      = ok (some riscv2zisk_single_row.Rv64imSingleRowOpcode.Jal) := rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = 0#u8; rw [hrop]; exact hop2
  · show row.is_external_op = false; rw [hrext]; exact hext2
  · show row.m32 = false; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = true; rw [hrstp]; exact hstp2cond (by rw [hinput] at hrd_ne ⊢; exact hrd_ne)
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2

theorem jal_decode_fields_of_binding (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) :
    msg.op = OP_FLAG ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj2⟩ := transpile_jal rd imm hrd hrd0
  obtain ⟨ho, hjo2, hf⟩ :=
    branch_decode_fields_false line msg _ 0#u8 OP_FLAG ext (by simp [OP_FLAG]) hok hop hj2 hbind
  exact ⟨ho, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_jal_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_jal trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) :
    ZiskFv.Compliance.Decode_jal trace i c := by
  set ext := (transpile_jal rd imm hrd hrd0).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj2⟩ := (transpile_jal rd imm hrd hrd0).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_jal_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj2', hflags⟩ :=
    branch_decode_fields_false (trace.program j).line (trace.program j) _ 0#u8 OP_FLAG ext
      (by simp [OP_FLAG]) hok hop hj2 hbk
  exact ⟨ho, hj2', hflags⟩

/-! ## JALR (I-type word `… 0x67`, `decode_i … false` → `jalr` → `OP_AND`,
`set_pc = true`, `store_pc = true`).  The `i.imm % 4` TWO-ROW split is handled in
`jalr_ok`; `Decode_jalr_of_program` pins NO jmp_offset, so the bridge threads only
`op` / `flags`, plus the genuine operand-side JALR witnesses (`flag` / a-mask /
c-mask / offset bridge / even / no-wrap) as caller hypotheses. -/

theorem transpile_jalr (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) = ok ext
      ∧ ext.row.op = 14#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = true ∧ ext.row.store_pc = true := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67))
      = aeneas_extract.rv64im_decode.decode_i
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) RiscvOpcode.Jalr false := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x67 (by norm_num)]
    all_goals rfl
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, hrdbv⟩ :=
    decode_i_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) RiscvOpcode.Jalr false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hbveq : decoded.rd.bv = BitVec.ofNat 32 rd := by
    rw [hrdbv]
    show ((ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67) &&& 3968#32) >>> 7
      = BitVec.ofNat 32 rd
    exact rawIType_rd imm rs1 0 rd 0x67 hrd (by norm_num) (by norm_num)
  have hrd_ne : input.rd ≠ 0#u32 := by
    rw [hinput]; exact rd_ne_zero_u32 decoded.rd rd hrd hrd0 hbveq
  obtain ⟨ctx0, hctx0⟩ := jalr_ok { defCtx with extract_marker := () } input
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrdb) (by rw [hinput])
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.jalr_static_pins_full { defCtx with extract_marker := () } input 4#u64 ctx0 hrd_ne hctx0
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have harm : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
        riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false
      = (do let s ← riscv2zisk_context.Riscv2ZiskContext.jalr { defCtx with extract_marker := () } input 4#u64
            ok { s with extract_marker := () }) := rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
      riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr false = ok { ctx0 with extract_marker := () } := by
    rw [harm, hctx0]; rfl
  have hlowop : aeneas_extract.lowering_opcode RiscvOpcode.Jalr
      = ok (some riscv2zisk_single_row.Rv64imSingleRowOpcode.Jalr) := rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = 14#u8; rw [hrop]; exact hop2
  · show row.is_external_op = true; rw [hrext]; exact hext2
  · show row.m32 = false; rw [hrm32]; exact hm322
  · show row.set_pc = true; rw [hrsp]; exact hsp2
  · show row.store_pc = true; rw [hrstp]; exact hstp2

noncomputable def Decode_jalr_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_jalr trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_flag : (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).flag i.val = 0)
    (h_a_mask_lo : (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_0 i.val = 4294967294)
    (h_a_mask_hi : (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).a_1 i.val = 4294967295)
    (h_c1_zero : (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_1 i.val = 0)
    (h_offset_bridge : ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val
      = c.offset_bv.toNat)
    (h_offset_even : c.offset_bv &&& 1#64 = 0#64)
    (h_no_fgl_wrap : ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).c_0 i.val).val
      + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val < GL_prime)
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67) :
    ZiskFv.Compliance.Decode_jalr trace i c := by
  set ext := (transpile_jalr rd rs1 imm hrd hrs1 hrd0).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc⟩ := (transpile_jalr rd rs1 imm hrd hrs1 hrd0).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_jalr_of_program trace i c h_idx h_flag h_a_mask_lo
    h_a_mask_hi h_c1_zero h_offset_bridge h_offset_even h_no_fgl_wrap
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line
          (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hflags⟩ :=
    op_flags_of_binding (trace.program j).line (trace.program j) _ 14#u8 OP_AND ext
      (by simp [OP_AND]) hok hop hbk
  exact ⟨ho, hflags⟩

/-! ## FENCE (supported-FENCE word `rawSupportedFence`, `decode_fence` → `nop` →
`OP_FLAG`).  Both jump slots are the constant fall-through; the claim-side
`fm = 0` / `rs = x0` / `rd = x0` are threaded as caller hypotheses (the FENCE
defect scope, matching `Decode_fence_of_program`). -/

theorem transpile_fence (pred succ : Nat) (hp : pred < 16) (hs : succ < 16) :
    ∃ ext, extract_transpile_rv64im_raw
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ)) = ok ext
      ∧ ext.row.op = 0#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  obtain ⟨decoded, hdec0, hopd⟩ :
      ∃ d, aeneas_extract.rv64im_decode.decode_32_core
          (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ)) = ok d
        ∧ d.opcode = RiscvOpcode.Fence :=
    ⟨_, by
      simp only [aeneas_extract.rv64im_decode.decode_32_core, aeneas_extract.rv64im_decode.decode_fence,
        aeneas_extract.rv64im_decode.DecodedRv64im.new, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and28672,
        ZiskFv.Compliance.Decode.toU32_and3968, ZiskFv.Compliance.Decode.toU32_and1015808,
        ZiskFv.Compliance.Decode.toU32_and4027551616, ZiskFv.Compliance.Decode.toU32_and15,
        ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr7,
        ZiskFv.Compliance.Decode.toU32_shr15, ZiskFv.Compliance.Decode.toU32_shr20,
        ZiskFv.Compliance.Decode.toU32_shr24, ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawSupportedFence_opcode,
        ZiskFv.Compliance.Decode.rawSupportedFence_funct3 pred succ hp hs,
        ZiskFv.Compliance.Decode.rawSupportedFence_zeros pred succ hp hs]
      rfl, rfl⟩
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  obtain ⟨ctx0, hctx0⟩ := nop_ok { defCtx with extract_marker := () } input 4#u64
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.nop_static_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    ZiskFv.Compliance.Extraction.nop_dynamic_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have harm : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
        riscv2zisk_single_row.Rv64imSingleRowOpcode.Fence false
      = (do let s ← riscv2zisk_context.Riscv2ZiskContext.nop { defCtx with extract_marker := () } input 4#u64
            ok { s with extract_marker := () }) := rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input
      riscv2zisk_single_row.Rv64imSingleRowOpcode.Fence false = ok { ctx0 with extract_marker := () } := by
    rw [harm, hctx0]; rfl
  have hlowop : aeneas_extract.lowering_opcode RiscvOpcode.Fence
      = ok (some riscv2zisk_single_row.Rv64imSingleRowOpcode.Fence) := rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [aeneas_extract.extract_transpile_rv64im_raw, hdec0]
    simp only [bind_ok, Bind.bind, hdext, hopd, hlowop]
    simp only [defCtx] at hlower
    simp only [riscv2zisk_single_row.Rv64imLoweringInput.new, bind_ok, ← hinput,
      hlower, hzib, core.option.Option.unwrap, Result.ofOption, hrow]
  · show row.op = 0#u8; rw [hrop]; exact hop2
  · show row.is_external_op = false; rw [hrext]; exact hext2
  · show row.m32 = false; rw [hrm32]; exact hm322
  · show row.set_pc = false; rw [hrsp]; exact hsp2
  · show row.store_pc = false; rw [hrstp]; exact hstp2
  · show row.jmp_offset1 = _; rw [hrj1]; exact hj1
  · show row.jmp_offset2 = _; rw [hrj2]; exact hj2

noncomputable def Decode_fence_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_fence trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_fm_zero : c.fm = 0#4)
    (h_rs_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rs)
    (h_rd_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rd)
    (pred succ : Nat) (hp : pred < 16) (hs : succ < 16)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ) :
    ZiskFv.Compliance.Decode_fence trace i c := by
  set ext := (transpile_fence pred succ hp hs).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := (transpile_fence pred succ hp hs).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_fence_of_program trace i c h_idx h_fm_zero h_rs_x0 h_rd_x0
    (romFlagBitsOfExtract ext.row) hieo hsetpc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line
          (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 0#u8 OP_FLAG ext
      (by simp [OP_FLAG]) hok hop hj1 hj2 hbk
  exact ⟨ho, hjo1, hjo2, hf⟩

section AxiomAudit
#print axioms transpile_lui
#print axioms Decode_lui_from_rawProgram
#print axioms transpile_auipc
#print axioms Decode_auipc_from_rawProgram
#print axioms transpile_jal
#print axioms Decode_jal_from_rawProgram
#print axioms transpile_jalr
#print axioms Decode_jalr_from_rawProgram
#print axioms transpile_fence
#print axioms Decode_fence_from_rawProgram
#print axioms transpile_beq
#print axioms beq_decode_fields_of_binding
#print axioms Decode_beq_from_rawProgram
#print axioms Decode_bne_from_rawProgram
#print axioms Decode_bgeu_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
