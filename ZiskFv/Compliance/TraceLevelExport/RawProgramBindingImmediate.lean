import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister

/-!
# Raw-program decode bridge — immediate-ALU / shift family (issue #159, BLOCK 3)

Mirrors the register-register bridge (`RawProgramBindingRegister`) for the plain
immediate-ALU and shift-immediate opcodes, with the raw word's `rd`/`rs1`/`imm`
(resp. `shamt`) SYMBOLIC.  The canonical builder is `immediate_op_typed`, whose
second operand is the unconditionally-total `src_b_imm`, so totality needs only
`rd < 32 ∧ rs1 < 32` (no rs2, no `≠ 0`).  For each op `<op>`:

  * `transpile_<op>` — the REAL Aeneas pipeline `extract_transpile_rv64im_raw` on
    the symbolic I-type / shift word reduces to the op's decode-field pins.
    Decode classification reuses #164's `rawIType_{opcode,funct3}` (and, for shifts,
    `rawIType_funct6_*` / `rawIType_funct7_*`) masks; lowering TOTALITY reuses
    `Extraction.immediate_op_typed_ok` + `Extraction.decode_i_bounds` (#159 block-3
    `Totality.lean`); the field pins reuse #111 `immediate_static_pins_of` +
    block-2 `immediate_op_typed_dynamic_pins`.
  * `<op>_decode_fields_of_binding` — the committed message's decode fields,
    derived from its raw word + the op-agnostic `romMessageOfRaw` binding (the
    generic `register_decode_fields_of_binding` is reused verbatim — it is op-shape
    agnostic).
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
  (defCtx decode_i_bounds immediate_op_typed_ok decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Bit-reorder: `(x &&& 3968) >>> 7 = (x >>> 7) &&& 31` (the [7,11] field, mask
    `3968 = 31 <<< 7`).  Lets us reuse the `>>>`-then-`&&&` extraction primitive. -/
private theorem and3968_shr7 (x : BitVec 32) :
    (x &&& 3968#32) >>> 7 = (x >>> 7) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    show (3968:Nat) = 31 <<< 7 by decide, Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge i 5 with h5 | h5
  · rw [decide_eq_true (show 7 + i < 32 by omega), decide_eq_true (show i < 32 by omega)]
    simp [show (7 : Nat) ≤ 7 + i by omega, show 7 + i - 7 = i by omega]
  · rw [ZiskFv.Compliance.Decode.tbf (show (31:Nat) < 2 ^ 5 by norm_num) (show 5 ≤ 7 + i - 7 by omega),
      ZiskFv.Compliance.Decode.tbf (show (31:Nat) < 2 ^ 5 by norm_num) (show 5 ≤ i by omega)]
    simp

/-- The decoder's `rd` field (`inst &&& 3968 >>> 7`, bits [7,11]) of an `rawIType`
    word recovers `rd` for `rd < 32`. -/
private theorem rawIType_rd (imm rs1 funct3 rd opcode : Nat) (hrd : rd < 32)
    (hf3 : funct3 < 8) (hop : opcode < 128) :
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

/-- The REAL transpile pipeline on an immediate-op raw word `raw` reduces to the
    op's decode-field pins, given: the decode classifies to `decode_i raw rop sh`;
    `rop` lowers to the single-row opcode `srop`; the dispatcher routes `srop` to
    `immediate_op_typed … zop 4` (under the side-condition `P` on the lowering
    input — `True` for the unconditional immediates, `rd ≠ 0` for ADDIW); and the
    static op-type facts (`code`/`is_m32`/`op_type`, external). -/
theorem transpile_immediate_of
    (raw : Std.U32) (rop : RiscvOpcode) (sh : Bool)
    (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (P : riscv2zisk_single_row.Rv64imLoweringInput → Prop)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_i raw rop sh)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (self : riscv2zisk_context.Riscv2ZiskContext)
        (input : riscv2zisk_single_row.Rv64imLoweringInput), P input →
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input self input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.immediate_op_typed
                  { self with extract_marker := () } input zop 4#u64
                ok { s with extract_marker := () }))
    (hP : ∀ d : aeneas_extract.rv64im_decode.DecodedRv64im,
        aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d →
        P { rom_address := 0#u64, rd := d.rd, rs1 := d.rs1, rs2 := d.rs2, imm := d.imm })
    (hcode : zisk_ops.ZiskOp.code zop = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 zop = ok m32v)
    (hot : zisk_ops.ZiskOp.op_type zop = ok otv)
    (hint : otv ≠ zisk_ops.OpType.Internal) (hfc : otv ≠ zisk_ops.OpType.Fcall) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = true ∧ ext.row.m32 = m32v
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, _⟩ := decode_i_bounds raw rop sh
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hPin : P input := hP decoded hdecoded
  obtain ⟨ctx0, hctx0⟩ := immediate_op_typed_ok { defCtx with extract_marker := () } input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.immediate_static_pins_of { defCtx with extract_marker := () }
      input zop 4#u64 ctx0 opc m32v otv hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    ZiskFv.Compliance.Extraction.immediate_op_typed_dynamic_pins
      { defCtx with extract_marker := () } input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input hPin, hctx0]; rfl
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

/-! ## Per-op macro (non-shift I-type): emits `transpile_<op>` +
    `<op>_decode_fields_of_binding` + `Decode_<op>_from_rawProgram`. -/

local macro "imm_op" nm:ident "," f3:term "," opw:term ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let t1 ← `(theorem $tName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
      refine transpile_immediate_of _ $rop false $srop $zop $opU8 $m32 $ot (fun _ => True) ?_ rfl
        (by intro self input _; rfl) (fun _ _ => trivial)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 $f3 rd $opw (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 $f3 rd $opw (by norm_num) hrd (by norm_num)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := $tName rd rs1 imm hrd hrs1
      obtain ⟨ho, hjo1, hjo2, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc ext (by simp [$opc:term]) hok hop hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw) :
        $decodeT trace i c := by
      set ext := ($tName rd rs1 imm hrd hrs1).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
        ($tName rd rs1 imm hrd hrs1).choose_spec
      refine $decodeOf trace i c h_idx (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd $opw) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hj2', hflags⟩ :=
        register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
          (by simp [$opc:term]) hok hop hj1 hj2 hbk
      exact ⟨ho, hj1', hj2', hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

/-! ## Per-op macro (shift-immediate): emits the same triple, but the raw word is
    `rawIType (upper ||| shamt) rs1 funct3 rd opcode`, the decode classifies through
    the funct6/funct7 sub-discriminant (`shift_level = true`), and the genuine
    side-condition is the shamt bound (`< 64` for 0x13, `< 32` for 0x1b). -/

local macro "shift_op" nm:ident "," upper:term "," f3:term "," opw:term ","
    shbound:term "," f67lemma:ident ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let f67 := Lean.mkIdent ((`ZiskFv.Compliance.Decode).str f67lemma.getId.toString)
  let t1 ← `(theorem $tName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < $shbound) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
      refine transpile_immediate_of _ $rop true $srop $zop $opU8 $m32 $ot (fun _ => True) ?_ rfl
        (by intro self input _; rfl) (fun _ _ => trivial)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_and63, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_shr25, ZiskFv.Compliance.Decode.toU32_shr26,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num) hrd (by norm_num),
        ($f67 shamt rs1 $f3 rd hsh hrs1 (by norm_num) hrd)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < $shbound)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := $tName rd rs1 shamt hrd hrs1 hsh
      obtain ⟨ho, hjo1, hjo2, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc ext (by simp [$opc:term]) hok hop hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < $shbound)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw) :
        $decodeT trace i c := by
      set ext := ($tName rd rs1 shamt hrd hrs1 hsh).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
        ($tName rd rs1 shamt hrd hrs1 hsh).choose_spec
      refine $decodeOf trace i c h_idx (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hj2', hflags⟩ :=
        register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
          (by simp [$opc:term]) hok hop hj1 hj2 hbk
      exact ⟨ho, hj1', hj2', hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

/-! ## Per-op macro (64-bit shift-immediate SLLI/SRLI/SRAI): same as `shift_op`,
    but `Decode_<op>_of_program` also takes the operand-column shamt low-bits binding
    `b_0 = shamt_b_lo c.shamt` (an operand-decode fact OUTSIDE the ROM decode-from-raw
    scope), threaded through as a caller hypothesis. -/

local macro "shift64_op" nm:ident "," upper:term "," f3:term "," opw:term ","
    f67lemma:ident ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let dName := Lean.mkIdent (Lean.Name.mkSimple ("Decode_" ++ s ++ "_from_rawProgram"))
  let decodeOf := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("Decode_" ++ s ++ "_of_program"))
  let claimT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let decodeT := Lean.mkIdent ((`ZiskFv.Compliance).str ("Decode_" ++ s))
  let f67 := Lean.mkIdent ((`ZiskFv.Compliance.Decode).str f67lemma.getId.toString)
  let t1 ← `(theorem $tName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 64) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
      refine transpile_immediate_of _ $rop true $srop $zop $opU8 $m32 $ot (fun _ => True) ?_ rfl
        (by intro self input _; rfl) (fun _ _ => trivial)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_and63, ZiskFv.Compliance.Decode.toU32_shr12,
        ZiskFv.Compliance.Decode.toU32_shr25, ZiskFv.Compliance.Decode.toU32_shr26,
        ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawIType_opcode ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num),
        ZiskFv.Compliance.Decode.rawIType_funct3 ($upper ||| shamt) rs1 $f3 rd $opw (by norm_num) hrd (by norm_num),
        ($f67 shamt rs1 $f3 rd hsh hrs1 (by norm_num) hrd)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 64)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := $tName rd rs1 shamt hrd hrs1 hsh
      obtain ⟨ho, hjo1, hjo2, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc ext (by simp [$opc:term]) hok hop hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  let t3 ← `(noncomputable def $dName {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
        (i : Fin trace.numInstructions) (c : $claimT trace i)
        (h_idx : i.val + 1 < trace.mainTable.table.length)
        (h_b_lo_t : (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val
            = ZiskFv.Trusted.shamt_b_lo c.shamt)
        (rd rs1 shamt : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hsh : shamt < 64)
        (rawProgram : Fin n → BitVec 32)
        (hbind : ProgramBinding trace rawProgram)
        (hLine : ∀ j : Fin n,
            (trace.program j).line
              = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
            rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw) :
        $decodeT trace i c := by
      set ext := ($tName rd rs1 shamt hrd hrs1 hsh).choose with hext
      obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
        ($tName rd rs1 shamt hrd hrs1 hsh).choose_spec
      refine $decodeOf trace i c h_idx h_b_lo_t (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
      intro j hline
      have hbk : trace.program j
          = romMessageOfRaw (trace.program j).line
              (ZiskFv.Completeness.Rv64imShapes.rawIType ($upper ||| shamt) rs1 $f3 rd $opw) :=
        (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
      obtain ⟨ho, hj1', hj2', hflags⟩ :=
        register_decode_fields_of_binding (trace.program j).line (trace.program j) _ $opU8 $opc ext
          (by simp [$opc:term]) hok hop hj1 hj2 hbk
      exact ⟨ho, hj1', hj2', hflags⟩)
  return ⟨Lean.mkNullNode #[t1, t2, t3]⟩

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

imm_op slti, 2, 0x13, RiscvOpcode.Slti, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slti, zisk_ops.ZiskOp.Lt, 7#u8, false, zisk_ops.OpType.Binary, OP_LT
imm_op sltiu, 3, 0x13, RiscvOpcode.Sltiu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sltiu, zisk_ops.ZiskOp.Ltu, 6#u8, false, zisk_ops.OpType.Binary, OP_LTU
imm_op andi, 7, 0x13, RiscvOpcode.Andi, riscv2zisk_single_row.Rv64imSingleRowOpcode.Andi, zisk_ops.ZiskOp.And, 14#u8, false, zisk_ops.OpType.Binary, OP_AND

/-! ## ADDIW (issue #159 block 3).  Unlike the other plain immediates, ADDIW's
    dispatcher arm degenerates to `nop` when `rd = 0 ∧ rs1 = 0 ∧ imm = 0`, so the
    canonical `immediate_op_typed AddW` route carries the genuine `rd ≠ 0`
    side-condition (the simplest sufficient nop-guard disproof, matching
    `Extraction.addiw_dispatch_static_pins`).  The symbolic `rd ≠ 0#u32` is derived
    from the Nat `rd ≠ 0` via the decoder's `rd`-field value (`rawIType_rd`). -/

theorem transpile_addiw (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b)) = ok ext
      ∧ ext.row.op = 26#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = true
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  refine transpile_immediate_of _ RiscvOpcode.Addiw false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Addiw zisk_ops.ZiskOp.AddW 26#u8 true zisk_ops.OpType.Binary
    (fun input => input.rd ≠ 0#u32) ?_ rfl ?_ ?_ rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x1b (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 0 rd 0x1b (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro self input hrdne
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input, Bind.bind, bind_ok]
    rw [if_neg hrdne]
  · intro d hd
    obtain ⟨d', hd', _, _, _, hrdbv'⟩ :=
      decode_i_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b))
        RiscvOpcode.Addiw false
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
    show d.rd ≠ 0#u32
    intro hcontra
    have hbv : d.rd.bv = BitVec.ofNat 32 rd := by
      rw [hdd, hrdbv']
      show ((ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b) &&& 3968#32) >>> 7
        = BitVec.ofNat 32 rd
      exact rawIType_rd imm rs1 0 rd 0x1b hrd (by norm_num) (by norm_num)
    rw [hcontra] at hbv
    have hz : (0 : Nat) = rd % 2 ^ 32 := by
      have := congrArg BitVec.toNat hbv
      simpa [BitVec.toNat_ofNat] using this
    omega

theorem addiw_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b)) :
    msg.op = OP_ADD_W ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = true
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := transpile_addiw rd rs1 imm hrd hrs1 hrd0
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 26#u8 OP_ADD_W ext (by simp [OP_ADD_W]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_addiw_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addiw trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b) :
    ZiskFv.Compliance.Decode_addiw trace i c := by
  set ext := (transpile_addiw rd rs1 imm hrd hrs1 hrd0).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ := (transpile_addiw rd rs1 imm hrd hrs1 hrd0).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_addiw_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line
          (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x1b) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 26#u8 OP_ADD_W ext
      (by simp [OP_ADD_W]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

shift64_op slli, 0, 1, 0x13, rawIType_funct6_zero, RiscvOpcode.Slli, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slli, zisk_ops.ZiskOp.Sll, 33#u8, false, zisk_ops.OpType.BinaryE, OP_SLL
shift64_op srli, 0, 5, 0x13, rawIType_funct6_zero, RiscvOpcode.Srli, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srli, zisk_ops.ZiskOp.Srl, 34#u8, false, zisk_ops.OpType.BinaryE, OP_SRL
shift64_op srai, 0x400, 5, 0x13, rawIType_funct6_sixteen, RiscvOpcode.Srai, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srai, zisk_ops.ZiskOp.Sra, 35#u8, false, zisk_ops.OpType.BinaryE, OP_SRA
shift_op slliw, 0, 1, 0x1b, 32, rawIType_funct7_zero, RiscvOpcode.Slliw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Slliw, zisk_ops.ZiskOp.SllW, 36#u8, true, zisk_ops.OpType.BinaryE, OP_SLL_W
shift_op srliw, 0, 5, 0x1b, 32, rawIType_funct7_zero, RiscvOpcode.Srliw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Srliw, zisk_ops.ZiskOp.SrlW, 37#u8, true, zisk_ops.OpType.BinaryE, OP_SRL_W
shift_op sraiw, 0x400, 5, 0x1b, 32, rawIType_funct7_thirtytwo, RiscvOpcode.Sraiw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sraiw, zisk_ops.ZiskOp.SraW, 38#u8, true, zisk_ops.OpType.BinaryE, OP_SRA_W

section AxiomAudit
#print axioms transpile_slti
#print axioms slti_decode_fields_of_binding
#print axioms Decode_slti_from_rawProgram
#print axioms transpile_slli
#print axioms Decode_slli_from_rawProgram
#print axioms transpile_sraiw
#print axioms Decode_sraiw_from_rawProgram
#print axioms transpile_addiw
#print axioms Decode_addiw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
