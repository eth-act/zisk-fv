import ZiskFv.Compliance.TraceLevelExport.RawProgramBinding
import ZiskFv.Compliance.TraceLevelExport.ProgramDecode
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

private theorem rawRType_rd (funct7 rs2 rs1 funct3 rd opcode : Nat)
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

private theorem and3968_ushift7 (x : BitVec 32) :
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

theorem store_reg_raw_index_pins
    (self z : zisk_inst_builder.ZiskInstBuilder) (rd : Std.U32)
    (hrd : rd.val < 32)
    (hzero : self.i.store_offset = 0#i64) (hstore : self.i.store = 0#u64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self
      (UScalar.hcast IScalarTy.I64 rd) false false = ok z) :
    z.i.store_offset.val = rd.val ∧ z.i.store ≠ zisk_inst.STORE_IND
      ∧ (rd.val ≠ 0 → z.i.store = zisk_inst.STORE_REG) := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  have e1 := ZiskFv.Compliance.Extraction.cast_one_i64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_i64
  have erd := ZiskFv.Compliance.Extraction.hcast_u32_i64_val rd
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       exact ⟨by scalar_tac, by simp [hstore, zisk_inst.STORE_IND],
         by intro habs; exfalso; scalar_tac⟩)
    | (rw [Result.ok.injEq] at h; subst h
       exact ⟨by scalar_tac, by simp [zisk_inst.STORE_REG, zisk_inst.STORE_IND], fun _ => rfl⟩)
    | (exfalso; scalar_tac)

theorem src_a_reg_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64) (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg self reg usp = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

private theorem src_b_reg_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64) (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg usp = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem op_zisk_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (op : zisk_ops.ZiskOp)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    Bind.bind] at h
  obtain ⟨ot, hot, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨b, hb, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨cval, hc, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zot, hzot, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨i1, hi1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨mval, hm, h4⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hself1
  rw [Result.ok.injEq] at h h4
  subst h
  subst h4
  exact ⟨rfl, rfl⟩

theorem j_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (j1 j2 : Std.I64)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j] at h
  rw [Result.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

theorem create_register_op_typed_store_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.store_offset.val = i.rd.val ∧ zib.i.store ≠ zisk_inst.STORE_IND
        ∧ (i.rd.val ≠ 0 → zib.i.store = zisk_inst.STORE_REG) := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨s1, h7, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have h30 : z3.i.store_offset = 0#i64 ∧ z3.i.store = 0#u64 := by
    simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
      zisk_inst_builder.ZiskInstBuilder.new,
      zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
      zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
      bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h0
    rw [Result.ok.injEq] at h0
    subst z0
    obtain ⟨ha0, ha1⟩ := src_a_reg_pres_store _ _ _ _ h1
    obtain ⟨hb0, hb1⟩ := src_b_reg_pres_store _ _ _ _ h2
    obtain ⟨ho0, ho1⟩ := op_zisk_pres_store _ _ _ h3
    exact ⟨ho0.trans (hb0.trans ha0), ho1.trans (hb1.trans ha1)⟩
  obtain ⟨hso, hst, hsr⟩ := store_reg_raw_index_pins z3 z4 i.rd hrd h30.1 h30.2 h4
  obtain ⟨hjso, hjst⟩ := j_pres_store _ _ _ _ h5
  have hz65 := ZiskFv.Compliance.Extraction.build_eq _ _ h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_⟩
  · rw [hz65, hjso]; exact hso
  · rw [hz65]; exact fun hh => hst (hjst.symm.trans hh)
  · intro hrd0; rw [hz65, hjst]; exact hsr hrd0

/-- The REAL transpile pipeline on a register-op raw word `raw` reduces to the
    op's decode-field pins, given: the decode classifies to `decode_r raw rop`;
    `rop` lowers to the single-row opcode `srop`; the dispatcher routes `srop`
    unconditionally to `create_register_op_typed … zop 4`; and the static op-type
    facts (`code`/`is_m32`/`op_type`, external). -/
theorem transpile_register_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (rdv : Nat)
    (hrdv : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rd.val = rdv)
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
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rdv
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (rdv ≠ 0 → ext.row.store = zisk_inst.STORE_REG) := by
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
  obtain ⟨zibS, hzibS, hstoreOffset, hstoreInd, hstoreReg⟩ :=
    create_register_op_typed_store_pins
      { defCtx with extract_marker := () } input zop 4#u64 ctx0 (by rw [hinput]; exact hrdb) hctx0
  have hzzS : zibS = zib := Option.some.inj (hzibS.symm.trans hzib)
  rw [hzzS] at hstoreOffset hstoreInd hstoreReg
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm, hctx0]; rfl
  have hrStoreOffset : row.store_offset = zib.i.store_offset := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrStore : row.store = zib.i.store := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  refine ⟨{ accepted := true, decode := dext, row := row },
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · show row.store_offset.val = rdv
    rw [hrStoreOffset, hstoreOffset, hinput]
    exact_mod_cast hrdv decoded hdecoded
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]; exact hstoreInd
  · intro hrd0
    show row.store = zisk_inst.STORE_REG
    rw [hrStore]
    exact hstoreReg (by rw [hinput]; exact_mod_cast (by
      intro he; exact hrd0 (by rw [← hrdv decoded hdecoded, ← he])))

/-! ## Generic decode-field bridge for register ops. -/

private theorem hcast4 : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-- The committed message's register-op decode fields, from its raw word binding. -/
theorem register_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (rdv : Nat)
    (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hstoreOffset : ext.row.store_offset.val = rdv)
    (hstoreInd : ext.row.store ≠ zisk_inst.STORE_IND)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rdv : FGL)
      ∧ (romFlagBitsOfExtract ext.row).store_ind = false
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4; rw [hj1]; norm_num [hcast4]
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4; rw [hj2]; norm_num [hcast4]
  · rw [hmsg]
    show (ext.row.store_offset.val : FGL) = (rdv : FGL)
    rw [hstoreOffset]
    norm_num
  · simp only [romFlagBitsOfExtract]
    exact decide_eq_false hstoreInd
  · rw [hmsg]; rfl

/-! ## Per-op macro: emits `transpile_<op>` + `<op>_decode_fields_of_binding`
    + `Decode_<op>_from_rawProgram` for an unconditional register-register op. -/

local macro "reg_op" nm:ident "," f7:term "," f3:term "," opw:term ","
    rop:term "," srop:term "," zop:term "," opU8:term "," m32:term "," ot:term ","
    opc:ident : command => do
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
        have hi3' :
            i3 = toU32 (BitVec.ofNat 32 rd) := by
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
            rw [and3968_ushift7,
              rawRType_rd $f7 rs2 rs1 $f3 rd $opw hrd (by norm_num)]
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
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hstoreOffset, hstoreInd, _⟩ :=
        $tName rd rs1 rs2 hrd hrs1 hrs2
      obtain ⟨ho, hjo1, hjo2, hso, hsi, hf⟩ :=
        register_decode_fields_of_binding line msg _ $opU8 $opc rd ext
          (by simp [romOpcode, $opc:term]) hok hop hj1 hj2 hstoreOffset hstoreInd hbind
      exact ⟨ho, hjo1, hjo2, hso, ext, hok, hieo, hm32, hsetpc, hstorepc, hsi, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

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

/-! ## Current `ProgramDecode` retarget: unconditional SUB pilot. -/

/-- Raw-program evidence for one SUB step. The raw word is stated directly in
    terms of the claim registers, so the destination-register pin required by
    `ProgramDecode_sub.h_prog` is not a separate caller premise. -/
structure RawProgramDecode_sub {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_sub trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        addr k = (trace.program j).line ∧
          rawProgram k = ZiskFv.Completeness.Rv64imShapes.rawRType 32
            (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0
            (regidx_to_fin c.rd).val 0x33

/-- Rebuild the current committed-program SUB bundle from the raw program and
    the op-agnostic production-lowering certificate. -/
noncomputable def ProgramDecode_sub_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_sub trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_sub trace i c addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_sub trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let rs1 := (regidx_to_fin c.r1).val
  let rs2 := (regidx_to_fin c.r2).val
  let ext := (transpile_sub rd rs1 rs2 (regidx_to_fin c.rd).isLt
    (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2,
      hstoreOffset, hstoreInd, hstoreReg⟩ :=
    (transpile_sub rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose_spec
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := ?_
      h_bits_m32 := ?_
      h_bits_set_pc := ?_
      h_bits_store_pc := ?_
      h_bits_store_ind := ?_
      h_bits_store_reg := ?_
      h_prog := ?_ }
  · simpa only [ext, romFlagBitsOfExtract] using hieo
  · simpa only [ext, romFlagBitsOfExtract] using hm32
  · simpa only [ext, romFlagBitsOfExtract] using hsetpc
  · simpa only [ext, romFlagBitsOfExtract] using hstorepc
  · simp only [romFlagBitsOfExtract]
    exact decide_eq_false hstoreInd
  · intro hrd0
    simp only [romFlagBitsOfExtract]
    exact decide_eq_true (hstoreReg hrd0)
  · intro j hline
    obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
    have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
    have hbk : trace.program j =
        romMessageOfRaw (addr k)
          (ZiskFv.Completeness.Rv64imShapes.rawRType 32 rs2 rs1 0 rd 0x33) := by
      have hok' : aeneas_extract.extract_transpile_rv64im_raw
          (ZiskFv.Compliance.Decode.toU32
            (ZiskFv.Completeness.Rv64imShapes.rawRType 32
              (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0
              (regidx_to_fin c.rd).val 0x33)) = .ok ext := by
        simpa only [rd, rs1, rs2, ext] using hok
      have hnon :
          (ZiskFv.Compliance.Decode.toU32
              (ZiskFv.Completeness.Rv64imShapes.rawRType 32
                (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val 0
                (regidx_to_fin c.rd).val 0x33) &&& 127#u32) ≠ 103#u32 := by
        rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawRType_opcode]
        all_goals decide
      have hp := hprimary.2
      rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext hok' hnon] at hp
      simpa only [rd, rs1, rs2] using hp
    obtain ⟨ho, hjo1, hjo2, hso, ext', hok', hieo', hm32', hsetpc',
        hstorepc', hstoreInd', hf⟩ :=
      sub_decode_fields_of_binding rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt
        (addr k) (trace.program j) hbk
    have hext : ext' = ext := Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
    subst ext'
    refine ⟨ho, hjo1, hjo2, ?_, hf⟩
    rw [hso]
    simp only [rd, Transpiler.ind]
    apply Fin.ext
    change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
    exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num))

/-! ## Remaining unconditional register-family `ProgramDecode` bundles. -/

local macro "reg_program_decode" nm:ident "," f7:term "," f3:term "," opw:term : command => do
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
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k =
              ZiskFv.Completeness.Rv64imShapes.rawRType $f7
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
        hstoreOffset, hstoreInd, hstoreReg⟩ :=
      ($transpileName rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose_spec
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := ?_
        h_bits_m32 := ?_
        h_bits_set_pc := ?_
        h_bits_store_pc := ?_
        h_bits_store_ind := ?_
        h_bits_store_reg := ?_
        h_prog := ?_ }
    · simpa only [ext, romFlagBitsOfExtract] using hieo
    · simpa only [ext, romFlagBitsOfExtract] using hm32
    · simpa only [ext, romFlagBitsOfExtract] using hsetpc
    · simpa only [ext, romFlagBitsOfExtract] using hstorepc
    · simp only [romFlagBitsOfExtract]
      exact decide_eq_false hstoreInd
    · intro hrd0
      simp only [romFlagBitsOfExtract]
      exact decide_eq_true (hstoreReg hrd0)
    · intro j hline
      obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
      have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
      have hbk : trace.program j =
          romMessageOfRaw (addr k)
            (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) := by
        have hok' : aeneas_extract.extract_transpile_rv64im_raw
            (ZiskFv.Compliance.Decode.toU32
              (ZiskFv.Completeness.Rv64imShapes.rawRType $f7
                (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3
                (regidx_to_fin c.rd).val $opw)) = .ok ext := by
          simpa only [rd, rs1, rs2, ext] using hok
        have hnon :
            (ZiskFv.Compliance.Decode.toU32
                (ZiskFv.Completeness.Rv64imShapes.rawRType $f7
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

reg_program_decode and, 0, 7, 0x33
reg_program_decode xor, 0, 4, 0x33
reg_program_decode slt, 0, 2, 0x33
reg_program_decode sltu, 0, 3, 0x33
reg_program_decode sll, 0, 1, 0x33
reg_program_decode srl, 0, 5, 0x33
reg_program_decode sra, 32, 5, 0x33
reg_program_decode addw, 0, 0, 0x3b
reg_program_decode subw, 32, 0, 0x3b
reg_program_decode sllw, 0, 1, 0x3b
reg_program_decode srlw, 0, 5, 0x3b
reg_program_decode sraw, 32, 5, 0x3b
reg_program_decode mulw, 1, 0, 0x3b

section AxiomAudit
#print axioms transpile_sub
#print axioms sub_decode_fields_of_binding
#print axioms ProgramDecode_sub_from_rawProgram
#print axioms ProgramDecode_and_from_rawProgram
#print axioms ProgramDecode_sraw_from_rawProgram
#print axioms ProgramDecode_mulw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
