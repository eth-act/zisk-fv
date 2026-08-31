import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingImmediate
import ZiskFv.Compliance.TraceLevelExport.RawProgramBitfields

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
    `rawProgram` + `ProgramRowsBinding` + the `<op>`-shaped raw-word hypothesis +
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

theorem src_b_ind_full_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (off : Std.U64) (usp : Bool)
    (h : self.src_b_ind off usp = ok z) :
    z.i.b_src = zisk_inst.SRC_IND ∧ z.i.b_offset_imm0 = off
      ∧ z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_ind,
    zisk_inst.SRC_IND, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;>
    (rw [Result.ok.injEq] at h; subst h
     exact ⟨by simp [zisk_inst.SRC_IND], rfl, rfl, rfl⟩)

theorem ind_width_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (w : Std.U64) (h : self.ind_width w = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.ind_width] at h
  split at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | simp at h

theorem store_reg_i64_index_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (rd : Std.I64) (hrd0 : 0 ≤ rd.val) (hrd : rd.val < 32)
    (hzero : self.i.store_offset = 0#i64) (hstore : self.i.store = 0#u64)
    (h : self.store_reg rd false false = ok z) :
    z.i.store_offset.val = rd.val ∧ z.i.store ≠ zisk_inst.STORE_IND := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  have e1 := ZiskFv.Compliance.Extraction.cast_one_i64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_i64
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       constructor
       · scalar_tac
       · simp [hstore, zisk_inst.STORE_IND])
    | (rw [Result.ok.injEq] at h; subst h
       constructor
       · scalar_tac
       · simp [zisk_inst.STORE_REG, zisk_inst.STORE_IND])
    | (exfalso; scalar_tac)

theorem store_reg_i64_is_reg (self z : zisk_inst_builder.ZiskInstBuilder)
    (rd : Std.I64) (hrd0 : 0 ≤ rd.val) (hrd : rd.val < 32) (hrdne : rd.val ≠ 0)
    (h : self.store_reg rd false false = ok z) :
    z.i.store = zisk_inst.STORE_REG := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  have e1 := ZiskFv.Compliance.Extraction.cast_one_i64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_i64
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; simp [zisk_inst.STORE_REG])
    | (exfalso; scalar_tac)
  all_goals exfalso; scalar_tac

theorem store_reg_i64_selector_pin (self z : zisk_inst_builder.ZiskInstBuilder)
    (rd : Std.I64) (hrd0 : 0 ≤ rd.val) (hrd : rd.val < 32)
    (hzero : self.i.store = 0#u64)
    (h : self.store_reg rd false false = ok z) :
    z.i.store = if rd.val = 0 then 0#u64 else zisk_inst.STORE_REG := by
  by_cases hz : rd.val = 0
  · simp [hz]
    simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
      zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
      zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
      lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
    have e1 := ZiskFv.Compliance.Extraction.cast_one_i64
    have e31 := ZiskFv.Compliance.Extraction.cast_31_i64
    split_ifs at h <;>
      first
      | (rw [Result.ok.injEq] at h; subst z; exact hzero)
      | (exfalso; scalar_tac)
    all_goals exfalso; scalar_tac
  · simp [hz]
    exact store_reg_i64_is_reg self z rd hrd0 hrd hz h

theorem load_op_typed_full_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size wval : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
      s.ind_width w = ok z → z.i.ind_width = wval)
    (h : self.load_op_typed i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib
      ∧ zib.i.ind_width = wval
      ∧ zib.i.b_src = zisk_inst.SRC_IND
      ∧ zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm
      ∧ zib.i.store_offset.val = i.rd.val
      ∧ zib.i.store ≠ zisk_inst.STORE_IND
      ∧ (i.rd.val ≠ 0 → zib.i.store = zisk_inst.STORE_REG)
      ∧ zib.i.store = (if i.rd.val = 0 then 0#u64 else zisk_inst.STORE_REG)
      ∧ zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at hs1
  obtain ⟨z0, h0, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z1, h1, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z2, h2, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z3, h3, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z4, h4, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨iadd, hadd, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z5, h5, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z6, h6, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z7, h7, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨s2, h8, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  rw [Result.ok.injEq] at hs1
  subst hs1
  have hbase : z4.i.store_offset = 0#i64 ∧ z4.i.store = 0#u64 := by
    simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
      zisk_inst_builder.ZiskInstBuilder.new,
      zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
      zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
      bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h0
    rw [Result.ok.injEq] at h0
    subst z0
    obtain ⟨ha0, ha1⟩ := src_a_reg_pres_store _ _ _ _ h1
    obtain ⟨hw0, hw1⟩ := ind_width_pres_store _ _ _ h2
    obtain ⟨_, _, hb0, hb1⟩ := src_b_ind_full_pins _ _ _ _ h3
    obtain ⟨ho0, ho1⟩ := op_zisk_pres_store _ _ _ h4
    exact ⟨ho0.trans (hb0.trans (hw0.trans ha0)),
      ho1.trans (hb1.trans (hw1.trans ha1))⟩
  obtain ⟨iadd', hiadd', hiaddval⟩ :=
    ZiskFv.Compliance.Extraction.iscalar_add_zero_ok
      (UScalar.hcast IScalarTy.I64 i.rd)
  rw [hadd] at hiadd'
  injection hiadd' with hiadd'
  obtain ⟨hso, hst⟩ := store_reg_i64_index_pins z4 z5 iadd
    (by rw [hiadd', hiaddval,
      ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; omega)
    (by rw [hiadd', hiaddval,
      ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; exact_mod_cast hrd)
    hbase.1 hbase.2 h5
  have hselector := store_reg_i64_selector_pin z4 z5 iadd
    (by rw [hiadd', hiaddval,
      ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; omega)
    (by rw [hiadd', hiaddval,
      ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; exact_mod_cast hrd)
    hbase.2
    h5
  obtain ⟨hjs, hjst⟩ := j_pres_store _ _ _ _ h6
  obtain ⟨hbs, hbo, _, _⟩ := src_b_ind_full_pins z2 z3 _ _ h3
  obtain ⟨hos, _, hol⟩ := op_zisk_pres_b z3 z4 op h4
  obtain ⟨hss, _, hsl⟩ := store_reg_pres_b z4 z5 _ _ _ h5
  obtain ⟨hjsb, _, hjlb⟩ := j_pres_b z5 z6 _ _ h6
  obtain ⟨hj1, hj2⟩ := ZiskFv.Compliance.Extraction.j_jmp _ _ _ _ h6
  have hiw2 := hiw _ _ h2
  have hiw3 := (ZiskFv.Compliance.Extraction.src_b_ind_set _ _ _ _ h3).2
  have hiw4 := (ZiskFv.Compliance.Extraction.op_zisk_pres_data _ _ _ h4).1
  have hiw5 := (ZiskFv.Compliance.Extraction.store_reg_pres_data _ _ _ _ _ h5).1
  have hiw6 := (ZiskFv.Compliance.Extraction.j_pres_data _ _ _ _ h6).1
  have hz := ZiskFv.Compliance.Extraction.build_eq _ _ h7
  refine ⟨z7, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h8,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hz, hiw6, hiw5, hiw4, hiw3, hiw2]
  · rw [hz, hjsb, hss, hos, hbs]
  · rw [hz, hjlb, hsl, hol, hbo]
  · rw [hz, hjs, hso, hiadd', hiaddval,
      ZiskFv.Compliance.Extraction.hcast_u32_i64_val]
  · rw [hz]
    exact fun hh => hst (hjst.symm.trans hh)
  · intro hrdne
    rw [hz, hjst]
    exact store_reg_i64_is_reg z4 z5 iadd
      (by rw [hiadd', hiaddval,
        ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; omega)
      (by rw [hiadd', hiaddval,
        ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; exact_mod_cast hrd)
      (by rw [hiadd', hiaddval,
        ZiskFv.Compliance.Extraction.hcast_u32_i64_val]; exact_mod_cast hrdne)
      h5
  · rw [hz, hjst, hselector, hiadd', hiaddval,
      ZiskFv.Compliance.Extraction.hcast_u32_i64_val]
    simp
  · rw [hz, hj1]
  · rw [hz, hj2]

#print axioms load_op_typed_full_pins

private def loadOperandPins (before after : zisk_inst_builder.ZiskInstBuilder) : Prop :=
  after.i.a_src = before.i.a_src
    ∧ after.i.a_use_sp_imm1 = before.i.a_use_sp_imm1
    ∧ after.i.a_offset_imm0 = before.i.a_offset_imm0

private theorem loadOperandPins_trans {a b c : zisk_inst_builder.ZiskInstBuilder}
    (hab : loadOperandPins a b) (hbc : loadOperandPins b c) : loadOperandPins a c := by
  rcases hab with ⟨ha1, ha2, ha3⟩
  rcases hbc with ⟨ha1', ha2', ha3'⟩
  exact ⟨ha1'.trans ha1, ha2'.trans ha2, ha3'.trans ha3⟩

private theorem loadOperandPins_ind_width (self z : zisk_inst_builder.ZiskInstBuilder)
    (w : Std.U64) (h : self.ind_width w = ok z) : loadOperandPins self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.ind_width] at h
  split at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)
    | simp at h

private theorem loadOperandPins_src_b_ind (self z : zisk_inst_builder.ZiskInstBuilder)
    (off : Std.U64) (usp : Bool) (h : self.src_b_ind off usp = ok z) :
    loadOperandPins self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_ind, bind_ok, Bind.bind] at h
  split_ifs at h <;> (rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)

private theorem loadOperandPins_op_zisk (self z : zisk_inst_builder.ZiskInstBuilder)
    (op : zisk_ops.ZiskOp) (hinput : zisk_ops.ZiskOp.input_size op = ok 0#u64)
    (h : self.op_zisk op = ok z) :
    z.i.a_src = self.i.a_src ∧ z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1
      ∧ z.i.a_offset_imm0 = self.i.a_offset_imm0 ∧ z.i.is_precompiled = false := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from, Bind.bind] at h
  obtain ⟨ot, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨b, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨cval, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zot, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨i1, hi1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨mval, _, hself1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hself1
  rw [hinput] at hi1
  injection hi1 with hi1
  subst i1
  rw [Result.ok.injEq] at h hself1
  subst h
  subst hself1
  exact ⟨rfl, rfl, rfl, by norm_num⟩

private theorem loadOperandPins_store_reg (self z : zisk_inst_builder.ZiskInstBuilder)
    (rd : Std.I64) (usp ais : Bool) (h : self.store_reg rd usp ais = ok z) :
    loadOperandPins self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst z; exact ⟨rfl, rfl, rfl⟩)

private theorem precompiled_pres_store_reg (self z : zisk_inst_builder.ZiskInstBuilder)
    (rd : Std.I64) (usp ais : Bool) (h : self.store_reg rd usp ais = ok z) :
    z.i.is_precompiled = self.i.is_precompiled := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst z; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst z; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst z; rfl)

private theorem loadOperandPins_j (self z : zisk_inst_builder.ZiskInstBuilder)
    (j1 j2 : Std.I64) (h : self.j j1 j2 = ok z) : loadOperandPins self z := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j, bind_ok, Bind.bind] at h
  rw [Result.ok.injEq] at h
  subst z
  exact ⟨rfl, rfl, rfl⟩

private theorem loadOperandPins_build (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : self.build = ok z) : loadOperandPins self z := by
  rw [ZiskFv.Compliance.Extraction.build_eq self z h]
  exact ⟨rfl, rfl, rfl⟩

private theorem src_a_reg_u32_nonzero_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (rs1 : Std.U32) (hrs1 : rs1.val < 32) (hrs1ne : rs1.val ≠ 0)
    (h : self.src_a_reg (UScalar.cast UScalarTy.U64 rs1) false = ok z) :
    z.i.a_src = zisk_inst.SRC_REG ∧ z.i.a_use_sp_imm1 = 0#u64
      ∧ z.i.a_offset_imm0.val = rs1.val := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  have hc := ZiskFv.Compliance.Extraction.cast_u32_u64_val rs1
  have e1 := ZiskFv.Compliance.Extraction.cast_one_u64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_u64
  simp only [Bool.false_eq_true, if_false] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst z
       simp [zisk_inst.SRC_REG, hc])
    | (exfalso; scalar_tac)
  all_goals exfalso; scalar_tac

theorem load_op_typed_nonzero_rs1_full_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size wval : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32) (hrs1 : i.rs1.val < 32) (hrs1ne : i.rs1.val ≠ 0)
    (hinput : zisk_ops.ZiskOp.input_size op = ok 0#u64)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
      s.ind_width w = ok z → z.i.ind_width = wval)
    (h : self.load_op_typed i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib
      ∧ zib.i.a_src = zisk_inst.SRC_REG
      ∧ zib.i.a_offset_imm0.val = i.rs1.val
      ∧ zib.i.a_use_sp_imm1 = 0#u64
      ∧ zib.i.b_src = zisk_inst.SRC_IND
      ∧ zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm
      ∧ zib.i.store_offset.val = i.rd.val
      ∧ zib.i.store ≠ zisk_inst.STORE_IND
      ∧ (i.rd.val ≠ 0 → zib.i.store = zisk_inst.STORE_REG)
      ∧ zib.i.store = (if i.rd.val = 0 then 0#u64 else zisk_inst.STORE_REG)
      ∧ zib.i.ind_width = wval
      ∧ zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.is_precompiled = false := by
  obtain ⟨zib, hzib, hiw', hbSrc, hbOff, hstoreOff, hstore, hstoreReg,
      hstoreSelector, hj1, hj2⟩ :=
    load_op_typed_full_pins self i op w inst_size wval ctx hrd hiw h
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  simp only [riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at hs1
  obtain ⟨z0, h0, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z1, h1, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z2, h2, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z3, h3, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z4, h4, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨iadd, hadd, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z5, h5, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z6, h6, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z7, h7, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨s2, h8, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  rw [Result.ok.injEq] at hs1
  subst hs1
  obtain ⟨haSrc, haSp, haOff⟩ := src_a_reg_u32_nonzero_pins z0 z1 i.rs1 hrs1 hrs1ne h1
  obtain ⟨haSrc4, haSp4, haOff4, hpre4⟩ := loadOperandPins_op_zisk z3 z4 op hinput h4
  have hp12 := loadOperandPins_ind_width z1 z2 w h2
  have hp23 := loadOperandPins_src_b_ind z2 z3 _ _ h3
  have hp45 := loadOperandPins_store_reg z4 z5 iadd false false h5
  have hp56 := loadOperandPins_j z5 z6 _ _ h6
  have hp67 := loadOperandPins_build z6 z7 h7
  have hp14 : loadOperandPins z1 z4 :=
    loadOperandPins_trans (loadOperandPins_trans hp12 hp23)
      ⟨haSrc4, haSp4, haOff4⟩
  have hp17 := loadOperandPins_trans (loadOperandPins_trans (loadOperandPins_trans hp14 hp45) hp56) hp67
  rcases hp17 with ⟨haSrc7, haSp7, haOff7⟩
  have hzz : zib = z7 := Option.some.inj (hzib.symm.trans
    (ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h8))
  subst zib
  refine ⟨z7, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h8,
    haSrc7.trans haSrc, ?_, haSp7.trans haSp, hbSrc, hbOff, hstoreOff, hstore,
    hstoreReg, hstoreSelector, hiw', hj1, hj2, ?_⟩
  · rw [haOff7]
    exact haOff
  · have hp45' : z5.i.is_precompiled = false := by
      rw [← hpre4]
      exact precompiled_pres_store_reg z4 z5 iadd false false h5
    have hp56' : z6.i.is_precompiled = false := by
      rw [← hp45']
      simp only [zisk_inst_builder.ZiskInstBuilder.j, bind_ok, Bind.bind] at h6
      rw [Result.ok.injEq] at h6
      subst z6
      rfl
    rw [ZiskFv.Compliance.Extraction.build_eq z6 z7 h7]
    exact hp56'

#print axioms load_op_typed_nonzero_rs1_full_pins

theorem ld_op_typed_nonzero_rs1_full_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (inst_size wval : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32) (hrs1 : i.rs1.val < 32) (hrs1ne : i.rs1.val ≠ 0)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
      s.ind_width 8#u64 = ok z → z.i.ind_width = wval)
    (h : self.load_op_typed i zisk_ops.ZiskOp.CopyB 8#u64 inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib
      ∧ zib.i.a_src = zisk_inst.SRC_REG
      ∧ zib.i.a_offset_imm0.val = i.rs1.val
      ∧ zib.i.a_use_sp_imm1 = 0#u64
      ∧ zib.i.b_src = zisk_inst.SRC_IND
      ∧ zib.i.b_offset_imm0 = IScalar.hcast UScalarTy.U64 i.imm
      ∧ zib.i.store_offset.val = i.rd.val
      ∧ zib.i.store ≠ zisk_inst.STORE_IND
      ∧ (i.rd.val ≠ 0 → zib.i.store = zisk_inst.STORE_REG)
      ∧ zib.i.store = (if i.rd.val = 0 then 0#u64 else zisk_inst.STORE_REG)
      ∧ zib.i.ind_width = wval
      ∧ zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.is_precompiled = false :=
  load_op_typed_nonzero_rs1_full_pins self i zisk_ops.ZiskOp.CopyB 8#u64
    inst_size wval ctx hrd hrs1 hrs1ne rfl hiw h

#print axioms ld_op_typed_nonzero_rs1_full_pins

theorem src_b_reg_not_ind (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64) (usp : Bool) (h : self.src_b_reg reg usp = ok z) :
    z.i.b_src ≠ zisk_inst.SRC_IND := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h
       simp [zisk_inst.SRC_IMM, zisk_inst.SRC_REG, zisk_inst.SRC_MEM,
         zisk_inst.SRC_IND])
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       simp [zisk_inst.SRC_IMM, zisk_inst.SRC_REG, zisk_inst.SRC_MEM,
         zisk_inst.SRC_IND])
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h
       simp [zisk_inst.SRC_IMM, zisk_inst.SRC_REG, zisk_inst.SRC_MEM,
         zisk_inst.SRC_IND])

theorem store_ind_full_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (off : Std.I64) (usp : Bool) (h : self.store_ind off usp = ok z) :
    z.i.store = zisk_inst.STORE_IND ∧ z.i.store_offset = off
      ∧ z.i.b_src = self.i.b_src ∧ z.i.ind_width = self.i.ind_width := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_ind, zisk_inst.STORE_IND] at h
  rw [Result.ok.injEq] at h
  subst z
  exact ⟨by simp [zisk_inst.STORE_IND], rfl, rfl, rfl⟩

theorem ind_width_pres_b (self z : zisk_inst_builder.ZiskInstBuilder)
    (w : Std.U64) (h : self.ind_width w = ok z) :
    z.i.b_src = self.i.b_src := by
  simp only [zisk_inst_builder.ZiskInstBuilder.ind_width] at h
  split at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; rfl)
    | simp at h

theorem store_op_typed_full_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (w inst_size wval : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
      s.ind_width w = ok z → z.i.ind_width = wval)
    (h : self.store_op_typed i op w inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib
      ∧ zib.i.ind_width = wval
      ∧ zib.i.b_src ≠ zisk_inst.SRC_IND
      ∧ zib.i.store = zisk_inst.STORE_IND
      ∧ zib.i.store_offset = IScalar.cast IScalarTy.I64 i.imm
      ∧ zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 inst_size
      ∧ zib.i.set_pc = false ∧ zib.i.store_pc = false
      ∧ zisk_ops.ZiskOp.code op = ok zib.i.op
      ∧ zisk_ops.ZiskOp.is_m32 op = ok zib.i.m32
      ∧ ∃ ot, zisk_ops.ZiskOp.op_type op = ok ot
        ∧ zib.i.is_external_op = extBit ot := by
  have hpins :=
    ZiskFv.Compliance.Extraction.store_op_typed_pins self i op w inst_size ctx h
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_typed,
    Bind.bind, bind_ok] at h
  obtain ⟨s1, hs1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  simp only [riscv2zisk_context.Riscv2ZiskContext.store_op_with_reg_offset,
    lift, Bind.bind, bind_ok] at hs1
  obtain ⟨z0, h0, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z1, h1, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨ioff, hoff, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z2, h2, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z3, h3, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z4, h4, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z5, h5, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z6, h6, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨z7, h7, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  obtain ⟨s2, h8, hs1⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hs1
  rw [Result.ok.injEq] at hs1
  subst hs1
  have hb2 := src_b_reg_not_ind z1 z2 _ _ h2
  obtain ⟨hb3, _, _⟩ := op_zisk_pres_b z2 z3 op h3
  have hb4 := ind_width_pres_b _ _ _ h4
  obtain ⟨hst5, hso5, hb5, hiw5⟩ := store_ind_full_pins z4 z5 _ _ h5
  obtain ⟨hjb, _, _⟩ := j_pres_b z5 z6 _ _ h6
  obtain ⟨hj1, hj2⟩ := ZiskFv.Compliance.Extraction.j_jmp _ _ _ _ h6
  have hiw4 := hiw _ _ h4
  have hiw6 := (ZiskFv.Compliance.Extraction.j_pres_data _ _ _ _ h6).1
  obtain ⟨hjs, hjst⟩ := j_pres_store _ _ _ _ h6
  have hz := ZiskFv.Compliance.Extraction.build_eq _ _ h7
  obtain ⟨zp, hzp, hsp, hstp, hcode, hm32, ot, hot, hext⟩ := hpins
  have heq : zp = z7 := by
    rw [ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h8] at hzp
    injection hzp with heq
    exact heq.symm
  subst zp
  refine ⟨z7, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h8,
    ?_, ?_, ?_, ?_, ?_, ?_, hsp, hstp, hcode, hm32, ot, hot, hext⟩
  · rw [hz, hiw6, hiw5, hiw4]
  · rw [hz, hjb, hb5, hb4, hb3]
    exact hb2
  · rw [hz, hjst, hst5]
  · rw [hz, hjs, hso5]
  · rw [hz, hj1]
  · rw [hz, hj2]

#print axioms store_op_typed_full_pins

/-! ## Generic load / store decode-field bridge (adds `ind_width` to the register one). -/

private theorem loadstore_hcast4 :
    (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-- The committed message's load/store decode fields (incl. `ind_width`), from its
    raw word binding.  Extends `register_decode_fields_of_binding` with the access
    width that the load/store ROM lookup reads. -/
theorem loadstore_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (wU64 : Std.U64) (wF : FGL)
    (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hwF : (wU64.val : FGL) = wF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hiw : ext.row.ind_width = wU64)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4 ∧ msg.ind_width = wF
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4
    rw [hj1]; norm_num [loadstore_hcast4]
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4
    rw [hj2]; norm_num [loadstore_hcast4]
  · rw [hmsg]; show (ext.row.ind_width.val : FGL) = wF; rw [hiw]; exact hwF
  · rw [hmsg]; rfl

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
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ∃ d, aeneas_extract.rv64im_decode.decode_i raw rop false = ok d
        ∧ ext.row.b_src = zisk_inst.SRC_IND
        ∧ ext.row.b_offset_imm0 = IScalar.hcast UScalarTy.U64 d.imm
        ∧ ext.row.store_offset.val = d.rd.val
        ∧ ext.row.store ≠ zisk_inst.STORE_IND
        ∧ (d.rd.val ≠ 0 → ext.row.store = zisk_inst.STORE_REG)
        ∧ ext.row.store = (if d.rd.val = 0 then 0#u64 else zisk_inst.STORE_REG) := by
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
  obtain ⟨zib'', hzib'', hiw'', hbSrc, hbOff, hstoreOff, hstore, hstoreReg,
      hstoreSelector, hj1', hj2'⟩ :=
    load_op_typed_full_pins { defCtx with extract_marker := () } input zop W 4#u64
      wval ctx0 (by rw [hinput]; exact hrdb) hiw hctx0
  have hzz' : zib'' = zib := Option.some.inj (hzib''.symm.trans hzib)
  rw [hzz'] at hbSrc hbOff hstoreOff hstore hstoreReg hstoreSelector
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, hriw⟩ := from_inst_ok zib.i
  have hrBSrc : row.b_src = zib.i.b_src := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨_, _, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrBOff : row.b_offset_imm0 = zib.i.b_offset_imm0 := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨_, _, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrStoreOff : row.store_offset = zib.i.store_offset := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨_, _, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrStore : row.store = zib.i.store := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨_, _, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · refine ⟨decoded, hdecoded, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrBSrc]; exact hbSrc
    · rw [hrBOff, hbOff, hinput]
    · rw [hrStoreOff, hstoreOff, hinput]
    · rw [hrStore]; exact hstore
    · intro hne
      rw [hrStore]
      exact hstoreReg (by rw [hinput]; exact hne)
    · rw [hrStore, hstoreSelector, hinput]

/-! ## Generic store-family transpile reduction (S-type word, `decode_s`). -/

theorem transpile_store_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v extv : Bool) (otv : zisk_ops.OpType)
    (W wval : Std.U64)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_s raw rop)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (hwtot : ∀ s : zisk_inst_builder.ZiskInstBuilder,
        ∃ z, zisk_inst_builder.ZiskInstBuilder.ind_width s W = ok z)
    (hiw : ∀ (s z : zisk_inst_builder.ZiskInstBuilder),
        zisk_inst_builder.ZiskInstBuilder.ind_width s W = ok z → z.i.ind_width = wval)
    (harm : ∀ (self : riscv2zisk_context.Riscv2ZiskContext)
        (input : riscv2zisk_single_row.Rv64imLoweringInput),
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input self input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.store_op_typed
                  { self with extract_marker := () } input zop W 4#u64
                ok { s with extract_marker := () }))
    (hcode : zisk_ops.ZiskOp.code zop = ok opc) (hm32 : zisk_ops.ZiskOp.is_m32 zop = ok m32v)
    (hot : zisk_ops.ZiskOp.op_type zop = ok otv) (hextv : extBit otv = extv) :
    ∃ ext, extract_transpile_rv64im_raw raw = ok ext
      ∧ ext.row.op = opc ∧ ext.row.is_external_op = extv ∧ ext.row.m32 = m32v
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.ind_width = wval
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ∃ d, decode_s raw rop = ok d
        ∧ ext.row.store = zisk_inst.STORE_IND
        ∧ ext.row.store_offset = IScalar.cast IScalarTy.I64 d.imm := by
  obtain ⟨decoded, hdecoded, hopd, hrs1b, hrs2b⟩ := decode_s_bounds raw rop
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core raw = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  obtain ⟨ctx0, hctx0⟩ := store_op_typed_ok { defCtx with extract_marker := () } input zop W 4#u64
    hwtot (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    ZiskFv.Compliance.Extraction.store_static_pins_of { defCtx with extract_marker := () }
      input zop W 4#u64 ctx0 opc m32v extv otv hcode hm32 hot hextv hctx0
  obtain ⟨zib', hzib', hiw', hj1, hj2⟩ :=
    store_op_typed_jmp_width { defCtx with extract_marker := () } input zop W 4#u64 ctx0 wval hiw hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hiw' hj1 hj2
  obtain ⟨zib'', hzib'', hiw'', hbSrc, hstore, hstoreOff, hj1', hj2',
      hsetpc', hstorepc', hcode', hm32', ot', hot', hext'⟩ :=
    store_op_typed_full_pins { defCtx with extract_marker := () } input zop W 4#u64
      wval ctx0 hiw hctx0
  have hzz' : zib'' = zib := Option.some.inj (hzib''.symm.trans hzib)
  rw [hzz'] at hstore hstoreOff
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, hriw⟩ := from_inst_ok zib.i
  have hrStoreOff : row.store_offset = zib.i.store_offset := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨_, _, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hrStore : row.store = zib.i.store := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨_, _, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · refine ⟨decoded, hdecoded, ?_, ?_⟩
    · rw [hrStore]; exact hstore
    · rw [hrStoreOff, hstoreOff, hinput]

open RiscvOpcode riscv2zisk_single_row.Rv64imSingleRowOpcode zisk_ops.ZiskOp zisk_ops.OpType
open ZiskFv.Trusted

/-! ## Per-op macro (COPYB loads: LBU/LHU/LWU/LD): emits the triple.  These route
    to the `Internal`/`CopyB` `Decode_<op>_of_program` (no operand-bus witness). -/

local macro "load_copyb_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    width:term "," wF:term "," iwlem:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let t1 ← `(theorem $tName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) = ok ext
          ∧ ext.row.op = 1#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.ind_width = $width
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ∃ d, decode_i
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03))
                $rop false = ok d
            ∧ ext.row.b_src = zisk_inst.SRC_IND
            ∧ ext.row.b_offset_imm0 = IScalar.hcast UScalarTy.U64 d.imm
            ∧ ext.row.store_offset.val = d.rd.val
            ∧ ext.row.store ≠ zisk_inst.STORE_IND
            ∧ (d.rd.val ≠ 0 → ext.row.store = zisk_inst.STORE_REG)
            ∧ ext.row.store =
              (if d.rd.val = 0 then 0#u64 else zisk_inst.STORE_REG) := by
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
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, _⟩ :=
        $tName rd rs1 imm hrd hrs1
      obtain ⟨ho, hjo1, hjo2, hiwF, hf⟩ :=
        loadstore_decode_fields_of_binding line msg _ 1#u8 $opc $width $wF ext
          (by simp [romOpcode, $opc:term])
          (by simp) hok hop hiw hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, hiwF, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

/-! ## Per-op macro (COPYB stores: SB/SH/SW): same shape, S-type word + `store`. -/

local macro "store_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    width:term "," wF:term "," iwlem:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let t1 ← `(theorem $tName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 $f3)) = ok ext
          ∧ ext.row.op = 1#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.ind_width = $width
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ∃ d, decode_s
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 $f3))
                $rop = ok d
            ∧ ext.row.store = zisk_inst.STORE_IND
            ∧ ext.row.store_offset = IScalar.cast IScalarTy.I64 d.imm := by
      refine transpile_store_of _ $rop $srop zisk_ops.ZiskOp.CopyB 1#u8 false false
        zisk_ops.OpType.Internal $width $width ?_ rfl (fun _ => ⟨_, rfl⟩) $iwlem
        (by intro self input; rfl) rfl rfl rfl rfl
      simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
        ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
        ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
        ZiskFv.Compliance.Decode.rawSType_opcode imm rs2 rs1 $f3,
        ZiskFv.Compliance.Decode.rawSType_funct3 imm rs2 rs1 $f3 (by norm_num)]
      all_goals rfl)
  let t2 ← `(theorem $dfName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 $f3)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4 ∧ msg.ind_width = $wF
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 $f3)) = ok ext
              ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, _⟩ :=
        $tName rs1 rs2 imm hrs1 hrs2
      obtain ⟨ho, hjo1, hjo2, hiwF, hf⟩ :=
        loadstore_decode_fields_of_binding line msg _ 1#u8 $opc $width $wF ext
          (by simp [romOpcode, $opc:term])
          (by simp) hok hop hiw hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, hiwF, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

load_copyb_op lbu, 4, RiscvOpcode.Lbu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lbu, 1#u64, (1 : FGL), ind_width_set1, OP_COPYB
load_copyb_op lhu, 5, RiscvOpcode.Lhu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lhu, 2#u64, (2 : FGL), ind_width_set2, OP_COPYB
load_copyb_op lwu, 6, RiscvOpcode.Lwu, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lwu, 4#u64, (4 : FGL), ind_width_set4, OP_COPYB
load_copyb_op ld,  3, RiscvOpcode.Ld,  riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld,  8#u64, (8 : FGL), ind_width_set8, OP_COPYB

store_op sb, 0, RiscvOpcode.Sb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sb, 1#u64, (1 : FGL), ind_width_set1, OP_COPYB
store_op sh, 1, RiscvOpcode.Sh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sh, 2#u64, (2 : FGL), ind_width_set2, OP_COPYB
store_op sw, 2, RiscvOpcode.Sw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Sw, 4#u64, (4 : FGL), ind_width_set4, OP_COPYB

/-! ## SD (issue #159 block 3).  `Decode_sd_of_program`'s ROM `h_prog` omits the
    `ind_width` column (the SD width column is not a decode pin), so SD threads only
    op/jmp1/jmp2/flags via the register field bridge. -/

theorem transpile_sd (rs1 rs2 imm : Nat) (_hrs1 : rs1 < 32) (_hrs2 : rs2 < 32) :
    ∃ ext, extract_transpile_rv64im_raw
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 3)) = ok ext
      ∧ ext.row.op = 1#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.ind_width = 8#u64
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ∃ d, decode_s
          (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 3))
            RiscvOpcode.Sd = ok d
        ∧ ext.row.store = zisk_inst.STORE_IND
        ∧ ext.row.store_offset = IScalar.cast IScalarTy.I64 d.imm := by
  refine transpile_store_of _ RiscvOpcode.Sd riscv2zisk_single_row.Rv64imSingleRowOpcode.Sd
    zisk_ops.ZiskOp.CopyB 1#u8 false false zisk_ops.OpType.Internal 8#u64 8#u64
    ?_ rfl (fun _ => ⟨_, rfl⟩) ind_width_set8 (by intro self input; rfl) rfl rfl rfl rfl
  simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
    ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
    ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
    ZiskFv.Compliance.Decode.rawSType_opcode imm rs2 rs1 3,
    ZiskFv.Compliance.Decode.rawSType_funct3 imm rs2 rs1 3 (by norm_num)]
  all_goals rfl

theorem sd_decode_fields_of_binding (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 3)) :
    msg.op = OP_COPYB ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 3)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, _, hj1, hj2, _⟩ :=
    transpile_sd rs1 rs2 imm hrs1 hrs2
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ext, hok, hieo, hm32, hsetpc, hstorepc, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = OP_COPYB
    rw [hop]; simp [romOpcode, OP_COPYB]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4
    rw [hj1]; norm_num [loadstore_hcast4]
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4
    rw [hj2]; norm_num [loadstore_hcast4]
  · rw [hmsg]; rfl

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
  let t1 ← `(theorem $tName (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = $m32
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.ind_width = $width
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ∃ d, decode_i
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03))
                $rop false = ok d
            ∧ ext.row.b_src = zisk_inst.SRC_IND
            ∧ ext.row.b_offset_imm0 = IScalar.hcast UScalarTy.U64 d.imm
            ∧ ext.row.store_offset.val = d.rd.val
            ∧ ext.row.store ≠ zisk_inst.STORE_IND
            ∧ (d.rd.val ≠ 0 → ext.row.store = zisk_inst.STORE_REG)
            ∧ ext.row.store =
              (if d.rd.val = 0 then 0#u64 else zisk_inst.STORE_REG) := by
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
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, _⟩ :=
        $tName rd rs1 imm hrd hrs1
      obtain ⟨ho, hjo1, hjo2, hiwF, hf⟩ :=
        loadstore_decode_fields_of_binding line msg _ $opU8 $opc $width $wF ext
          (by simp [romOpcode, $opc:term])
          (by simp) hok hop hiw hj1 hj2 hbind
      exact ⟨ho, hjo1, hjo2, hiwF, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

load_sext_op lb, 0, RiscvOpcode.Lb, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lb, zisk_ops.ZiskOp.SignExtendB, 39#u8, false, 1#u64, (1 : FGL), ind_width_set1, OP_SIGNEXTEND_B
load_sext_op lh, 1, RiscvOpcode.Lh, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lh, zisk_ops.ZiskOp.SignExtendH, 40#u8, false, 2#u64, (2 : FGL), ind_width_set2, OP_SIGNEXTEND_H
load_sext_op lw, 2, RiscvOpcode.Lw, riscv2zisk_single_row.Rv64imSingleRowOpcode.Lw, zisk_ops.ZiskOp.SignExtendW, 41#u8, true, 4#u64, (4 : FGL), ind_width_set4, OP_SIGNEXTEND_W

/-! ## Current `ProgramDecode` retarget: load family. -/

private theorem load_rom_offset (imm : BitVec 12) (d : DecodedRv64im)
    (hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv = BitVec.signExtend 64 imm) :
    signedOffset (IScalar.hcast UScalarTy.U64 d.imm) =
      ((BitVec.signExtend 64 imm).toInt : FGL) := by
  unfold signedOffset
  exact congrArg (fun x : BitVec 64 => (x.toInt : FGL)) hdimm

private theorem load_rom_store_offset (rd : BitVec 5) (d : DecodedRv64im)
    (hrd : d.rd.bv = BitVec.ofNat 32 rd.toNat) :
    (d.rd.val : FGL) = Transpiler.ind (Transpiler.regidxOfBitVec5 rd) := by
  apply Fin.ext
  change d.rd.val % GL_prime = rd.toNat
  have hdval : d.rd.val = rd.toNat := by
    change d.rd.bv.toNat = rd.toNat
    rw [hrd, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hdval]
  exact Nat.mod_eq_of_lt (by omega)

local macro "load_copyb_program_decode" nm:ident "," inp:term "," f3:term ","
    rop:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
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
              ZiskFv.Completeness.Rv64imShapes.rawIType ($inp c).imm.toNat
                ($inp c).r1.toNat $f3 ($inp c).rd.toNat 0x03)
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      $programName trace i c := by
    let rd := ($inp c).rd.toNat
    let rs1 := ($inp c).r1.toNat
    let imm := ($inp c).imm.toNat
    let ext := ($transpileName rd rs1 imm ($inp c).rd.isLt ($inp c).r1.isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, hrow⟩ :=
      ($transpileName rd rs1 imm ($inp c).rd.isLt ($inp c).r1.isLt).choose_spec
    let d := hrow.choose
    obtain ⟨hdecode, hbSrc, hbOff, hstoreOff, hstoreInd, hstoreReg, hstoreSelector⟩ :=
      hrow.choose_spec
    have hdfields := decode_i_rawIType_fields imm rs1 $f3 rd 0x03
      ($inp c).r1.isLt (by norm_num) ($inp c).rd.isLt (by norm_num) $rop d hdecode
    have hdval : d.rd.val = ($inp c).rd.toNat := by
      change d.rd.bv.toNat = ($inp c).rd.toNat
      rw [hdfields.1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 ($inp c).imm := by
      simpa only [imm, BitVec.ofNat_toNat] using hdfields.2.2
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false hstoreInd
        h_bits_store_reg := by
          simp only [romFlagBitsOfExtract]
          rw [hstoreSelector, hdval]
          by_cases hrd : ($inp c).rd.toNat = 0
          · simp [hrd, zisk_inst.STORE_REG]
          · simp [hrd]
        h_bits_b_src_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_true hbSrc
        h_prog := by
          intro j hline
          obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
          have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
          have hbk : trace.program j =
              romMessageOfRaw (addr k)
                (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03) := by
            have hp := hprimary.2
            rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext
              (by simpa only [rd, rs1, imm, ext] using hok)
              (by
                rw [ZiskFv.Compliance.Decode.toU32_and127,
                  ZiskFv.Compliance.Decode.rawIType_opcode]
                all_goals decide)] at hp
            simpa only [rd, rs1, imm] using hp
          obtain ⟨ho, hjo1, hjo2, hiwF, ext', hok', hieo', hm32', hsetpc',
              hstorepc', hf⟩ :=
            $fieldsName rd rs1 imm ($inp c).rd.isLt ($inp c).r1.isLt
              (addr k) (trace.program j) hbk
          have hext : ext' = ext :=
            Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
          subst ext'
          refine ⟨ho, hjo1, hjo2, hiwF, ?_, ?_, hf⟩
          · rw [hbk, romMessageOfRaw, hok]
            show signedOffset ext.row.b_offset_imm0 =
              ((BitVec.signExtend 64 ($inp c).imm).toInt : FGL)
            rw [hbOff]
            exact load_rom_offset ($inp c).imm d hdimm
          · rw [hbk, romMessageOfRaw, hok]
            show (ext.row.store_offset.val : FGL) =
              Transpiler.ind (Transpiler.regidxOfBitVec5 ($inp c).rd)
            rw [hstoreOff]
            exact load_rom_store_offset ($inp c).rd d (by
              simpa only [rd, BitVec.ofNat_toNat] using hdfields.1) })
  return ⟨Lean.mkNullNode #[t1, t2]⟩

load_copyb_program_decode ld, ZiskFv.Compliance.Claim_ld.ld_input, 3, RiscvOpcode.Ld
load_copyb_program_decode lbu, ZiskFv.Compliance.Claim_lbu.lbu_input, 4, RiscvOpcode.Lbu
load_copyb_program_decode lhu, ZiskFv.Compliance.Claim_lhu.lhu_input, 5, RiscvOpcode.Lhu
load_copyb_program_decode lwu, ZiskFv.Compliance.Claim_lwu.lwu_input, 6, RiscvOpcode.Lwu

local macro "load_sext_program_decode" nm:ident "," inp:term "," f3:term ","
    rop:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let t1 ← `(structure $rawName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL
    r_binary : ℕ
    offset : ℕ
    env : Environment FGL
    h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v
    h_match :
      ZiskFv.Airs.OperationBus.matches_entry
        (ZiskFv.Airs.OperationBus.opBus_row_Main
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable)
          i.val)
        (ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r_binary)
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        ∃ k : Fin rawLength,
          addr k = (trace.program j).line ∧
            rawProgram k =
              ZiskFv.Completeness.Rv64imShapes.rawIType ($inp c).imm.toNat
                ($inp c).r1.toNat $f3 ($inp c).rd.toNat 0x03)
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      $programName trace i c := by
    let rd := ($inp c).rd.toNat
    let rs1 := ($inp c).r1.toNat
    let imm := ($inp c).imm.toNat
    let ext := ($transpileName rd rs1 imm ($inp c).rd.isLt ($inp c).r1.isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, hrow⟩ :=
      ($transpileName rd rs1 imm ($inp c).rd.isLt ($inp c).r1.isLt).choose_spec
    let d := hrow.choose
    obtain ⟨hdecode, hbSrc, hbOff, hstoreOff, hstoreInd, hstoreReg, hstoreSelector⟩ :=
      hrow.choose_spec
    have hdfields := decode_i_rawIType_fields imm rs1 $f3 rd 0x03
      ($inp c).r1.isLt (by norm_num) ($inp c).rd.isLt (by norm_num) $rop d hdecode
    have hdval : d.rd.val = ($inp c).rd.toNat := by
      change d.rd.bv.toNat = ($inp c).rd.toNat
      rw [hdfields.1, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 ($inp c).imm := by
      simpa only [imm, BitVec.ofNat_toNat] using hdfields.2.2
    refine
      { h_idx := rawDecode.h_idx
        v := rawDecode.v
        r_binary := rawDecode.r_binary
        offset := rawDecode.offset
        env := rawDecode.env
        h_static := rawDecode.h_static
        h_match := rawDecode.h_match
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false hstoreInd
        h_bits_store_reg := by
          simp only [romFlagBitsOfExtract]
          rw [hstoreSelector, hdval]
          by_cases hrd : ($inp c).rd.toNat = 0
          · simp [hrd, zisk_inst.STORE_REG]
          · simp [hrd]
        h_bits_b_src_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_true hbSrc
        h_prog := by
          intro j hline
          obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
          have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
          have hbk : trace.program j =
              romMessageOfRaw (addr k)
                (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 $f3 rd 0x03) := by
            have hp := hprimary.2
            rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext
              (by simpa only [rd, rs1, imm, ext] using hok)
              (by
                rw [ZiskFv.Compliance.Decode.toU32_and127,
                  ZiskFv.Compliance.Decode.rawIType_opcode]
                all_goals decide)] at hp
            simpa only [rd, rs1, imm] using hp
          obtain ⟨ho, hjo1, hjo2, hiwF, ext', hok', hieo', hm32', hsetpc',
              hstorepc', hf⟩ :=
            $fieldsName rd rs1 imm ($inp c).rd.isLt ($inp c).r1.isLt
              (addr k) (trace.program j) hbk
          have hext : ext' = ext :=
            Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
          subst ext'
          refine ⟨ho, hjo1, hjo2, hiwF, ?_, ?_, hf⟩
          · rw [hbk, romMessageOfRaw, hok]
            show signedOffset ext.row.b_offset_imm0 =
              ((BitVec.signExtend 64 ($inp c).imm).toInt : FGL)
            rw [hbOff]
            exact load_rom_offset ($inp c).imm d hdimm
          · rw [hbk, romMessageOfRaw, hok]
            show (ext.row.store_offset.val : FGL) =
              Transpiler.ind (Transpiler.regidxOfBitVec5 ($inp c).rd)
            rw [hstoreOff]
            exact load_rom_store_offset ($inp c).rd d (by
              simpa only [rd, BitVec.ofNat_toNat] using hdfields.1) })
  return ⟨Lean.mkNullNode #[t1, t2]⟩

load_sext_program_decode lb, ZiskFv.Compliance.Claim_lb.lb_input, 0, RiscvOpcode.Lb
load_sext_program_decode lh, ZiskFv.Compliance.Claim_lh.lh_input, 1, RiscvOpcode.Lh
load_sext_program_decode lw, ZiskFv.Compliance.Claim_lw.lw_input, 2, RiscvOpcode.Lw

/-! ## Current `ProgramDecode` retarget: store family. -/

private theorem store_rom_offset (imm : BitVec 12) (d : DecodedRv64im)
    (hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv = BitVec.signExtend 64 imm) :
    ((IScalar.cast IScalarTy.I64 d.imm).val : FGL) =
      ((BitVec.signExtend 64 imm).toInt : FGL) := by
  congr 1
  change (BitVec.signExtend 64 d.imm.bv).toInt = _
  rw [show BitVec.signExtend 64 d.imm.bv = BitVec.signExtend 64 imm by
    simpa only using hdimm]

local macro "store_program_decode" nm:ident "," inp:term "," f3:term ","
    rop:term : command => do
  let s := nm.getId.toString
  let rawName := Lean.mkIdent (Lean.Name.mkSimple ("RawProgramDecode_" ++ s))
  let ctorName := Lean.mkIdent (Lean.Name.mkSimple ("ProgramDecode_" ++ s ++ "_from_rawProgram"))
  let transpileName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let fieldsName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let claimName := Lean.mkIdent ((`ZiskFv.Compliance).str ("Claim_" ++ s))
  let programName := Lean.mkIdent ((`ZiskFv.Compliance.RomDecodeBinding).str ("ProgramDecode_" ++ s))
  let decodeFieldsName := Lean.mkIdent `decode_s_rawSType_fields
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
              ZiskFv.Completeness.Rv64imShapes.rawSType ($inp c).imm.toNat
                ($inp c).r2.toNat ($inp c).r1.toNat $f3)
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c addr rawProgram) :
      $programName trace i c := by
    let rs1 := ($inp c).r1.toNat
    let rs2 := ($inp c).r2.toNat
    let imm := ($inp c).imm.toNat
    let ext := ($transpileName rs1 rs2 imm ($inp c).r1.isLt ($inp c).r2.isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, hrowStore⟩ :=
      ($transpileName rs1 rs2 imm ($inp c).r1.isLt ($inp c).r2.isLt).choose_spec
    let d := hrowStore.choose
    obtain ⟨hdecode, hstore, hstoreOff⟩ := hrowStore.choose_spec
    have hdfields := $decodeFieldsName imm rs2 rs1 $f3
      ($inp c).r2.isLt ($inp c).r1.isLt (by norm_num) $rop d hdecode
    have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 ($inp c).imm := by
      simpa only [imm, BitVec.ofNat_toNat] using hdfields.2.2
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_ind := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_true hstore
        h_bits_store_reg := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false (by
            rw [hstore]
            simp [zisk_inst.STORE_IND, zisk_inst.STORE_REG])
        h_prog := by
          intro j hline
          obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
          have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
          have hbk : trace.program j =
              romMessageOfRaw (addr k)
                (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 $f3) := by
            have hp := hprimary.2
            rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext
              (by simpa only [rs1, rs2, imm, ext] using hok)
              (by
                rw [ZiskFv.Compliance.Decode.toU32_and127,
                  ZiskFv.Compliance.Decode.rawSType_opcode]
                all_goals decide)] at hp
            simpa only [rs1, rs2, imm] using hp
          obtain ⟨ho, hjo1, hjo2, hiwF, ext', hok', hieo', hm32', hsetpc',
              hstorepc', hf⟩ :=
            $fieldsName rs1 rs2 imm ($inp c).r1.isLt ($inp c).r2.isLt
              (addr k) (trace.program j) hbk
          have hext : ext' = ext :=
            Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
          subst ext'
          refine ⟨ho, hjo1, hjo2, hiwF, ?_, hf⟩
          rw [hbk, romMessageOfRaw, hok]
          show (ext.row.store_offset.val : FGL) =
            ((BitVec.signExtend 64 ($inp c).imm).toInt : FGL)
          rw [hstoreOff]
          exact store_rom_offset ($inp c).imm d hdimm })
  return ⟨Lean.mkNullNode #[t1, t2]⟩

store_program_decode sb, ZiskFv.Compliance.Claim_sb.sb_input, 0, RiscvOpcode.Sb
store_program_decode sh, ZiskFv.Compliance.Claim_sh.sh_input, 1, RiscvOpcode.Sh
store_program_decode sw, ZiskFv.Compliance.Claim_sw.sw_input, 2, RiscvOpcode.Sw

structure RawProgramDecode_sd {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_sd trace i)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      ∃ k : Fin rawLength,
        addr k = (trace.program j).line ∧
          rawProgram k =
            ZiskFv.Completeness.Rv64imShapes.rawSType c.sd_input.imm.toNat
              c.sd_input.r2.toNat c.sd_input.r1.toNat 3

noncomputable def ProgramDecode_sd_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_sd trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_sd trace i c addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_sd trace i c := by
  let rs1 := c.sd_input.r1.toNat
  let rs2 := c.sd_input.r2.toNat
  let imm := c.sd_input.imm.toNat
  let ext := (transpile_sd rs1 rs2 imm c.sd_input.r1.isLt c.sd_input.r2.isLt).choose
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hiw, hj1, hj2, hrowStore⟩ :=
    (transpile_sd rs1 rs2 imm c.sd_input.r1.isLt c.sd_input.r2.isLt).choose_spec
  let d := hrowStore.choose
  obtain ⟨hdecode, hstore, hstoreOff⟩ := hrowStore.choose_spec
  have hdfields := decode_s_rawSType_fields imm rs2 rs1 3
    c.sd_input.r2.isLt c.sd_input.r1.isLt (by norm_num) RiscvOpcode.Sd d hdecode
  have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
      BitVec.signExtend 64 c.sd_input.imm := by
    simpa only [imm, BitVec.ofNat_toNat] using hdfields.2.2
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_true hstore
      h_bits_store_reg := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false (by
          rw [hstore]
          simp [zisk_inst.STORE_IND, zisk_inst.STORE_REG])
      h_prog := by
        intro j hline
        obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
        have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
        have hbk : trace.program j =
            romMessageOfRaw (addr k)
              (ZiskFv.Completeness.Rv64imShapes.rawSType imm rs2 rs1 3) := by
          have hp := hprimary.2
          rw [hraw, romMessagesOfRaw_fst_of_non_jalr _ _ ext
            (by simpa only [rs1, rs2, imm, ext] using hok)
            (by
              rw [ZiskFv.Compliance.Decode.toU32_and127,
                ZiskFv.Compliance.Decode.rawSType_opcode]
              all_goals decide)] at hp
          simpa only [rs1, rs2, imm] using hp
        obtain ⟨ho, hjo1, hjo2, ext', hok', hieo', hm32', hsetpc',
            hstorepc', hf⟩ :=
          sd_decode_fields_of_binding rs1 rs2 imm c.sd_input.r1.isLt c.sd_input.r2.isLt
            (addr k) (trace.program j) hbk
        have hext : ext' = ext :=
          Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
        subst ext'
        refine ⟨ho, hjo1, hjo2, ?_, hf⟩
        rw [hbk, romMessageOfRaw, hok]
        show (ext.row.store_offset.val : FGL) =
          ((BitVec.signExtend 64 c.sd_input.imm).toInt : FGL)
        rw [hstoreOff]
        exact store_rom_offset c.sd_input.imm d hdimm }

section AxiomAudit
#print axioms transpile_lbu
#print axioms lbu_decode_fields_of_binding
#print axioms transpile_ld
#print axioms transpile_sb
#print axioms transpile_sd
#print axioms transpile_lb
#print axioms transpile_lw
#print axioms ProgramDecode_sb_from_rawProgram
#print axioms ProgramDecode_sh_from_rawProgram
#print axioms ProgramDecode_sw_from_rawProgram
#print axioms ProgramDecode_sd_from_rawProgram
#print axioms ProgramDecode_ld_from_rawProgram
#print axioms ProgramDecode_lbu_from_rawProgram
#print axioms ProgramDecode_lhu_from_rawProgram
#print axioms ProgramDecode_lwu_from_rawProgram
#print axioms ProgramDecode_lb_from_rawProgram
#print axioms ProgramDecode_lh_from_rawProgram
#print axioms ProgramDecode_lw_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
