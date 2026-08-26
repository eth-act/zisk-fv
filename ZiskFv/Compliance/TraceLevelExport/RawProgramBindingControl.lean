import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingRegister
import ZiskFv.Compliance.TraceLevelExport.RawProgramBitfields

/-!
# Raw-program decode bridge — branch + control family (issue #159, BLOCK 3)

Mirrors the register / immediate / load-store bridges
(`RawProgramBinding{Register,Immediate,LoadStore}`) for the six RV64I branches
(BEQ/BNE/BLT/BGE/BLTU/BGEU) and the non-JALR control ops
(LUI/AUIPC/JAL/FENCE), with symbolic raw-word register and immediate fields.

  * BRANCHES (B-type word `rawBType`, `decode_b`) lower through
    `create_branch_op_typed`.  `neg` flips the two `j` offsets: the CONSTANT
    fall-through slot is `jmp_offset2` for the `neg = false` ops (BEQ/BLT/BLTU)
    and `jmp_offset1` for the `neg = true` ops (BNE/BGE/BGEU); the other slot
    is the signed decoded branch target.
  * LUI / AUIPC (U-type word `rawUType`, `decode_u`) lower through `lui` /
    `auipc`.  AUIPC's `store_pc = true` needs `rd ≠ 0` (the nop-guard disproof,
    matching `auipc_static_pins_full`); `jmp_offset1 = 4` and `jmp_offset2`
    carries the signed decoded immediate.
  * JAL (J-type word `rawJType`, `decode_j`) lowers through `jal`; `store_pc =
    true` needs `rd ≠ 0`.  `jmp_offset2 = 4` and `jmp_offset1` carries the
    signed decoded immediate.
  * JALR (I-type word `rawIType … 0x67`, `decode_i … false`) lowers through
    `jalr`, whose `i.imm % 4` TWO-ROW split makes `jmp_offset` a per-row
    disjunction; `Decode_jalr_of_program` pins NO jmp_offset, so the bridge
    threads only `op` / `flags` plus the genuine operand-side JALR witnesses
    (a/c masks, flag, offset bridge/even/no-wrap) as caller hypotheses.
  * FENCE (supported-FENCE word `rawSupportedFence`, `decode_fence`) lowers
    through `nop`; both jump slots are the constant fall-through (`= 4`).  The
    claim-side `fm = 0` / `rs = x0` / `rd = x0` are threaded as caller
    hypotheses (the FENCE defect scope, matching `Decode_fence_of_program`).

For each op `<op>` this module retains:
  * `transpile_<op>` — the REAL Aeneas pipeline `extract_transpile_rv64im_raw`
    reduces to the op's decode-field pins.
  * `<op>_decode_fields_of_binding` — the committed message's decode fields,
    from its raw word + the op-agnostic `romMessageOfRaw` binding.

The raw bundles feed architectural `ProgramDecode_<op>` constructors through
`ProgramRowsBinding` and `RawAtProgramStart`; JALR remains in its dedicated
two-row binding module.

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

attribute [local step] IScalar.sub_bv_spec I32.sub_bv_spec

private theorem hcast4' : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

private theorem store_reg_raw_index_pins_any
    (self z : zisk_inst_builder.ZiskInstBuilder) (rd : Std.U32)
    (hrd : rd.val < 32) (storePc : Bool)
    (hzero : self.i.store_offset = 0#i64) (hstore : self.i.store = 0#u64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self
      (UScalar.hcast IScalarTy.I64 rd) false storePc = ok z) :
    z.i.store_offset.val = rd.val ∧ z.i.store ≠ zisk_inst.STORE_IND := by
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
       constructor
       · scalar_tac
       · simp [hstore, zisk_inst.STORE_IND])
    | (rw [Result.ok.injEq] at h; subst h
       constructor
       · scalar_tac
       · simp [zisk_inst.STORE_REG, zisk_inst.STORE_IND])
    | (exfalso; scalar_tac)

private theorem store_reg_raw_index_iff_any
    (self z : zisk_inst_builder.ZiskInstBuilder) (rd : Std.U32)
    (hrd : rd.val < 32) (storePc : Bool)
    (hstore : self.i.store = 0#u64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self
      (UScalar.hcast IScalarTy.I64 rd) false storePc = ok z) :
    z.i.store = zisk_inst.STORE_REG ↔ rd.val ≠ 0 := by
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
       simp [hstore, zisk_inst.STORE_REG] ; scalar_tac)
    | (exfalso; scalar_tac)

private theorem src_a_imm_pres_store
    (self z : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_imm self v = ok z) :
    z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; rfl)

private theorem src_b_imm_pres_store
    (self z : zisk_inst_builder.ZiskInstBuilder) (v : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_imm self v = ok z) :
    z.i.store = self.i.store := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  first
  | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
     rw [Result.ok.injEq] at h; subst h; rfl)

private theorem nop_store_pin
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (instSize : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.nop self i instSize = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧ zib.i.store ≠ zisk_inst.STORE_REG := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.nop,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have hstore0 : z0.i.store = 0#u64 := by
    simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
      zisk_inst_builder.ZiskInstBuilder.new,
      zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
      zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
      bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h0
    rw [Result.ok.injEq] at h0
    subst z0
    rfl
  have hs1 := src_a_imm_pres_store z0 z1 _ h1
  have hs2 := src_b_imm_pres_store z1 z2 _ h2
  have hs3 := (op_zisk_pres_store z2 z3 _ h3).2
  have hs4 := (j_pres_store z3 z4 _ _ h4).2
  have hz5 := ZiskFv.Compliance.Extraction.build_eq z4 z5 h5
  refine ⟨z5, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h6, ?_⟩
  rw [hz5, hs4, hs3, hs2, hs1, hstore0]
  norm_num [zisk_inst.STORE_REG]

private theorem lui_store_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (instSize : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.lui self i instSize = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.store_offset.val = i.rd.val ∧ zib.i.store ≠ zisk_inst.STORE_IND ∧
      (zib.i.store = zisk_inst.STORE_REG ↔ i.rd.val ≠ 0) := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.lui,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    UScalar.hcast, IScalar.hcast, lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    ZiskFv.Compliance.Extraction.i32_32_nonnegative,
    ZiskFv.Compliance.Extraction.i32_32_toNat_lt_u64_numBits,
    bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  obtain ⟨zib, hstore, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨hso, hsi⟩ :=
    store_reg_raw_index_pins_any _ _ i.rd hrd false (by rfl) (by rfl) hstore
  have hsr := store_reg_raw_index_iff_any _ _ i.rd hrd false (by rfl) hstore
  rw [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, by simpa using hso, by simpa using hsi, by simpa using hsr⟩

private theorem auipc_store_jmp_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.auipc self i = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.store_offset.val = i.rd.val ∧ zib.i.store ≠ zisk_inst.STORE_IND ∧
      (zib.i.store = zisk_inst.STORE_REG ↔ i.rd.val ≠ 0) ∧
      zib.i.jmp_offset2 = IScalar.cast IScalarTy.I64 i.imm := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.auipc,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    ZiskFv.Compliance.Extraction.i32_32_nonnegative,
    ZiskFv.Compliance.Extraction.i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨zib, hstore, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨hso, hsi⟩ :=
    store_reg_raw_index_pins_any _ _ i.rd hrd true (by rfl) (by rfl) hstore
  have hsr := store_reg_raw_index_iff_any _ _ i.rd hrd true (by rfl) hstore
  rw [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, by simpa using hso, by simpa using hsi, by simpa using hsr, rfl⟩

private theorem jal_store_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (instSize : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrd : i.rd.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.jal self i instSize = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.store_offset.val = i.rd.val ∧ zib.i.store ≠ zisk_inst.STORE_IND ∧
      (zib.i.store = zisk_inst.STORE_REG ↔ i.rd.val ≠ 0) := by
  simp only [
    riscv2zisk_context.Riscv2ZiskContext.jal,
    zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
    zisk_inst_builder.ZiskInstBuilder.new,
    zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_ops.ZiskOp.op_type, zisk_ops.ZiskOp.code,
    zisk_ops.ZiskOp.input_size, zisk_ops.ZiskOp.is_m32,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    zisk_inst_builder.ZiskInstBuilder.store_pc_reg,
    zisk_inst_builder.ZiskInstBuilder.j,
    zisk_inst_builder.ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    lift, reduceIte,
    HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight,
    ZiskFv.Compliance.Extraction.i32_32_nonnegative,
    ZiskFv.Compliance.Extraction.i32_32_toNat_lt_u64_numBits,
    bind_ok, Bind.bind] at h
  obtain ⟨zib, hstore, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨hso, hsi⟩ :=
    store_reg_raw_index_pins_any _ _ i.rd hrd true (by rfl) (by rfl) hstore
  have hsr := store_reg_raw_index_iff_any _ _ i.rd hrd true (by rfl) hstore
  rw [Result.ok.injEq] at h
  subst h
  exact ⟨_, rfl, by simpa using hso, by simpa using hsi, by simpa using hsr⟩

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

private theorem decode_u_rawUType_imm
    (imm : BitVec 20) (rd opcode : Nat)
    (hrd : rd < 32) (hopcode : opcode < 128)
    (rop : RiscvOpcode) (d : DecodedRv64im)
    (hd : decode_u (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType
      (imm ++ (0 : BitVec 12)).toNat rd opcode)) rop = ok d) :
    (IScalar.hcast UScalarTy.U64 d.imm).bv =
      BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  simp only [decode_u, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨_i1, _, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i2, hi2, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i3, hi3, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  rw [Result.ok.injEq] at hd
  rw [← hd]
  have hi2bv : i2.bv =
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType
        (imm ++ (0 : BitVec 12)).toNat rd opcode) &&& 4294963200#u32).bv >>> 12 := by
    rw [show ((toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType
        (imm ++ (0 : BitVec 12)).toNat rd opcode) &&& 4294963200#u32) >>> 12#i32 :
      Result Std.U32) = ok ⟨(toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType
        (imm ++ (0 : BitVec 12)).toNat rd opcode) &&& 4294963200#u32).bv >>> 12⟩
      from rfl, Result.ok.injEq] at hi2
    exact (congrArg UScalar.bv hi2).symm
  have hi3bv : i3.bv = i2.bv <<< 12 := by
    rw [show (i2 <<< 12#i32 : Result Std.U32) = ok ⟨i2.bv <<< 12⟩ from rfl,
      Result.ok.injEq] at hi3
    exact (congrArg UScalar.bv hi3).symm
  change BitVec.signExtend 64 i3.bv =
    BitVec.signExtend 64 (imm ++ (0 : BitVec 12))
  rw [hi3bv, hi2bv]
  congr 1
  simp only [toU32, ZiskFv.Completeness.Rv64imShapes.rawUType,
    ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  have hlow (k : Nat) (hk : k < 12) :
      (imm ++ (0 : BitVec 12)).getLsbD k = false := by
    rw [BitVec.getLsbD_append, if_pos hk]
    simp
  have hrdBit (k : Nat) (hk : 5 ≤ k) : rd.testBit k = false :=
    ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) hk
  have hopBit (k : Nat) (hk : 7 ≤ k) : opcode.testBit k = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) hk
  have hrdHigh (k : Nat) (hk : 12 ≤ k) :
      (BitVec.ofNat 32 (rd <<< 7)).getLsbD k = false := by
    simp [BitVec.getLsbD_ofNat, Nat.testBit_shiftLeft, hk,
      hrdBit (k - 7) (by omega)]
  have hopHigh (k : Nat) (hk : 12 ≤ k) :
      (BitVec.ofNat 32 opcode).getLsbD k = false := by
    simp [BitVec.getLsbD_ofNat, hopBit k (by omega)]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 32
  · by_cases hk12 : k < 12
    · interval_cases k <;>
        simp [hlow, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit] <;>
        first
        | (have hz := hlow _ (by omega)
           simpa only [BitVec.getLsbD_eq_getElem (by omega)] using hz)
    · interval_cases k <;>
        simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_and, BitVec.getLsbD_ofNat, BitVec.getLsbD_append,
          Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
          Nat.testBit_mod_two_pow, Nat.testBit, hrdBit, hopBit] <;>
        first
        | (rw [show (BitVec.ofNat 32 (rd <<< 7))[_] = false by
                 rw [← BitVec.getLsbD_eq_getElem (by omega)]
                 exact hrdHigh _ (by omega),
               show (BitVec.ofNat 32 opcode)[_] = false by
                 rw [← BitVec.getLsbD_eq_getElem (by omega)]
                 exact hopHigh _ (by omega)]
           simp)
  · simp [BitVec.getLsbD, hk]

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

private theorem rawIType_rd (imm rs1 funct3 rd opcode : Nat) (hrd : rd < 32) (_hf3 : funct3 < 8)
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
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]; rfl

/-! ## Generic branch-family transpile reduction (B-type word, `decode_b`).

`create_branch_op_typed` writes only `rs1` / `rs2` (no `rd`); the constant
fall-through jump slot is `jmp_offset2` for `neg = false`, `jmp_offset1` for
`neg = true`. -/

private theorem branch_dynamic_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (instSize : Std.U64)
    (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
      self i op neg instSize = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      (neg = false →
        zib.i.jmp_offset1 = IScalar.cast IScalarTy.I64 i.imm ∧
        zib.i.jmp_offset2 = UScalar.hcast IScalarTy.I64 instSize) ∧
      (neg = true →
        zib.i.jmp_offset1 = UScalar.hcast IScalarTy.I64 instSize ∧
        zib.i.jmp_offset2 = IScalar.cast IScalarTy.I64 i.imm) := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨zib0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zib1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zib2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zib3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zib4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨zib5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨s1, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have hb := ZiskFv.Compliance.Extraction.build_eq _ _ h5
  split_ifs at h4 with hcond
  · obtain ⟨hj1, hj2⟩ := ZiskFv.Compliance.Extraction.j_jmp _ _ _ _ h4
    refine ⟨zib5, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h6, ?_, ?_⟩
    · intro hf
      rw [hcond] at hf
      contradiction
    · intro _
      constructor <;> rw [hb] <;> assumption
  · obtain ⟨hj1, hj2⟩ := ZiskFv.Compliance.Extraction.j_jmp _ _ _ _ h4
    refine ⟨zib5, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h6, ?_, ?_⟩
    · intro _
      constructor <;> rw [hb] <;> assumption
    · intro ht
      exact absurd ht hcond

theorem create_branch_op_typed_source_store_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (neg : Bool) (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrs1 : i.rs1.val < 32) (hrs2 : i.rs2.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed
      self i op neg inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧ zib.i.store ≠ zisk_inst.STORE_REG ∧
      zib.i.a_src = (if i.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      zib.i.a_offset_imm0.val = i.rs1.val ∧ zib.i.a_use_sp_imm1 = 0#u64 ∧
      zib.i.b_src = (if i.rs2.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      zib.i.b_offset_imm0.val = i.rs2.val ∧ zib.i.b_use_sp_imm1 = 0#u64 := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_branch_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have hcast1 := ZiskFv.Compliance.Extraction.cast_u32_u64_val i.rs1
  have hcast2 := ZiskFv.Compliance.Extraction.cast_u32_u64_val i.rs2
  have ha : z1.i.a_src = (if i.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      z1.i.a_offset_imm0.val = i.rs1.val ∧ z1.i.a_use_sp_imm1 = 0#u64 := by
    by_cases hz : i.rs1.val = 0
    · have hc : UScalar.cast UScalarTy.U64 i.rs1 = 0#u64 :=
        UScalar.eq_of_val_eq (hcast1.trans hz)
      obtain ⟨hs, ho, hu⟩ := src_a_reg_zero_pins z0 z1 false (by simpa [hc] using h1)
      simp only [if_pos hz]
      exact ⟨hs, by rw [ho]; norm_num; exact hz.symm, hu⟩
    · have hcne : UScalar.cast UScalarTy.U64 i.rs1 ≠ 0#u64 := by
        intro heq; apply hz
        have hv := congrArg UScalar.val heq
        simpa [hcast1] using hv
      obtain ⟨hs, ho⟩ := ZiskFv.Compliance.Extraction.src_a_reg_src_eq z0 z1 _ false
        hcne h1
        (by
          simp only [zisk_registers.REGS_IN_MAIN_FROM]
          change ¬(UScalar.cast UScalarTy.U64 i.rs1).val <
            (UScalar.cast UScalarTy.U64 1#usize).val
          rw [hcast1]; norm_num; omega)
        (by
          simp only [zisk_registers.REGS_IN_MAIN_TO]
          change ¬(UScalar.cast UScalarTy.U64 i.rs1).val >
            (UScalar.cast UScalarTy.U64 31#usize).val
          rw [hcast1]; norm_num; omega)
      simp only [if_neg hz]
      exact ⟨hs, by rw [ho, hcast1], src_a_reg_false_use_sp_zero z0 z1 _ h1⟩
  have hb : z2.i.b_src = (if i.rs2.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      z2.i.b_offset_imm0.val = i.rs2.val ∧ z2.i.b_use_sp_imm1 = 0#u64 := by
    by_cases hz : i.rs2.val = 0
    · have hc : UScalar.cast UScalarTy.U64 i.rs2 = 0#u64 :=
        UScalar.eq_of_val_eq (hcast2.trans hz)
      obtain ⟨hs, ho, hu⟩ := src_b_reg_zero_pins z1 z2 false (by simpa [hc] using h2)
      simp only [if_pos hz]
      exact ⟨hs, by rw [ho]; norm_num; exact hz.symm, hu⟩
    · have hcne : UScalar.cast UScalarTy.U64 i.rs2 ≠ 0#u64 := by
        intro heq; apply hz
        have hv := congrArg UScalar.val heq
        simpa [hcast2] using hv
      obtain ⟨hs, ho, _, _⟩ := ZiskFv.Compliance.Extraction.src_b_reg_src_eq z1 z2 _ false
        hcne h2
        (by
          simp only [zisk_registers.REGS_IN_MAIN_FROM]
          change ¬(UScalar.cast UScalarTy.U64 i.rs2).val <
            (UScalar.cast UScalarTy.U64 1#usize).val
          rw [hcast2]; norm_num; omega)
        (by
          simp only [zisk_registers.REGS_IN_MAIN_TO]
          change ¬(UScalar.cast UScalarTy.U64 i.rs2).val >
            (UScalar.cast UScalarTy.U64 31#usize).val
          rw [hcast2]; norm_num; omega)
      simp only [if_neg hz]
      exact ⟨hs, by rw [ho, hcast2], src_b_reg_false_use_sp_zero z1 z2 _ h2⟩
  obtain ⟨hba, hbao⟩ := ZiskFv.Compliance.Extraction.src_b_reg_a_pres z1 z2 _ false h2
  have hbau := src_b_reg_a_use_sp_pres z1 z2 _ false h2
  obtain ⟨hoa, hoao, hob, hobo⟩ := ZiskFv.Compliance.Extraction.op_zisk_src_pres z2 z3 op h3
  obtain ⟨houa, houb⟩ := op_zisk_use_sp_pres z2 z3 op h3
  have hjSrc : z4.i.a_src = z3.i.a_src ∧ z4.i.a_offset_imm0 = z3.i.a_offset_imm0 ∧
      z4.i.b_src = z3.i.b_src ∧ z4.i.b_offset_imm0 = z3.i.b_offset_imm0 ∧
      z4.i.a_use_sp_imm1 = z3.i.a_use_sp_imm1 ∧ z4.i.b_use_sp_imm1 = z3.i.b_use_sp_imm1 := by
    split_ifs at h4
    all_goals
      obtain ⟨hja, hjao, hjb, hjbo⟩ := ZiskFv.Compliance.Extraction.j_src_pres z3 _ _ z4 h4
      obtain ⟨hjua, hjub⟩ := j_use_sp_pres z3 z4 _ _ h4
      exact ⟨hja, hjao, hjb, hjbo, hjua, hjub⟩
  obtain ⟨hda, hdao, hdb, hdbo⟩ := ZiskFv.Compliance.Extraction.build_src_pres z4 z5 h5
  obtain ⟨hdua, hdub⟩ := build_use_sp_pres z4 z5 h5
  have hstore0 : z0.i.store = 0#u64 := by
    simp only [zisk_inst_builder.ZiskInstBuilder.new_for_rv64im_lowering,
      zisk_inst_builder.ZiskInstBuilder.new,
      zisk_inst_builder.ZiskInstBuilder.Insts.CoreDefaultDefault.default,
      zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
      bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h0
    rw [Result.ok.injEq] at h0
    subst z0
    rfl
  obtain ⟨_, hs1⟩ := src_a_reg_pres_store z0 z1 _ _ h1
  obtain ⟨_, hs2⟩ := src_b_reg_pres_store z1 z2 _ _ h2
  obtain ⟨_, hs3⟩ := op_zisk_pres_store z2 z3 _ h3
  have hs4 : z4.i.store = z3.i.store := by
    split_ifs at h4 <;> exact (j_pres_store z3 z4 _ _ h4).2
  have hz5 := ZiskFv.Compliance.Extraction.build_eq z4 z5 h5
  refine ⟨z5, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h6, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hz5, hs4, hs3, hs2, hs1, hstore0]
    norm_num [zisk_inst.STORE_REG]
  · rw [hda, hjSrc.1, hoa, hba]; exact ha.1
  · rw [hdao, hjSrc.2.1, hoao, hbao]; exact ha.2.1
  · rw [hdua, hjSrc.2.2.2.2.1, houa, hbau]; exact ha.2.2
  · rw [hdb, hjSrc.2.2.1, hob]; exact hb.1
  · rw [hdbo, hjSrc.2.2.2.1, hobo]; exact hb.2.1
  · rw [hdub, hjSrc.2.2.2.2.2, houb]; exact hb.2.2

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
      ∧ ext.row.store ≠ zisk_inst.STORE_REG
      ∧ (neg = false → ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
      ∧ (neg = true  → ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
      ∧ ∃ d, decode_b raw rop = ok d
        ∧ ext.row.a_src = (if d.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
        ∧ ext.row.a_offset_imm0.val = d.rs1.val ∧ ext.row.a_use_sp_imm1 = 0#u64
        ∧ ext.row.b_src = (if d.rs2.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
        ∧ ext.row.b_offset_imm0.val = d.rs2.val ∧ ext.row.b_use_sp_imm1 = 0#u64
        ∧ (neg = false → ext.row.jmp_offset1 = IScalar.cast IScalarTy.I64 d.imm)
        ∧ (neg = true → ext.row.jmp_offset2 = IScalar.cast IScalarTy.I64 d.imm) := by
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
    branch_dynamic_pins
      { defCtx with extract_marker := () } input op neg 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hjf hjt
  obtain ⟨zibSrc, hzibSrc, hstore, haSrc, haOff, haUse, hbSrc, hbOff, hbUse⟩ :=
    create_branch_op_typed_source_store_pins { defCtx with extract_marker := () }
      input op neg 4#u64 ctx0 (by rw [hinput]; exact hrs1b)
      (by rw [hinput]; exact hrs2b) hctx0
  have hzzSrc : zibSrc = zib := Option.some.inj (hzibSrc.symm.trans hzib)
  rw [hzzSrc] at hstore haSrc haOff haUse hbSrc hbOff hbUse
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  obtain ⟨row', hrow', hraSrc, hraUse, hraOff, hrbSrc, hrbUse, hrbOff,
      _, _, hrStore, _, _, _, _, _, _⟩ :=
    ZiskFv.Compliance.Extraction.from_inst_full_fields zib.i
  have hrowEq : row' = row := Result.ok.inj (hrow'.symm.trans hrow)
  subst row'
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm defCtx input, hctx0]; rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [hrStore]; exact hstore
  · intro hf; show row.jmp_offset2 = _; rw [hrj2]; exact (hjf hf).2
  · intro ht; show row.jmp_offset1 = _; rw [hrj1]; exact (hjt ht).1
  · refine ⟨decoded, hdecoded, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hraSrc, haSrc, hinput]
    · rw [hraOff, haOff, hinput]
    · rw [hraUse, haUse]
    · rw [hrbSrc, hbSrc, hinput]
    · rw [hrbOff, hbOff, hinput]
    · rw [hrbUse, hbUse]
    · intro hf
      show row.jmp_offset1 = _
      rw [hrj1, (hjf hf).1, hinput]
    · intro ht
      show row.jmp_offset2 = _
      rw [hrj2, (hjt ht).2, hinput]

/-! ## Branch decode-field bridges (one constant jump slot, op, flags). -/

/-- `neg = false` branch (BEQ/BLT/BLTU): the committed message's `op` /
`jmp_offset2` / `flags`, from its raw word binding. -/
theorem branch_decode_fields_false
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset2 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4; rw [hj2]; norm_num [hcast4']
  · rw [hmsg]; rfl

/-- `neg = true` branch (BNE/BGE/BGEU): the committed message's `op` /
`jmp_offset1` / `flags`, from its raw word binding. -/
theorem branch_decode_fields_true
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4; rw [hj1]; norm_num [hcast4']
  · rw [hmsg]; rfl

/-- The committed message's opcode, both fall-through offsets, and flags. -/
theorem jump_decode_fields_of_binding
    (line : FGL) (msg : ZiskRomMessage FGL) (raw : BitVec 32)
    (opc : Std.U8) (opF : FGL) (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hopF : romOpcode opc = opF)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hop : ext.row.op = opc)
    (hj1 : ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64)
    (hj2 : ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64)
    (hbind : msg = romMessageOfRaw line raw) :
    msg.op = opF ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmsg]; show romOpcode ext.row.op = opF; rw [hop, hopF]
  · rw [hmsg]; show (ext.row.jmp_offset1.val : FGL) = 4; rw [hj1]; norm_num [hcast4']
  · rw [hmsg]; show (ext.row.jmp_offset2.val : FGL) = 4; rw [hj2]; norm_num [hcast4']
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
  let t1 ← `(theorem $tName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.store ≠ zisk_inst.STORE_REG
          ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ∃ d, decode_b
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3))
                $rop = ok d
            ∧ ext.row.a_src = (if d.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
            ∧ ext.row.a_offset_imm0.val = d.rs1.val ∧ ext.row.a_use_sp_imm1 = 0#u64
            ∧ ext.row.b_src = (if d.rs2.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
            ∧ ext.row.b_offset_imm0.val = d.rs2.val ∧ ext.row.b_use_sp_imm1 = 0#u64
            ∧ ext.row.jmp_offset1 = IScalar.cast IScalarTy.I64 d.imm := by
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
      obtain ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hstore, hjf, _, d, hd,
          haSrc, haOff, haUse, hbSrc, hbOff, hbUse, htarget, _⟩ :=
        transpile_branch_of _ $rop $srop $op false $opU8 hdec rfl (by intro self input; rfl) rfl rfl rfl
      exact ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hstore, hjf rfl, d, hd,
        haSrc, haOff, haUse, hbSrc, hbOff, hbUse, htarget rfl⟩)
  let t2 ← `(theorem $dfName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) :
        msg.op = $opc ∧ msg.jmp_offset2 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, _, hj2, _⟩ :=
        $tName rs1 rs2 imm hrs1 hrs2
      obtain ⟨ho, hjo2, hf⟩ :=
        branch_decode_fields_false line msg _ $opU8 $opc ext
          (by simp [romOpcode, $opc:term]) hok hop hj2 hbind
      exact ⟨ho, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

/-- macro (neg = true branch: BNE/BGE/BGEU; constant slot `jmp_offset1`). -/
local macro "branch_true_op" nm:ident "," f3:term "," rop:term "," srop:term ","
    op:term "," opU8:term "," opc:ident : command => do
  let s := nm.getId.toString
  let tName := Lean.mkIdent (Lean.Name.mkSimple ("transpile_" ++ s))
  let dfName := Lean.mkIdent (Lean.Name.mkSimple (s ++ "_decode_fields_of_binding"))
  let t1 ← `(theorem $tName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32) :
        ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
          ∧ ext.row.op = $opU8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ ext.row.store ≠ zisk_inst.STORE_REG
          ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
          ∧ ∃ d, decode_b
              (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3))
                $rop = ok d
            ∧ ext.row.a_src = (if d.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
            ∧ ext.row.a_offset_imm0.val = d.rs1.val ∧ ext.row.a_use_sp_imm1 = 0#u64
            ∧ ext.row.b_src = (if d.rs2.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
            ∧ ext.row.b_offset_imm0.val = d.rs2.val ∧ ext.row.b_use_sp_imm1 = 0#u64
            ∧ ext.row.jmp_offset2 = IScalar.cast IScalarTy.I64 d.imm := by
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
      obtain ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hstore, _, hjt, d, hd,
          haSrc, haOff, haUse, hbSrc, hbOff, hbUse, _, htarget⟩ :=
        transpile_branch_of _ $rop $srop $op true $opU8 hdec rfl (by intro self input; rfl) rfl rfl rfl
      exact ⟨ext, hok, hop, hieo, hm32, hsp, hstp, hstore, hjt rfl, d, hd,
        haSrc, haOff, haUse, hbSrc, hbOff, hbUse, htarget rfl⟩)
  let t2 ← `(theorem $dfName (rs1 rs2 imm : Nat) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
        (line : FGL) (msg : ZiskRomMessage FGL)
        (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) :
        msg.op = $opc ∧ msg.jmp_offset1 = 4
          ∧ ∃ ext, extract_transpile_rv64im_raw
                (toU32 (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3)) = ok ext
              ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
              ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
              ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
      obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, _, hj1, _⟩ :=
        $tName rs1 rs2 imm hrs1 hrs2
      obtain ⟨ho, hjo1, hf⟩ :=
        branch_decode_fields_true line msg _ $opU8 $opc ext
          (by simp [romOpcode, $opc:term]) hok hop hj1 hbind
      exact ⟨ho, hjo1, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩)
  return ⟨Lean.mkNullNode #[t1, t2]⟩

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
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0) := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37))
      = aeneas_extract.rv64im_decode.decode_u
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) RiscvOpcode.Lui := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawUType_opcode imm rd 0x37 (by norm_num)]
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrdbv⟩ :=
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
  obtain ⟨zibS, hzibS, hstoreOffset, hstoreInd, hstoreReg⟩ :=
    lui_store_pins { defCtx with extract_marker := () } input 4#u64 ctx0
      (by rw [hinput]; exact hrdb) hctx0
  have hzzS : zibS = zib := Option.some.inj (hzibS.symm.trans hzib)
  rw [hzzS] at hstoreOffset hstoreInd hstoreReg
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
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · show row.store_offset.val = rd
    rw [hrStoreOffset, hstoreOffset, hinput]
    exact_mod_cast (show decoded.rd.val = rd by
      change decoded.rd.bv.toNat = rd
      rw [hrdbv]
      change (((ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37) &&&
        3968#32) >>> 7).toNat = rd
      rw [rawUType_rd imm rd 0x37 hrd (by norm_num), BitVec.toNat_ofNat]
      omega)
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]
    exact hstoreInd
  · have hrdval : decoded.rd.val = rd := by
      change decoded.rd.bv.toNat = rd
      rw [hrdbv]
      change (((ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37) &&&
        3968#32) >>> 7).toNat = rd
      rw [rawUType_rd imm rd 0x37 hrd (by norm_num), BitVec.toNat_ofNat]
      omega
    rw [hrStore, hstoreReg, hinput, hrdval]

theorem lui_decode_fields_of_binding (rd imm : Nat) (hrd : rd < 32)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) :
    msg.op = OP_COPYB ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, _⟩ :=
    transpile_lui rd imm hrd
  obtain ⟨ho, hjo1, hjo2, hmso, _, hf⟩ :=
    register_decode_fields_of_binding line msg _ 1#u8 OP_COPYB rd ext
      (by simp [romOpcode, OP_COPYB]) hok hop hj1 hj2 hso hsi hbind
  exact ⟨ho, hjo1, hjo2, hmso, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

/-! ## AUIPC (U-type word, `decode_u` → `auipc` → `OP_FLAG`, `store_pc = true`).
The constant slot is `jmp_offset1 = 4` (`= 4#i64`, defeq `hcast 4#u64`); the
`store_pc = true` needs `rd ≠ 0`.  jmp_offset2 is the imm target (skipped). -/

theorem transpile_auipc (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) = ok ext
      ∧ ext.row.op = 0#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ∃ d, decode_u
          (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17))
            RiscvOpcode.Auipc = ok d
        ∧ ext.row.jmp_offset2 = IScalar.cast IScalarTy.I64 d.imm := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17))
      = aeneas_extract.rv64im_decode.decode_u
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) RiscvOpcode.Auipc := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawUType_opcode imm rd 0x17 (by norm_num)]
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
  obtain ⟨zibS, hzibS, hstoreOffset, hstoreInd, hstoreReg, hj2⟩ :=
    auipc_store_jmp_pins { defCtx with extract_marker := () } input ctx0
      (by rw [hinput]; exact hrdb) hctx0
  have hzzS : zibS = zib := Option.some.inj (hzibS.symm.trans hzib)
  rw [hzzS] at hstoreOffset hstoreInd hstoreReg hj2
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
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · show row.store_offset.val = rd
    rw [hrStoreOffset, hstoreOffset, hinput]
    exact_mod_cast (show decoded.rd.val = rd by
      change decoded.rd.bv.toNat = rd
      rw [hrdbv]
      change (((ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17) &&&
        3968#32) >>> 7).toNat = rd
      rw [rawUType_rd imm rd 0x17 hrd (by norm_num), BitVec.toNat_ofNat]
      omega)
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]
    exact hstoreInd
  · have hrdval : decoded.rd.val = rd := by
      change decoded.rd.bv.toNat = rd
      rw [hrdbv]
      change (((ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17) &&&
        3968#32) >>> 7).toNat = rd
      rw [rawUType_rd imm rd 0x17 hrd (by norm_num), BitVec.toNat_ofNat]
      omega
    rw [hrStore, hstoreReg, hinput, hrdval]
  · refine ⟨decoded, hdecoded, ?_⟩
    rw [hrj2, hj2, hinput]

theorem auipc_decode_fields_of_binding (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) :
    msg.op = OP_FLAG ∧ msg.jmp_offset1 = 4
      ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hso, hsi, hdyn⟩ :=
    transpile_auipc rd imm hrd hrd0
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ext, hok, hieo, hm32, hsetpc, hstorepc, ?_⟩
  · rw [hmsg]
    show romOpcode ext.row.op = OP_FLAG
    rw [hop]
    simp [romOpcode, OP_FLAG]
  · rw [hmsg]
    show (ext.row.jmp_offset1.val : FGL) = 4
    rw [hj1]
    norm_num [hcast4']
  · rw [hmsg]
    show (ext.row.store_offset.val : FGL) = (rd : FGL)
    rw [hso]
    norm_num
  · rw [hmsg]
    rfl

/-! ## JAL (J-type word, `decode_j` → `jal` → `OP_FLAG`, `store_pc = true`).
Constant slot `jmp_offset2 = 4`; `store_pc = true` needs `rd ≠ 0`.  jmp_offset1
is the imm target (skipped). -/

theorem transpile_jal (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) = ok ext
      ∧ ext.row.op = 0#u8 ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store_offset.val = rd
      ∧ ext.row.store ≠ zisk_inst.STORE_IND
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
      ∧ ∃ d, decode_j
          (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd))
            RiscvOpcode.Jal = ok d
        ∧ ext.row.jmp_offset1 = IScalar.cast IScalarTy.I64 d.imm := by
  have hdec : aeneas_extract.rv64im_decode.decode_32_core
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd))
      = aeneas_extract.rv64im_decode.decode_j
        (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) RiscvOpcode.Jal := by
    simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawJType_opcode imm rd]
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
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    ZiskFv.Compliance.Extraction.jal_dynamic_pins { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨zibS, hzibS, hstoreOffset, hstoreInd, hstoreReg⟩ :=
    jal_store_pins { defCtx with extract_marker := () } input 4#u64 ctx0
      (by rw [hinput]; exact hrdb) hctx0
  have hzzS : zibS = zib := Option.some.inj (hzibS.symm.trans hzib)
  rw [hzzS] at hstoreOffset hstoreInd hstoreReg
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
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · show row.store_offset.val = rd
    rw [hrStoreOffset, hstoreOffset, hinput]
    exact_mod_cast (show decoded.rd.val = rd by
      change decoded.rd.bv.toNat = rd
      rw [hrdbv]
      change (((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
        3968#32) >>> 7).toNat = rd
      rw [rawJType_rd imm rd hrd, BitVec.toNat_ofNat]
      omega)
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]
    exact hstoreInd
  · have hrdval : decoded.rd.val = rd := by
      change decoded.rd.bv.toNat = rd
      rw [hrdbv]
      change (((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
        3968#32) >>> 7).toNat = rd
      rw [rawJType_rd imm rd hrd, BitVec.toNat_ofNat]
      omega
    rw [hrStore, hstoreReg, hinput, hrdval]
  · refine ⟨decoded, hdecoded, ?_⟩
    show row.jmp_offset1 = _
    rw [hrj1, hj1, hinput]

theorem jal_decode_fields_of_binding (rd imm : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) :
    msg.op = OP_FLAG ∧ msg.jmp_offset2 = 4 ∧ msg.store_offset = (rd : FGL)
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = true
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj2, hso, hsi, _⟩ :=
    transpile_jal rd imm hrd hrd0
  have hmsg : msg = serializeExtract line ext.row := by
    rw [hbind, romMessageOfRaw, hok]
    exact romRowOf_eq_serializeExtract line ext.row
  refine ⟨?_, ?_, ?_, ext, hok, hieo, hm32, hsetpc, hstorepc, ?_⟩
  · rw [hmsg]
    show romOpcode ext.row.op = OP_FLAG
    rw [hop]
    simp [romOpcode, OP_FLAG]
  · rw [hmsg]
    show (ext.row.jmp_offset2.val : FGL) = 4
    rw [hj2]
    norm_num [hcast4']
  · rw [hmsg]
    show (ext.row.store_offset.val : FGL) = (rd : FGL)
    rw [hso]
    norm_num
  · rw [hmsg]
    rfl

/-! ## JALR (I-type word `… 0x67`, `decode_i … false` → `jalr` → `OP_AND`,
`set_pc = true`, `store_pc = true`).  The `i.imm % 4` TWO-ROW split is handled in
`jalr_ok`; `Decode_jalr_of_program` pins NO jmp_offset, so the bridge threads only
`op` / `flags`, plus the genuine operand-side JALR witnesses (`flag` / a-mask /
c-mask / offset bridge / even / no-wrap) as caller hypotheses. -/

theorem transpile_jalr (rd rs1 imm : Nat) (hrd : rd < 32) (_hrs1 : rs1 < 32) (hrd0 : rd ≠ 0) :
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
  obtain ⟨decoded, hdecoded, hopd, hrdb, hrs1b, hrdbv⟩ :=
    decode_i_bounds (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) RiscvOpcode.Jalr false
  have hdec0 : aeneas_extract.rv64im_decode.decode_32_core
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) = ok decoded := hdec.trans hdecoded
  set input : riscv2zisk_single_row.Rv64imLoweringInput :=
    { rom_address := 0#u64, rd := decoded.rd, rs1 := decoded.rs1, rs2 := decoded.rs2, imm := decoded.imm }
    with hinput
  have hbveq : decoded.rd.bv = BitVec.ofNat 32 rd := by
    rw [hrdbv.1]
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

theorem jalr_decode_fields_of_binding
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line
      (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) :
    msg.op = OP_AND
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawIType imm rs1 0 rd 0x67)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = true ∧ ext.row.store_pc = true
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc⟩ :=
    transpile_jalr rd rs1 imm hrd hrs1 hrd0
  obtain ⟨ho, hf⟩ :=
    op_flags_of_binding line msg _ 14#u8 OP_AND ext
      (by simp [romOpcode, OP_AND]) hok hop hbind
  exact ⟨ho, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

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
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.store ≠ zisk_inst.STORE_REG := by
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
  obtain ⟨zibS, hzibS, hstoreReg⟩ :=
    nop_store_pin { defCtx with extract_marker := () } input 4#u64 ctx0 hctx0
  have hzzS : zibS = zib := Option.some.inj (hzibS.symm.trans hzib)
  rw [hzzS] at hstoreReg
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
  have hrStore : row.store = zib.i.store := by
    rw [aeneas_extract.ZiskInstExtract.from_inst] at hrow
    obtain ⟨i2, hi2, hrow⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hrow
    rw [Result.ok.injEq] at hrow
    subst row
    rfl
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [hrStore]
    exact hstoreReg

theorem fence_decode_fields_of_binding
    (pred succ : Nat) (hp : pred < 16) (hs : succ < 16)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line
      (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ)) :
    msg.op = OP_FLAG ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw
            (toU32 (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ)) = ok ext
          ∧ ext.row.is_external_op = false ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, _⟩ :=
    transpile_fence pred succ hp hs
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    jump_decode_fields_of_binding line msg _ 0#u8 OP_FLAG ext
      (by simp [romOpcode, OP_FLAG]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

/-! ## Current `ProgramDecode` retarget: U-type controls and FENCE. -/

private theorem primary_row_non_jalr_control {n rawLength : Nat}
    {trace : ZiskFv.Compliance.AcceptedZiskTrace n}
    {start : Fin rawLength → Fin trace.programLength}
    {addr : Fin rawLength → FGL} {rawProgram : Fin rawLength → BitVec 32}
    {j : Fin trace.programLength} {line : FGL} {raw : BitVec 32}
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (hlookup : RawAtProgramStart start addr rawProgram j line raw)
    (ext : zisk_core.aeneas_extract.Rv64imTranspileExtract)
    (hok : extract_transpile_rv64im_raw (toU32 raw) = ok ext)
    (hnon : (toU32 raw &&& 127#u32) ≠ 103#u32) :
    trace.program j = romMessageOfRaw line raw := by
  calc
    trace.program j = (romMessagesOfRaw line raw).1 :=
      primary_row_of_programRowsBinding hbind hlookup
    _ = romMessageOfRaw line raw :=
      romMessagesOfRaw_fst_of_non_jalr line raw ext hok hnon

structure RawProgramDecode_lui {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_lui trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_imm_lo_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_0 i.val).val
      = (c.imm ++ (0 : BitVec 12)).toNat
  h_imm_hi_nat :
    ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).b_1 i.val).val
      = (BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toNat / 4294967296
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      RawAtProgramStart start addr rawProgram j (trace.program j).line
        (ZiskFv.Completeness.Rv64imShapes.rawUType
          (c.imm ++ (0 : BitVec 12)).toNat (regidx_to_fin c.rd).val 0x37)

noncomputable def ProgramDecode_lui_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_lui trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_lui trace i c start addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_lui trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let imm := (c.imm ++ (0 : BitVec 12)).toNat
  let ext := (transpile_lui rd imm (regidx_to_fin c.rd).isLt).choose
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2, hso, hsi, hstoreReg⟩ :=
    (transpile_lui rd imm (regidx_to_fin c.rd).isLt).choose_spec
  refine
    { h_idx := rawDecode.h_idx
      h_imm_lo_nat := rawDecode.h_imm_lo_nat
      h_imm_hi_nat := rawDecode.h_imm_hi_nat
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hsi
      h_bits_store_reg := by
        exact storeBit_of_store_iff_val ext.row (regidx_to_fin c.rd)
          (by simpa only [ext, rd] using hstoreReg)
      h_prog := by
        intro j hline
        obtain ⟨k, hstart, haddr, hraw⟩ := rawDecode.hLine j hline
        have hbk : trace.program j = romMessageOfRaw (addr k)
            (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x37) := by
          apply primary_row_non_jalr_control hbind ⟨k, hstart, rfl, hraw⟩ ext
          · simpa only [imm, rd, ext] using hok
          · rw [ZiskFv.Compliance.Decode.toU32_and127,
              ZiskFv.Compliance.Decode.rawUType_opcode imm rd 0x37 (by norm_num)]
            decide
        obtain ⟨ho, hjo1, hjo2, hs, ext', hok', hieo', hm32', hsetpc',
            hstorepc', hf⟩ :=
          lui_decode_fields_of_binding rd imm (regidx_to_fin c.rd).isLt
            (addr k) (trace.program j) hbk
        have hext : ext' = ext :=
          Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
        subst ext'
        refine ⟨ho, hjo1, hjo2, ?_, hf⟩
        rw [hs]
        simp only [rd, Transpiler.ind]
        apply Fin.ext
        change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
        exact Nat.mod_eq_of_lt (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)) }

private theorem control_rom_offset (imm : BitVec w) (d : DecodedRv64im)
    (hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv = BitVec.signExtend 64 imm) :
    ((IScalar.cast IScalarTy.I64 d.imm).val : FGL) =
      ((BitVec.signExtend 64 imm).toInt : FGL) := by
  congr 1
  change (BitVec.signExtend 64 d.imm.bv).toInt = _
  rw [show BitVec.signExtend 64 d.imm.bv = BitVec.signExtend 64 imm by
    simpa only using hdimm]

private theorem signExtend21_of_sign_control (v : BitVec 21) (h : v[20] = true) :
    v.setWidth 32 - 2097152#32 = BitVec.signExtend 32 v := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, BitVec.toInt_signExtend_of_le (by omega)]
  have hlo : 1048576 ≤ v.toNat := by
    by_contra hnlt
    have ht := Nat.testBit_lt_two_pow (show v.toNat < 2 ^ 20 by omega)
    have hb : v.toNat.testBit 20 = true := by
      change v[20] = true
      exact h
    rw [ht] at hb
    contradiction
  have hsetInt : (v.setWidth 32).toInt = v.toNat := by
    rw [BitVec.toInt]
    have hnat : (v.setWidth 32).toNat = v.toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by norm_num))]
    rw [hnat, if_pos (by have hv := v.isLt; norm_num at hv ⊢; omega)]
  have hvInt : v.toInt = (v.toNat : Int) - 2097152 := by
    rw [BitVec.toInt, if_neg (by omega)]
    norm_num
  have hmax : (2097152#32).toInt = 2097152 := by decide
  rw [hvInt, hsetInt, hmax]
  norm_num [Int.bmod]
  have hmod : ((v.toNat : Int) - 2097152) % 4294967296 =
      (v.toNat : Int) - 2097152 + 4294967296 := by
    rw [Int.emod_eq_add_self_emod]
    apply Int.emod_eq_of_lt <;> have hv := v.isLt <;> omega
  rw [hmod, if_neg (by have hv := v.isLt; omega)]
  omega

private theorem signExtend21_of_not_sign_control (v : BitVec 21) (h : v[20] = false) :
    v.setWidth 32 = BitVec.signExtend 32 v := by
  symm
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 32
  · interval_cases i <;>
      simp [BitVec.getElem_signExtend, BitVec.getElem_setWidth,
        BitVec.msb_setWidth] at h ⊢ <;> assumption
  · simp [BitVec.getLsbD_signExtend, hi]

private theorem signext21_control (v : BitVec 21) :
    signext ⟨v.setWidth 32⟩ 21#u32
      ⦃r => r.bv = BitVec.signExtend 32 v⦄ := by
  rw [signext]
  step*
  all_goals
    have hi : i = 20#u32 := UScalar.eq_imp _ _ (by simpa using i_post1)
    subst i
    have hs : sign_bit = 1048576#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [sign_bit_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst sign_bit
    have hm : max_value = 2097152#u32 :=
      UScalar.eq_imp _ _ (by
        norm_num [max_value_post1, U32.size_eq, Nat.shiftLeft_eq])
    subst max_value
    clear i_post1 i_post2 sign_bit_post1 sign_bit_post2 max_value_post1 max_value_post2
  · clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change I32.min ≤ (v.setWidth 32).toInt - (2097152#32).toInt
    have hmin : I32.min = -2147483648 := by
      norm_num [I32.min, I32.numBits_eq]
    have hset : (v.setWidth 32).toInt = v.toNat := by
      rw [BitVec.toInt]
      have hnat : (v.setWidth 32).toNat = v.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by norm_num))]
      rw [hnat, if_pos (by have hv := v.isLt; norm_num at hv ⊢; omega)]
    have hmax : (2097152#32).toInt = 2097152 := by decide
    rw [hmin, hset, hmax]
    omega
  · clear i1_post1 i1_post2
    rw [i2_post, i3_post]
    change (v.setWidth 32).toInt - (2097152#32).toInt ≤ I32.max
    have hmax : I32.max = 2147483647 := by
      norm_num [I32.max, I32.numBits_eq]
    have hset : (v.setWidth 32).toInt = v.toNat := by
      rw [BitVec.toInt]
      have hnat : (v.setWidth 32).toNat = v.toNat := by
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (lt_trans v.isLt (by norm_num))]
      rw [hnat, if_pos (by have hv := v.isLt; norm_num at hv ⊢; omega)]
    have hpow : (2097152#32).toInt = 2097152 := by decide
    rw [hmax, hset, hpow]
    omega
  · calc
      r.bv = i2.bv - i3.bv := r_post2
      _ = v.setWidth 32 - 2097152#32 := by rw [i2_post, i3_post]; rfl
      _ = BitVec.signExtend 32 v := by
        apply signExtend21_of_sign_control
        have hi1 := i1_post2
        change i1.bv = 1048576#32 &&& v.setWidth 32 at hi1
        have hne : (i1 != 0#u32) = true := by assumption
        simp at hne
        change i1.bv.toNat ≠ 0 at hne
        by_contra hb
        have hz : 1048576#32 &&& v.setWidth 32 = 0#32 := by
          apply BitVec.eq_of_getLsbD_eq
          intro k
          by_cases hk : k < 32
          · interval_cases k <;> simp_all
          · simp [BitVec.getLsbD, hk]
        rw [hi1, hz] at hne
        exact hne rfl
  · change v.setWidth 32 = BitVec.signExtend 32 v
    apply signExtend21_of_not_sign_control
    have hi1 := i1_post2
    change i1.bv = 1048576#32 &&& v.setWidth 32 at hi1
    have hne : ¬(i1 != 0#u32) = true := by assumption
    simp at hne
    change i1.bv.toNat = 0 at hne
    have hi1zero : i1.bv = 0#32 := BitVec.eq_of_toNat_eq hne
    rw [hi1] at hi1zero
    have hzbit := congrArg (fun x : BitVec 32 => x[20]) hi1zero
    simpa using hzbit

private theorem rawJType_imm_bits (imm rd : Nat) (hrd : rd < 32)
    (himm : imm < 2097152) (halign : imm % 2 = 0) :
    let assembled :=
      ((((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd &&&
          2147483648#32) >>> 31) <<< 20) |||
        (((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd &&&
          1044480#32) >>> 12) <<< 12) |||
        (((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd &&&
          1048576#32) >>> 20) <<< 11) |||
        (((ZiskFv.Completeness.Rv64imShapes.rawJType imm rd &&&
          2145386496#32) >>> 21) <<< 1))
    assembled.truncate 21 = BitVec.ofNat 21 imm := by
  have hbit0 : imm.testBit 0 = false := by
    rw [Nat.testBit_zero]
    simp [halign]
  have hrdBit (k : Nat) (hk : 5 ≤ k) : rd.testBit k = false :=
    ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) hk
  have hdiv (s k : Nat) :
      (imm / 2 ^ s).testBit k = imm.testBit (s + k) := by
    rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
  have hdiv2 (k : Nat) :
      (imm / 2).testBit k = imm.testBit (k + 1) := by
    simpa [Nat.add_comm] using hdiv 1 k
  have himmhalf : imm = imm / 2 * 2 := by omega
  have htest (k : Nat) :
      imm.testBit k = ((1 ≤ k) && (imm / 2).testBit (k - 1)) := by
    rw [himmhalf]
    simpa using Nat.testBit_mul_two_pow (imm / 2) k 1
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 21
  · interval_cases k <;>
      simp only [ZiskFv.Completeness.Rv64imShapes.rawJType,
        ZiskFv.Completeness.Rv64imShapes.rawOfNat32,
        BitVec.truncate, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat,
        Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
        Nat.testBit_and, Nat.testBit_mod_two_pow] <;>
      simp [Nat.mod_eq_of_lt himm, halign, hbit0, hrdBit, htest] <;>
      norm_num [Nat.testBit] <;>
      simp
  · simp [BitVec.getLsbD, hk]

private theorem decode_j_rawJType_imm
    (imm rd : Nat) (hrd : rd < 32) (himm : imm < 2097152)
    (halign : imm % 2 = 0) (d : DecodedRv64im)
    (hd : decode_j (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd))
      RiscvOpcode.Jal = ok d) :
    (IScalar.hcast UScalarTy.U64 d.imm).bv =
      BitVec.signExtend 64 (BitVec.ofNat 21 imm) := by
  simp only [decode_j, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨_rd, _, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨imm20, himm20, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨imm10_1, himm10, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨imm11, himm11, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨imm19_12, himm19, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i6, hi6, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i7, hi7, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i9, hi9, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i11, hi11, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  obtain ⟨i13, hi13, hd⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hd
  rw [Result.ok.injEq] at hd
  rw [← hd]
  have himm20bv : imm20.bv =
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
        2147483648#u32).bv >>> 31 := by
    rw [show ((toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
      2147483648#u32) >>> 31#i32 : Result Std.U32) =
        ok ⟨(toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
          2147483648#u32).bv >>> 31⟩ from rfl, Result.ok.injEq] at himm20
    exact (congrArg UScalar.bv himm20).symm
  have himm10bv : imm10_1.bv =
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
        2145386496#u32).bv >>> 21 := by
    rw [show ((toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
      2145386496#u32) >>> 21#i32 : Result Std.U32) =
        ok ⟨(toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
          2145386496#u32).bv >>> 21⟩ from rfl, Result.ok.injEq] at himm10
    exact (congrArg UScalar.bv himm10).symm
  have himm11bv : imm11.bv =
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
        1048576#u32).bv >>> 20 := by
    rw [show ((toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
      1048576#u32) >>> 20#i32 : Result Std.U32) =
        ok ⟨(toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
          1048576#u32).bv >>> 20⟩ from rfl, Result.ok.injEq] at himm11
    exact (congrArg UScalar.bv himm11).symm
  have himm19bv : imm19_12.bv =
      (toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
        1044480#u32).bv >>> 12 := by
    rw [show ((toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
      1044480#u32) >>> 12#i32 : Result Std.U32) =
        ok ⟨(toU32 (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) &&&
          1044480#u32).bv >>> 12⟩ from rfl, Result.ok.injEq] at himm19
    exact (congrArg UScalar.bv himm19).symm
  have hi6bv : i6.bv = imm20.bv <<< 20 := by
    rw [show (imm20 <<< 20#i32 : Result Std.U32) =
      ok ⟨imm20.bv <<< 20⟩ from rfl, Result.ok.injEq] at hi6
    exact (congrArg UScalar.bv hi6).symm
  have hi7bv : i7.bv = imm19_12.bv <<< 12 := by
    rw [show (imm19_12 <<< 12#i32 : Result Std.U32) =
      ok ⟨imm19_12.bv <<< 12⟩ from rfl, Result.ok.injEq] at hi7
    exact (congrArg UScalar.bv hi7).symm
  have hi9bv : i9.bv = imm11.bv <<< 11 := by
    rw [show (imm11 <<< 11#i32 : Result Std.U32) =
      ok ⟨imm11.bv <<< 11⟩ from rfl, Result.ok.injEq] at hi9
    exact (congrArg UScalar.bv hi9).symm
  have hi11bv : i11.bv = imm10_1.bv <<< 1 := by
    rw [show (imm10_1 <<< 1#i32 : Result Std.U32) =
      ok ⟨imm10_1.bv <<< 1⟩ from rfl, Result.ok.injEq] at hi11
    exact (congrArg UScalar.bv hi11).symm
  have hi12bv : (i6 ||| i7 ||| i9 ||| i11).bv =
      (imm20.bv <<< 20) ||| (imm19_12.bv <<< 12) |||
        (imm11.bv <<< 11) ||| (imm10_1.bv <<< 1) := by
    change i6.bv ||| i7.bv ||| i9.bv ||| i11.bv = _
    rw [hi6bv, hi7bv, hi9bv, hi11bv]
  have hassembled : (i6 ||| i7 ||| i9 ||| i11).bv.truncate 21 =
      BitVec.ofNat 21 imm := by
    rw [hi12bv, himm20bv, himm19bv, himm11bv, himm10bv]
    exact rawJType_imm_bits imm rd hrd himm halign
  have hwidth : (i6 ||| i7 ||| i9 ||| i11).bv =
      (BitVec.ofNat 21 imm).setWidth 32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k
    by_cases hk : k < 21
    · have hg := congrArg (fun x : BitVec 21 => x.getLsbD k) hassembled
      simpa [BitVec.getLsbD_setWidth, hk, show k < 32 by omega] using hg
    · by_cases hk32 : k < 32
      · interval_cases k <;>
          simp [hi12bv, himm20bv, himm19bv, himm11bv, himm10bv,
            BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
            BitVec.getLsbD_and]
      · simp [BitVec.getLsbD, hk32]
  have hs := signext21_control (BitVec.ofNat 21 imm)
  rw [← hwidth] at hs
  rw [hi13] at hs
  have hi13bv : i13.bv = BitVec.signExtend 32 (BitVec.ofNat 21 imm) := hs
  change BitVec.signExtend 64 i13.bv =
    BitVec.signExtend 64 (BitVec.ofNat 21 imm)
  rw [hi13bv]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases hk : k < 64
  · interval_cases k <;>
      simp [BitVec.getElem_signExtend, BitVec.msb_signExtend]
  · simp [BitVec.getLsbD_signExtend, hk]

/-! ## Branch-family `ProgramDecode` bundles. -/

local macro "branch_program_decode" nm:ident "," f3:term "," rop:term ","
    _neg:term : command => do
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
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
    h_idx : i.val + 1 < trace.mainTable.table.length
    h_imm_aligned : c.imm.toNat % 2 = 0
    hLine : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        RawAtProgramStart start addr rawProgram j (trace.program j).line
          (ZiskFv.Completeness.Rv64imShapes.rawBType c.imm.toNat
            (regidx_to_fin c.r2).val (regidx_to_fin c.r1).val $f3))
  let t2 ← `(noncomputable def $ctorName {n rawLength : Nat}
      (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
      (i : Fin trace.numInstructions) (c : $claimName trace i)
      (start : Fin rawLength → Fin trace.programLength)
      (addr : Fin rawLength → FGL)
      (rawProgram : Fin rawLength → BitVec 32)
      (hbind : ProgramRowsBinding trace start addr rawProgram)
      (rawDecode : $rawName trace i c start addr rawProgram) :
      $programName trace i c := by
    let rs1 := (regidx_to_fin c.r1).val
    let rs2 := (regidx_to_fin c.r2).val
    let imm := c.imm.toNat
    let ext := ($transpileName rs1 rs2 imm (regidx_to_fin c.r1).isLt
      (regidx_to_fin c.r2).isLt).choose
    obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hstore, hconst, hdyn⟩ :=
      ($transpileName rs1 rs2 imm (regidx_to_fin c.r1).isLt
        (regidx_to_fin c.r2).isLt).choose_spec
    let d := hdyn.choose
    have hd := hdyn.choose_spec.1
    have haSrc := hdyn.choose_spec.2.1
    have haOff := hdyn.choose_spec.2.2.1
    have haUse := hdyn.choose_spec.2.2.2.1
    have hbSrc := hdyn.choose_spec.2.2.2.2.1
    have hbOff := hdyn.choose_spec.2.2.2.2.2.1
    have hbUse := hdyn.choose_spec.2.2.2.2.2.2.1
    have htarget := hdyn.choose_spec.2.2.2.2.2.2.2
    have hfields := decode_b_rawBType_fields
      imm rs2 rs1 $f3 (regidx_to_fin c.r2).isLt (regidx_to_fin c.r1).isLt
      (by norm_num)
      (by simpa only [imm] using
        (Aeneas.SimpScalar.BitVec.toNat_lt_two_pow c.imm 13 (by omega)))
      rawDecode.h_imm_aligned $rop d hd
    have hrs1val : d.rs1.val = rs1 := by
      change d.rs1.bv.toNat = rs1
      rw [hfields.1]
      simp [BitVec.toNat_ofNat]
      omega
    have hrs2val : d.rs2.val = rs2 := by
      change d.rs2.bv.toNat = rs2
      rw [hfields.2.1]
      simp [BitVec.toNat_ofNat]
      omega
    have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
        BitVec.signExtend 64 c.imm := by
      simpa only [imm, BitVec.ofNat_toNat] using hfields.2.2
    have hserialized : ∀ j : Fin trace.programLength,
        (trace.program j).line =
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
          trace.program j = serializeExtract (trace.program j).line ext.row := by
      intro j hline
      obtain ⟨k, hstart, haddr, hraw⟩ := rawDecode.hLine j hline
      have hbk : trace.program j = romMessageOfRaw (addr k)
          (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3) := by
        apply primary_row_non_jalr_control hbind ⟨k, hstart, rfl, hraw⟩ ext
        · simpa only [imm, rs1, rs2, ext] using hok
        · rw [ZiskFv.Compliance.Decode.toU32_and127,
            ZiskFv.Compliance.Decode.rawBType_opcode]
          decide
      have hser : trace.program j = serializeExtract (addr k) ext.row := by
        rw [hbk, romMessageOfRaw, hok]
        exact romRowOf_eq_serializeExtract (addr k) ext.row
      exact hser.trans (by rw [haddr])
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
        h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
        h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
        h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
        h_bits_store_reg := by
          simp only [romFlagBitsOfExtract]
          exact decide_eq_false hstore
        aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
          (by simpa only [d, ext, hrs1val, rs1] using haSrc)
          (by simpa only [d, ext, hrs1val, rs1] using haOff) haUse hserialized
        bFacts := bRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r2) ext.row
          (by simpa only [d, ext, hrs2val, rs2] using hbSrc)
          (by simpa only [d, ext, hrs2val, rs2] using hbOff) hbUse hserialized
        h_prog := by
          intro j hline
          obtain ⟨k, hstart, haddr, hraw⟩ := rawDecode.hLine j hline
          have hbk : trace.program j =
              romMessageOfRaw (addr k)
                (ZiskFv.Completeness.Rv64imShapes.rawBType imm rs2 rs1 $f3) := by
            apply primary_row_non_jalr_control hbind ⟨k, hstart, rfl, hraw⟩ ext
            · simpa only [imm, rs1, rs2, ext] using hok
            · rw [ZiskFv.Compliance.Decode.toU32_and127,
                ZiskFv.Compliance.Decode.rawBType_opcode]
              decide
          obtain ⟨ho, hconstant, ext', hok', _hieo', _hm32', _hsetpc',
              _hstorepc', hf⟩ :=
            $fieldsName rs1 rs2 imm (regidx_to_fin c.r1).isLt
              (regidx_to_fin c.r2).isLt (addr k) (trace.program j) hbk
          have hext : ext' = ext :=
            Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
          subst ext'
          have htargetF :
              ((IScalar.cast IScalarTy.I64 d.imm).val : FGL) =
                ((BitVec.signExtend 64 c.imm).toInt : FGL) :=
            control_rom_offset c.imm d hdimm
          first
          | exact ⟨ho, by
              rw [hbk, romMessageOfRaw, hok]
              simp only [romRowOf_eq_serializeExtract, serializeExtract]
              rw [htarget, htargetF], hconstant, hf⟩
          | exact ⟨ho, hconstant, by
              rw [hbk, romMessageOfRaw, hok]
              simp only [romRowOf_eq_serializeExtract, serializeExtract]
              rw [htarget, htargetF], hf⟩ })
  return ⟨Lean.mkNullNode #[t1, t2]⟩

branch_program_decode beq, 0, RiscvOpcode.Beq, false
branch_program_decode bne, 1, RiscvOpcode.Bne, true
branch_program_decode blt, 4, RiscvOpcode.Blt, false
branch_program_decode bge, 5, RiscvOpcode.Bge, true
branch_program_decode bltu, 6, RiscvOpcode.Bltu, false
branch_program_decode bgeu, 7, RiscvOpcode.Bgeu, true

structure RawProgramDecode_auipc {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_auipc trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_rd_ne_zero : (regidx_to_fin c.rd).val ≠ 0
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      RawAtProgramStart start addr rawProgram j (trace.program j).line
        (ZiskFv.Completeness.Rv64imShapes.rawUType
          (c.imm ++ (0 : BitVec 12)).toNat (regidx_to_fin c.rd).val 0x17)

noncomputable def ProgramDecode_auipc_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_auipc trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_auipc trace i c start addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_auipc trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let imm := (c.imm ++ (0 : BitVec 12)).toNat
  let ext := (transpile_auipc rd imm (regidx_to_fin c.rd).isLt
    rawDecode.h_rd_ne_zero).choose
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hconstant, hstoreOffset,
      hstoreInd, hstoreReg, hdyn⟩ :=
    (transpile_auipc rd imm (regidx_to_fin c.rd).isLt
      rawDecode.h_rd_ne_zero).choose_spec
  let d := hdyn.choose
  have hd := hdyn.choose_spec.1
  have htarget := hdyn.choose_spec.2
  have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
      BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12)) :=
    decode_u_rawUType_imm (c.imm) rd 0x17 (regidx_to_fin c.rd).isLt
      (by norm_num) RiscvOpcode.Auipc d hd
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hstoreInd
      h_bits_store_reg := by
        exact storeBit_of_store_iff_val ext.row (regidx_to_fin c.rd)
          (by simpa only [ext, rd] using hstoreReg)
      h_prog := by
        intro j hline
        obtain ⟨k, hstart, haddr, hraw⟩ := rawDecode.hLine j hline
        have hbk : trace.program j =
            romMessageOfRaw (addr k)
              (ZiskFv.Completeness.Rv64imShapes.rawUType imm rd 0x17) := by
          apply primary_row_non_jalr_control hbind ⟨k, hstart, rfl, hraw⟩ ext
          · simpa only [imm, rd, ext] using hok
          · rw [ZiskFv.Compliance.Decode.toU32_and127,
              ZiskFv.Compliance.Decode.rawUType_opcode imm rd 0x17 (by norm_num)]
            decide
        obtain ⟨ho, hjo1, hso, ext', hok', _hieo', _hm32', _hsetpc',
            _hstorepc', hf⟩ :=
          auipc_decode_fields_of_binding rd imm (regidx_to_fin c.rd).isLt
            rawDecode.h_rd_ne_zero (addr k) (trace.program j) hbk
        have hext : ext' = ext :=
          Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
        subst ext'
        have htargetF :
            ((IScalar.cast IScalarTy.I64 d.imm).val : FGL) =
              ((BitVec.signExtend 64 (c.imm ++ (0 : BitVec 12))).toInt : FGL) :=
          control_rom_offset (c.imm ++ (0 : BitVec 12)) d hdimm
        refine ⟨ho, hjo1, ?_, ?_, hf⟩
        · rw [hbk, romMessageOfRaw, hok]
          simp only [romRowOf_eq_serializeExtract, serializeExtract]
          rw [htarget, htargetF]
        · rw [hso]
          simp only [rd, Transpiler.ind]
          apply Fin.ext
          change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
          exact Nat.mod_eq_of_lt
            (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)) }

structure RawProgramDecode_jal {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_jal trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_rd_ne_zero : (regidx_to_fin c.rd).val ≠ 0
  h_imm_aligned : c.imm.toNat % 2 = 0
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      RawAtProgramStart start addr rawProgram j (trace.program j).line
        (ZiskFv.Completeness.Rv64imShapes.rawJType
          c.imm.toNat (regidx_to_fin c.rd).val)

noncomputable def ProgramDecode_jal_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_jal trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_jal trace i c start addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_jal trace i c := by
  let rd := (regidx_to_fin c.rd).val
  let imm := c.imm.toNat
  let ext := (transpile_jal rd imm (regidx_to_fin c.rd).isLt
    rawDecode.h_rd_ne_zero).choose
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hconstant, hstoreOffset,
      hstoreInd, hstoreReg, hdyn⟩ :=
    (transpile_jal rd imm (regidx_to_fin c.rd).isLt
      rawDecode.h_rd_ne_zero).choose_spec
  let d := hdyn.choose
  have hd := hdyn.choose_spec.1
  have htarget := hdyn.choose_spec.2
  have hdimm : (IScalar.hcast UScalarTy.U64 d.imm).bv =
      BitVec.signExtend 64 c.imm := by
    simpa only [imm, BitVec.ofNat_toNat] using
      decode_j_rawJType_imm imm rd (regidx_to_fin c.rd).isLt
        (by
          simpa only [imm] using
            (Aeneas.SimpScalar.BitVec.toNat_lt_two_pow c.imm 21 (by omega)))
        rawDecode.h_imm_aligned d hd
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := by simpa only [ext, romFlagBitsOfExtract] using hieo
      h_bits_m32 := by simpa only [ext, romFlagBitsOfExtract] using hm32
      h_bits_set_pc := by simpa only [ext, romFlagBitsOfExtract] using hsetpc
      h_bits_store_pc := by simpa only [ext, romFlagBitsOfExtract] using hstorepc
      h_bits_store_ind := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hstoreInd
      h_bits_store_reg := by
        exact storeBit_of_store_iff_val ext.row (regidx_to_fin c.rd)
          (by simpa only [ext, rd] using hstoreReg)
      h_prog := by
        intro j hline
        obtain ⟨k, hstart, haddr, hraw⟩ := rawDecode.hLine j hline
        have hbk : trace.program j =
            romMessageOfRaw (addr k)
              (ZiskFv.Completeness.Rv64imShapes.rawJType imm rd) := by
          apply primary_row_non_jalr_control hbind ⟨k, hstart, rfl, hraw⟩ ext
          · simpa only [imm, rd, ext] using hok
          · rw [ZiskFv.Compliance.Decode.toU32_and127,
              ZiskFv.Compliance.Decode.rawJType_opcode]
            decide
        obtain ⟨ho, hjo2, hso, ext', hok', _hieo', _hm32', _hsetpc',
            _hstorepc', hf⟩ :=
          jal_decode_fields_of_binding rd imm (regidx_to_fin c.rd).isLt
            rawDecode.h_rd_ne_zero (addr k) (trace.program j) hbk
        have hext : ext' = ext :=
          Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
        subst ext'
        have htargetF :
            ((IScalar.cast IScalarTy.I64 d.imm).val : FGL) =
              ((BitVec.signExtend 64 c.imm).toInt : FGL) :=
          control_rom_offset c.imm d hdimm
        refine ⟨ho, ?_, hjo2, ?_, hf⟩
        · rw [hbk, romMessageOfRaw, hok]
          simp only [romRowOf_eq_serializeExtract, serializeExtract]
          rw [htarget, htargetF]
        · rw [hso]
          simp only [rd, Transpiler.ind]
          apply Fin.ext
          change (regidx_to_fin c.rd).val % GL_prime = (regidx_to_fin c.rd).val
          exact Nat.mod_eq_of_lt
            (lt_trans (regidx_to_fin c.rd).isLt (by norm_num)) }

/-- Raw-program evidence for one supported FENCE step.  Only the claim-side
    defect witnesses and the Main-row bound remain caller supplied; all
    committed-ROM fields are recovered from the raw word. -/
structure RawProgramDecode_fence {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_fence trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  h_fm_zero : c.fm = 0#4
  h_rs_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rs
  h_rd_x0 : ZiskFv.Compliance.Defects.IsX0Reg c.rd
  hLine : ∀ j : Fin trace.programLength,
    (trace.program j).line =
        (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      RawAtProgramStart start addr rawProgram j (trace.program j).line
        (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence
          c.fenceP.toNat c.fenceS.toNat)

/-- Rebuild the current committed-program FENCE bundle from the raw program and
    the op-agnostic production-lowering certificate. -/
noncomputable def ProgramDecode_fence_from_rawProgram {n rawLength : Nat}
    (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_fence trace i)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL)
    (rawProgram : Fin rawLength → BitVec 32)
    (hbind : ProgramRowsBinding trace start addr rawProgram)
    (rawDecode : RawProgramDecode_fence trace i c start addr rawProgram) :
    ZiskFv.Compliance.RomDecodeBinding.ProgramDecode_fence trace i c := by
  let pred := c.fenceP.toNat
  let succ := c.fenceS.toNat
  have hp : pred < 16 := by
    simpa only [pred] using
      (Aeneas.SimpScalar.BitVec.toNat_lt_two_pow c.fenceP 4 (by omega))
  have hs : succ < 16 := by
    simpa only [succ] using
      (Aeneas.SimpScalar.BitVec.toNat_lt_two_pow c.fenceS 4 (by omega))
  let ext := (transpile_fence pred succ hp hs).choose
  obtain ⟨hok, hop, hieo, _hm32, hsetpc, _hstorepc, hj1, hj2, hstoreReg⟩ :=
    (transpile_fence pred succ hp hs).choose_spec
  refine
    { h_idx := rawDecode.h_idx
      h_fm_zero := rawDecode.h_fm_zero
      h_rs_x0 := rawDecode.h_rs_x0
      h_rd_x0 := rawDecode.h_rd_x0
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := ?_
      h_bits_set_pc := ?_
      h_bits_store_reg := by
        simp only [romFlagBitsOfExtract]
        exact decide_eq_false hstoreReg
      h_prog := ?_ }
  · simpa only [ext, romFlagBitsOfExtract] using hieo
  · simpa only [ext, romFlagBitsOfExtract] using hsetpc
  · intro j hline
    obtain ⟨k, hstart, haddr, hraw⟩ := rawDecode.hLine j hline
    have hbk : trace.program j =
        romMessageOfRaw (addr k)
          (ZiskFv.Completeness.Rv64imShapes.rawSupportedFence pred succ) := by
      apply primary_row_non_jalr_control hbind ⟨k, hstart, rfl, hraw⟩ ext
      · simpa only [pred, succ, ext] using hok
      · rw [ZiskFv.Compliance.Decode.toU32_and127,
          ZiskFv.Compliance.Decode.rawSupportedFence_opcode]
        decide
    obtain ⟨ho, hjo1, hjo2, ext', hok', _hieo', _hm32', _hsetpc',
        _hstorepc', hf⟩ :=
      fence_decode_fields_of_binding pred succ hp hs
        (addr k) (trace.program j) hbk
    have hext : ext' = ext := Result.ok.inj (hok'.symm.trans (by simpa only [ext] using hok))
    subst ext'
    exact ⟨ho, hjo1, hjo2, hf⟩

section AxiomAudit
#print axioms ProgramDecode_beq_from_rawProgram
#print axioms ProgramDecode_bne_from_rawProgram
#print axioms ProgramDecode_blt_from_rawProgram
#print axioms ProgramDecode_bge_from_rawProgram
#print axioms ProgramDecode_bltu_from_rawProgram
#print axioms ProgramDecode_bgeu_from_rawProgram
#print axioms ProgramDecode_lui_from_rawProgram
#print axioms ProgramDecode_auipc_from_rawProgram
#print axioms ProgramDecode_jal_from_rawProgram
#print axioms ProgramDecode_fence_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
