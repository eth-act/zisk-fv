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

private theorem and_shr_reorder (x : BitVec 32) (k : Nat) (hk : k + 5 ≤ 32) :
    (x &&& BitVec.ofNat 32 (31 <<< k)) >>> k = (x >>> k) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge (i : Nat) 5 with h5 | h5
  · rw [decide_eq_true (show k + (i : Nat) < 32 by omega),
      decide_eq_true (show (i : Nat) < 32 by omega)]
    simp [show k ≤ k + (i : Nat) by omega, show k + (i : Nat) - k = (i : Nat) by omega]
  · rw [ZiskFv.Compliance.Decode.tbf (show (31 : Nat) < 2 ^ 5 by norm_num)
        (show 5 ≤ k + (i : Nat) - k by omega),
      ZiskFv.Compliance.Decode.tbf (show (31 : Nat) < 2 ^ 5 by norm_num)
        (show 5 ≤ (i : Nat) by omega)]
    simp

private theorem and1015808_shr15 (x : BitVec 32) :
    (x &&& 1015808#32) >>> 15 = (x >>> 15) &&& 31#32 := by
  have h := and_shr_reorder x 15 (by norm_num)
  simpa using h

private theorem and32505856_shr20 (x : BitVec 32) :
    (x &&& 32505856#32) >>> 20 = (x >>> 20) &&& 31#32 := by
  have h := and_shr_reorder x 20 (by norm_num)
  simpa using h

theorem rawRType_rs1 (funct7 rs2 rs1 funct3 rd opcode : Nat)
    (hrs1 : rs1 < 32) (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode)
        &&& 1015808#32) >>> 15 = BitVec.ofNat 32 rs1 := by
  rw [and1015808_shr15]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawRType,
    ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 15 + i) := by omega
  have e20 : ¬ (20 ≤ 15 + i) := by omega
  have e15 : 15 ≤ 15 + i := by omega
  have e12 : 12 ≤ 15 + i := by omega
  have e7 : 7 ≤ 15 + i := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hf3', hrd', hop', show 15 + i - 15 = i from by omega]

theorem rawRType_rs2 (funct7 rs2 rs1 funct3 rd opcode : Nat)
    (hrs2 : rs2 < 32) (hrs1 : rs1 < 32) (hf3 : funct3 < 8)
    (hrd : rd < 32) (hop : opcode < 128) :
    ((ZiskFv.Completeness.Rv64imShapes.rawRType funct7 rs2 rs1 funct3 rd opcode)
        &&& 32505856#32) >>> 20 = BitVec.ofNat 32 rs2 := by
  rw [and32505856_shr20]
  simp only [ZiskFv.Completeness.Rv64imShapes.rawRType,
    ZiskFv.Completeness.Rv64imShapes.rawOfNat32]
  refine ZiskFv.Compliance.Decode.ofNat32_shift_mask_eq _ 20 5 rs2 hrs2 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 20 + i) := by omega
  have e20 : 20 ≤ 20 + i := by omega
  have e15 : 15 ≤ 20 + i := by omega
  have e12 : 12 ≤ 20 + i := by omega
  have e7 : 7 ≤ 20 + i := by omega
  have hrs1' : rs1.testBit (20 + i - 15) = false :=
    ZiskFv.Compliance.Decode.tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (20 + i - 12) = false :=
    ZiskFv.Compliance.Decode.tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (20 + i - 7) = false :=
    ZiskFv.Compliance.Decode.tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (20 + i) = false :=
    ZiskFv.Compliance.Decode.tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hrs1', hf3', hrd', hop',
    show 20 + i - 20 = i from by omega]

theorem decode_r_fields (raw : Std.U32) (rop : RiscvOpcode) :
    ∃ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d
      ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7
      ∧ d.rs1.bv = (raw &&& 1015808#u32).bv >>> 15
      ∧ d.rs2.bv = (raw &&& 32505856#u32).bv >>> 20 := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> rfl

theorem store_reg_raw_index_pins
    (self z : zisk_inst_builder.ZiskInstBuilder) (rd : Std.U32)
    (hrd : rd.val < 32)
    (hzero : self.i.store_offset = 0#i64) (hstore : self.i.store = 0#u64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self
      (UScalar.hcast IScalarTy.I64 rd) false false = ok z) :
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

theorem store_reg_u32_is_reg
    (self z : zisk_inst_builder.ZiskInstBuilder) (rd : Std.U32)
    (hrd : rd.val < 32) (hrdne : rd.val ≠ 0)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self
      (UScalar.hcast IScalarTy.I64 rd) false false = ok z) :
    z.i.store = zisk_inst.STORE_REG := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  have e1 := ZiskFv.Compliance.Extraction.cast_one_i64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_i64
  have erd := ZiskFv.Compliance.Extraction.hcast_u32_i64_val rd
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; simp [zisk_inst.STORE_REG])
    | (exfalso; scalar_tac)
  all_goals exfalso; scalar_tac

theorem store_reg_u32_zero_not_reg
    (self z : zisk_inst_builder.ZiskInstBuilder) (rd : Std.U32)
    (hrd : rd.val = 0) (hself : self.i.store = 0#u64)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self
      (UScalar.hcast IScalarTy.I64 rd) false false = ok z) :
    z.i.store ≠ zisk_inst.STORE_REG := by
  have hrd0 : rd = 0#u32 := UScalar.eq_of_val_eq hrd
  subst rd
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, bind_assoc, Bind.bind, pure, Pure.pure] at h
  have e0 : UScalar.hcast IScalarTy.I64 0#u32 = 0#i64 := by rfl
  have e1 := ZiskFv.Compliance.Extraction.cast_one_i64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_i64
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst z
       simpa [hself, zisk_inst.STORE_REG])
    | (exfalso; scalar_tac)

theorem src_a_reg_pres_store (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64) (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg self reg usp = ok z) :
    z.i.store_offset = self.i.store_offset ∧ z.i.store = self.i.store := by
  simp [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
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

theorem src_a_reg_zero_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg self 0#u64 usp = ok z) :
    z.i.a_src = zisk_inst.SRC_IMM ∧ z.i.a_offset_imm0 = 0#u64 ∧
      z.i.a_use_sp_imm1 = 0#u64 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    lift, Bind.bind, bind_ok] at h
  simp only [if_true] at h
  have hz : (0#u64 >>> 32#i32) = ok 0#u64 := by rfl
  rw [hz] at h
  simp only [bind_ok, Result.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

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

theorem src_b_reg_zero_pins (self z : zisk_inst_builder.ZiskInstBuilder)
    (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self 0#u64 usp = ok z) :
    z.i.b_src = zisk_inst.SRC_IMM ∧ z.i.b_offset_imm0 = 0#u64 ∧
      z.i.b_use_sp_imm1 = 0#u64 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    lift, Bind.bind, bind_ok] at h
  simp only [if_true] at h
  have hz : (0#u64 >>> 32#i32) = ok 0#u64 := by rfl
  rw [hz] at h
  simp only [bind_ok, Result.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem src_a_reg_false_use_sp_zero (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_a_reg self reg false = ok z) :
    z.i.a_use_sp_imm1 = 0#u64 := by
  by_cases hz : reg = 0#u64
  · subst reg
    exact (src_a_reg_zero_pins self z false h).2.2
  simp only [zisk_inst_builder.ZiskInstBuilder.src_a_reg,
    zisk_inst_builder.ZiskInstBuilder.src_a_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok, if_neg hz] at h
  simp only [Bool.false_eq_true, if_false, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; rfl)
    | (subst z; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)

private theorem src_b_reg_false_use_sp_zero (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg false = ok z) :
    z.i.b_use_sp_imm1 = 0#u64 := by
  by_cases hz : reg = 0#u64
  · subst reg
    exact (src_b_reg_zero_pins self z false h).2.2
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok, if_neg hz] at h
  simp only [Bool.false_eq_true, if_false, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; rfl)
    | (subst z; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)

private theorem src_b_reg_a_use_sp_pres (self z : zisk_inst_builder.ZiskInstBuilder)
    (reg : Std.U64) (usp : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_reg self reg usp = ok z) :
    z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_reg,
    zisk_inst_builder.ZiskInstBuilder.src_b_imm,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, Bind.bind, bind_ok] at h
  split_ifs at h <;> (try simp only [bind_ok] at h) <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; rfl)

theorem op_zisk_use_sp_pres (self z : zisk_inst_builder.ZiskInstBuilder)
    (op : zisk_ops.ZiskOp)
    (h : zisk_inst_builder.ZiskInstBuilder.op_zisk self op = ok z) :
    z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1 ∧
      z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.op_zisk,
    zisk_inst_builder.ZiskInstBuilder.set_runtime_op_fields,
    core.convert.IntoFrom.into,
    zisk_inst.ZiskOperationType.Insts.CoreConvertFromOpType.from,
    Bind.bind] at h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨self1, hself1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, _, h4⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp hself1
  rw [Result.ok.injEq] at h h4
  subst h
  subst h4
  exact ⟨rfl, rfl⟩

theorem store_reg_use_sp_pres (self z : zisk_inst_builder.ZiskInstBuilder)
    (off : Std.I64) (usp spc : Bool)
    (h : zisk_inst_builder.ZiskInstBuilder.store_reg self off usp spc = ok z) :
    z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1 ∧
      z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.store_reg,
    zisk_registers.REGS_IN_MAIN_FROM, zisk_registers.REGS_IN_MAIN_TO,
    zisk_registers.REG_FIRST, mem.SYS_ADDR, mem.RAM_ADDR,
    lift, bind_ok, Bind.bind] at h
  split_ifs at h <;>
    first
    | (rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       obtain ⟨_, _, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
       rw [Result.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem j_use_sp_pres (self z : zisk_inst_builder.ZiskInstBuilder)
    (j1 j2 : Std.I64)
    (h : zisk_inst_builder.ZiskInstBuilder.j self j1 j2 = ok z) :
    z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1 ∧
      z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.j] at h
  rw [Result.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

theorem build_use_sp_pres (self z : zisk_inst_builder.ZiskInstBuilder)
    (h : zisk_inst_builder.ZiskInstBuilder.build self = ok z) :
    z.i.a_use_sp_imm1 = self.i.a_use_sp_imm1 ∧
      z.i.b_use_sp_imm1 = self.i.b_use_sp_imm1 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.build] at h
  rw [Result.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

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
      ∧ (zib.i.store = zisk_inst.STORE_REG ↔ i.rd.val ≠ 0) := by
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
  obtain ⟨hso, hst⟩ := store_reg_raw_index_pins z3 z4 i.rd hrd h30.1 h30.2 h4
  obtain ⟨hjso, hjst⟩ := j_pres_store _ _ _ _ h5
  have hz65 := ZiskFv.Compliance.Extraction.build_eq _ _ h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7, ?_, ?_, ?_⟩
  · rw [hz65]
    rw [hjso]
    exact hso
  · rw [hz65]
    exact fun hh => hst (hjst.symm.trans hh)
  · have hjst' := j_pres_store _ _ _ _ h5
    constructor
    · intro hreg hzero
      rw [hz65, hjst'.2] at hreg
      exact store_reg_u32_zero_not_reg z3 z4 i.rd hzero h30.2 h4 hreg
    · intro hne
      rw [hz65, hjst'.2]
      exact store_reg_u32_is_reg z3 z4 i.rd hrd hne h4

theorem create_register_op_typed_source_pins
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp)
    (inst_size : Std.U64) (ctx : riscv2zisk_context.Riscv2ZiskContext)
    (hrs1 : i.rs1.val < 32) (hrs2 : i.rs2.val < 32)
    (h : riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed
      self i op inst_size = ok ctx) :
    ∃ zib, ctx.extract_inst = some zib ∧
      zib.i.a_src = (if i.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      zib.i.a_offset_imm0.val = i.rs1.val ∧ zib.i.a_use_sp_imm1 = 0#u64 ∧
      zib.i.b_src = (if i.rs2.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      zib.i.b_offset_imm0.val = i.rs2.val ∧ zib.i.b_use_sp_imm1 = 0#u64 := by
  simp only [riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed,
    lift, Bind.bind, bind_ok] at h
  obtain ⟨z0, h0, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z1, h1, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z2, h2, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z3, h3, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z4, h4, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z5, h5, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨z6, h6, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  obtain ⟨_, h7, h⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  rw [Result.ok.injEq] at h
  subst h
  have hcast1 := ZiskFv.Compliance.Extraction.cast_u32_u64_val i.rs1
  have hcast2 := ZiskFv.Compliance.Extraction.cast_u32_u64_val i.rs2
  have e1 := ZiskFv.Compliance.Extraction.cast_one_u64
  have e31 := ZiskFv.Compliance.Extraction.cast_31_u64
  have ha : z1.i.a_src = (if i.rs1.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG) ∧
      z1.i.a_offset_imm0.val = i.rs1.val ∧ z1.i.a_use_sp_imm1 = 0#u64 := by
    by_cases hz : i.rs1.val = 0
    · have hc : UScalar.cast UScalarTy.U64 i.rs1 = 0#u64 :=
        UScalar.eq_of_val_eq (hcast1.trans hz)
      obtain ⟨hs, ho, hu⟩ := src_a_reg_zero_pins z0 z1 false (by simpa [hc] using h1)
      simp only [if_pos hz]
      exact ⟨hs, by rw [ho]; norm_num; exact hz.symm, hu⟩
    · have hcne : UScalar.cast UScalarTy.U64 i.rs1 ≠ 0#u64 := by
        intro heq
        apply hz
        have := congrArg UScalar.val heq
        simpa [hcast1] using this
      obtain ⟨hs, ho⟩ := ZiskFv.Compliance.Extraction.src_a_reg_src_eq z0 z1 _ false
        hcne h1
          (by simp only [zisk_registers.REGS_IN_MAIN_FROM]; scalar_tac)
          (by simp only [zisk_registers.REGS_IN_MAIN_TO]; scalar_tac)
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
        intro heq
        apply hz
        have := congrArg UScalar.val heq
        simpa [hcast2] using this
      obtain ⟨hs, ho, _, _⟩ := ZiskFv.Compliance.Extraction.src_b_reg_src_eq z1 z2 _ false
        hcne h2
          (by simp only [zisk_registers.REGS_IN_MAIN_FROM]; scalar_tac)
          (by simp only [zisk_registers.REGS_IN_MAIN_TO]; scalar_tac)
      simp only [if_neg hz]
      exact ⟨hs, by rw [ho, hcast2], src_b_reg_false_use_sp_zero z1 z2 _ h2⟩
  obtain ⟨hba, hbao⟩ := ZiskFv.Compliance.Extraction.src_b_reg_a_pres z1 z2 _ false h2
  have hbau := src_b_reg_a_use_sp_pres z1 z2 _ false h2
  obtain ⟨hoa, hoao, hob, hobo⟩ := ZiskFv.Compliance.Extraction.op_zisk_src_pres z2 z3 op h3
  obtain ⟨houa, houb⟩ := op_zisk_use_sp_pres z2 z3 op h3
  obtain ⟨hsa, hsao, hsb, hsbo⟩ :=
    ZiskFv.Compliance.Extraction.store_reg_src_pres z3 _ _ _ z4 h4
  obtain ⟨hsua, hsub⟩ := store_reg_use_sp_pres z3 z4 _ _ _ h4
  obtain ⟨hja, hjao, hjb, hjbo⟩ := ZiskFv.Compliance.Extraction.j_src_pres z4 _ _ z5 h5
  obtain ⟨hjua, hjub⟩ := j_use_sp_pres z4 z5 _ _ h5
  obtain ⟨hda, hdao, hdb, hdbo⟩ := ZiskFv.Compliance.Extraction.build_src_pres z5 z6 h6
  obtain ⟨hdua, hdub⟩ := build_use_sp_pres z5 z6 h6
  refine ⟨z6, ZiskFv.Compliance.Extraction.insert_inst_extract _ _ _ _ h7,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hda, hja, hsa, hoa, hba]; exact ha.1
  · rw [hdao, hjao, hsao, hoao, hbao]; exact ha.2.1
  · rw [hdua, hjua, hsua, houa, hbau]; exact ha.2.2
  · rw [hdb, hjb, hsb, hob]; exact hb.1
  · rw [hdbo, hjbo, hsbo, hobo]; exact hb.2.1
  · rw [hdub, hjub, hsub, houb]; exact hb.2.2

/-- The REAL transpile pipeline on a register-op raw word `raw` reduces to the
    op's decode-field pins, given: the decode classifies to `decode_r raw rop`;
    `rop` lowers to the single-row opcode `srop`; the dispatcher routes `srop`
    unconditionally to `create_register_op_typed … zop 4`; and the static op-type
    facts (`code`/`is_m32`/`op_type`, external). -/
theorem transpile_register_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (rdv rs1v rs2v : Nat)
    (hrdv : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rd.val = rdv)
    (hrs1v : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rs1.val = rs1v)
    (hrs2v : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d → d.rs2.val = rs2v)
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
      ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rdv ≠ 0)
      ∧ ext.row.a_src = (if rs1v = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.a_offset_imm0.val = rs1v ∧ ext.row.a_use_sp_imm1 = 0#u64
      ∧ ext.row.b_src = (if rs2v = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
      ∧ ext.row.b_offset_imm0.val = rs2v ∧ ext.row.b_use_sp_imm1 = 0#u64 := by
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
  obtain ⟨zibSrc, hzibSrc, haSrc, haOff, haUse, hbSrc, hbOff, hbUse⟩ :=
    create_register_op_typed_source_pins
      { defCtx with extract_marker := () } input zop 4#u64 ctx0
      (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b) hctx0
  have hzzSrc : zibSrc = zib := Option.some.inj (hzibSrc.symm.trans hzib)
  rw [hzzSrc] at haSrc haOff haUse hbSrc hbOff hbUse
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  obtain ⟨row', hrow', hraSrc, hraUse, hraOff, hrbSrc, hrbUse, hrbOff,
      _, _, hrStore', _, _, _, _, _, _⟩ :=
    ZiskFv.Compliance.Extraction.from_inst_full_fields zib.i
  have hrowEq : row' = row := Result.ok.inj (hrow'.symm.trans hrow)
  subst row'
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
  refine ⟨{ accepted := true, decode := dext, row := row }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    rw [hrStoreOffset, hstoreOffset]
    rw [hinput]
    exact_mod_cast hrdv decoded hdecoded
  · show row.store ≠ zisk_inst.STORE_IND
    rw [hrStore]
    exact hstoreInd
  · rw [hrStore, hstoreReg]
    rw [hinput]
    rw [hrdv decoded hdecoded]
  · rw [hraSrc, haSrc, hinput, hrs1v decoded hdecoded]
  · rw [hraOff, haOff, hinput, hrs1v decoded hdecoded]
  · rw [hraUse, haUse]
  · rw [hrbSrc, hbSrc, hinput, hrs2v decoded hdecoded]
  · rw [hrbOff, hbOff, hinput, hrs2v decoded hdecoded]
  · rw [hrbUse, hbUse]

/-! ## Generic decode-field bridge for register ops. -/

private theorem hcast4 : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

private theorem signedOffset_eq_registerIndex (x : Std.U64) (r : Fin 32)
    (h : x.val = r.val) : signedOffset x = Transpiler.ind r := by
  have hx : x.bv.toNat < 32 := by
    change x.bv.toNat < 32
    rw [show x.bv.toNat = r.val by simpa only [UScalar.val] using h]
    exact r.isLt
  have hnonneg : 2 * x.val < 18446744073709551616 := by
    change 2 * x.bv.toNat < 18446744073709551616
    omega
  have hsigned : signedOffset x = (x.bv.toNat : FGL) := by
    simp [signedOffset, BitVec.toInt, if_pos hnonneg]
  rw [hsigned]
  rw [show x.bv.toNat = r.val by simpa only [UScalar.val] using h]
  apply Fin.ext
  simp only [Transpiler.ind]
  exact Nat.mod_eq_of_lt (lt_trans r.isLt (by norm_num))

theorem storeBit_of_store_iff (row : zisk_core.aeneas_extract.ZiskInstExtract)
    (rd : Fin 32) (hstore : row.store = zisk_inst.STORE_REG ↔ rd.val ≠ 0) :
    (romFlagBitsOfExtract row).store_reg = decide (rd ≠ 0) := by
  by_cases hrd : rd = 0
  · have hrdv : rd.val = 0 := by simp [hrd]
    have hnstore : row.store ≠ zisk_inst.STORE_REG := by
      intro hs
      exact (hstore.mp hs) hrdv
    simp [romFlagBitsOfExtract, hnstore, hrd]
  · have hrdv : rd.val ≠ 0 := by
      intro hz
      apply hrd
      apply Fin.ext
      exact hz
    have hs : row.store = zisk_inst.STORE_REG := hstore.mpr hrdv
    simp [romFlagBitsOfExtract, hs, hrd]

theorem storeBit_of_store_iff_val
    (row : zisk_core.aeneas_extract.ZiskInstExtract) (rd : Fin 32)
    (hstore : row.store = zisk_inst.STORE_REG ↔ rd.val ≠ 0) :
    (romFlagBitsOfExtract row).store_reg = decide (rd.val ≠ 0) := by
  by_cases hrd : rd.val = 0
  · have hnstore : row.store ≠ zisk_inst.STORE_REG := by
      intro hs
      exact (hstore.mp hs) hrd
    rw [show (romFlagBitsOfExtract row).store_reg = false by
      exact decide_eq_false hnstore]
    have hn : ¬ rd.val ≠ 0 := by omega
    exact (decide_eq_false hn).symm
  · have hs : row.store = zisk_inst.STORE_REG := hstore.mpr hrd
    rw [show (romFlagBitsOfExtract row).store_reg = true by
      exact decide_eq_true hs]
    exact (decide_eq_true hrd).symm

theorem aRegisterProgramFacts_of_serialized
    {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (r : Fin 32)
    (row : zisk_core.aeneas_extract.ZiskInstExtract)
    (hsrc : row.a_src = if r.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
    (hoff : row.a_offset_imm0.val = r.val) (huse : row.a_use_sp_imm1 = 0#u64)
    (hserialized : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        trace.program j = serializeExtract (trace.program j).line row) :
    ZiskFv.Compliance.RomDecodeBinding.ARegisterProgramFacts trace i
      (romFlagBitsOfExtract row) r := by
  refine { h_src_reg := ?_, h_src_imm := ?_, h_program := ?_ }
  · by_cases hr : r = 0
    · have hs : row.a_src = zisk_inst.SRC_IMM := by simpa [hr] using hsrc
      have hn : row.a_src ≠ zisk_inst.SRC_REG := by
        rw [hs]
        intro heq
        have hv := congrArg UScalar.val heq
        norm_num [zisk_inst.SRC_IMM, zisk_inst.SRC_REG] at hv
      change decide (row.a_src = zisk_inst.SRC_REG) = decide (r ≠ 0)
      have hrn : ¬ r ≠ 0 := by exact fun hne => hne hr
      rw [decide_eq_false hn, decide_eq_false hrn]
    · have hrv : r.val ≠ 0 := by
        intro hz
        apply hr
        apply Fin.ext
        exact hz
      have hs : row.a_src = zisk_inst.SRC_REG := by simpa [hrv] using hsrc
      change decide (row.a_src = zisk_inst.SRC_REG) = decide (r ≠ 0)
      rw [decide_eq_true hs, decide_eq_true hr]
  · by_cases hr : r = 0
    · have hs : row.a_src = zisk_inst.SRC_IMM := by simpa [hr] using hsrc
      change decide (row.a_src = zisk_inst.SRC_IMM) = decide (r = 0)
      rw [decide_eq_true hs, decide_eq_true hr]
    · have hrv : r.val ≠ 0 := by
        intro hz
        apply hr
        apply Fin.ext
        exact hz
      have hs : row.a_src = zisk_inst.SRC_REG := by simpa [hrv] using hsrc
      have hn : row.a_src ≠ zisk_inst.SRC_IMM := by
        rw [hs]
        intro heq
        have hv := congrArg UScalar.val heq
        norm_num [zisk_inst.SRC_IMM, zisk_inst.SRC_REG] at hv
      change decide (row.a_src = zisk_inst.SRC_IMM) = decide (r = 0)
      rw [decide_eq_false hn, decide_eq_false hr]
  · intro j hline
    have hs := hserialized j hline
    have ho := congrArg (fun msg => msg.a_offset_imm0) hs
    have hi := congrArg (fun msg => msg.a_imm1) hs
    have hf := congrArg (fun msg => msg.flags) hs
    simp only [serializeExtract] at ho hi hf
    refine ⟨ho.trans (signedOffset_eq_registerIndex row.a_offset_imm0 r hoff), ?_, ?_⟩
    · exact hi.trans (by
        rw [huse]
        unfold sourceImmediate
        split <;> norm_num)
    · exact hf

theorem bRegisterProgramFacts_of_serialized
    {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (r : Fin 32)
    (row : zisk_core.aeneas_extract.ZiskInstExtract)
    (hsrc : row.b_src = if r.val = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
    (hoff : row.b_offset_imm0.val = r.val) (huse : row.b_use_sp_imm1 = 0#u64)
    (hserialized : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        trace.program j = serializeExtract (trace.program j).line row) :
    ZiskFv.Compliance.RomDecodeBinding.BRegisterProgramFacts trace i
      (romFlagBitsOfExtract row) r := by
  refine { h_src_reg := ?_, h_src_imm := ?_, h_program := ?_ }
  · by_cases hr : r = 0
    · have hs : row.b_src = zisk_inst.SRC_IMM := by simpa [hr] using hsrc
      have hn : row.b_src ≠ zisk_inst.SRC_REG := by
        rw [hs]
        intro heq
        have hv := congrArg UScalar.val heq
        norm_num [zisk_inst.SRC_IMM, zisk_inst.SRC_REG] at hv
      change decide (row.b_src = zisk_inst.SRC_REG) = decide (r ≠ 0)
      have hrn : ¬ r ≠ 0 := by exact fun hne => hne hr
      rw [decide_eq_false hn, decide_eq_false hrn]
    · have hrv : r.val ≠ 0 := by
        intro hz
        apply hr
        apply Fin.ext
        exact hz
      have hs : row.b_src = zisk_inst.SRC_REG := by simpa [hrv] using hsrc
      change decide (row.b_src = zisk_inst.SRC_REG) = decide (r ≠ 0)
      rw [decide_eq_true hs, decide_eq_true hr]
  · by_cases hr : r = 0
    · have hs : row.b_src = zisk_inst.SRC_IMM := by simpa [hr] using hsrc
      change decide (row.b_src = zisk_inst.SRC_IMM) = decide (r = 0)
      rw [decide_eq_true hs, decide_eq_true hr]
    · have hrv : r.val ≠ 0 := by
        intro hz
        apply hr
        apply Fin.ext
        exact hz
      have hs : row.b_src = zisk_inst.SRC_REG := by simpa [hrv] using hsrc
      have hn : row.b_src ≠ zisk_inst.SRC_IMM := by
        rw [hs]
        intro heq
        have hv := congrArg UScalar.val heq
        norm_num [zisk_inst.SRC_IMM, zisk_inst.SRC_REG] at hv
      change decide (row.b_src = zisk_inst.SRC_IMM) = decide (r = 0)
      rw [decide_eq_false hn, decide_eq_false hr]
  · intro j hline
    have hs := hserialized j hline
    have ho := congrArg (fun msg => msg.b_offset_imm0) hs
    have hi := congrArg (fun msg => msg.b_imm1) hs
    have hf := congrArg (fun msg => msg.flags) hs
    simp only [serializeExtract] at ho hi hf
    refine ⟨ho.trans (signedOffset_eq_registerIndex row.b_offset_imm0 r hoff), ?_, ?_⟩
    · exact hi.trans (by
        rw [huse]
        unfold sourceImmediate
        split <;> norm_num)
    · exact hf

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
          ∧ (ext.row.store = zisk_inst.STORE_REG ↔ rd ≠ 0)
          ∧ ext.row.a_src = (if rs1 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
          ∧ ext.row.a_offset_imm0.val = rs1 ∧ ext.row.a_use_sp_imm1 = 0#u64
          ∧ ext.row.b_src = (if rs2 = 0 then zisk_inst.SRC_IMM else zisk_inst.SRC_REG)
          ∧ ext.row.b_offset_imm0.val = rs2 ∧ ext.row.b_use_sp_imm1 = 0#u64 := by
      refine transpile_register_of _ $rop $srop $zop $opU8 $m32 $ot rd rs1 rs2 ?_ ?_ ?_ ?_ rfl
        (by intro self input; rfl)
        rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
      · intro d hd
        obtain ⟨d', hd', hrdbv, _, _⟩ := decode_r_fields _ $rop
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rd.bv.toNat = rd
        rw [hrdbv]
        change (((ZiskFv.Completeness.Rv64imShapes.rawRType
          $f7 rs2 rs1 $f3 rd $opw) &&& 3968#32) >>> 7).toNat = rd
        rw [and3968_ushift7,
          rawRType_rd $f7 rs2 rs1 $f3 rd $opw hrd (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      · intro d hd
        obtain ⟨d', hd', _, hrs1bv, _⟩ := decode_r_fields _ $rop
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rs1.bv.toNat = rs1
        rw [hrs1bv]
        change (((ZiskFv.Completeness.Rv64imShapes.rawRType
          $f7 rs2 rs1 $f3 rd $opw) &&& 1015808#32) >>> 15).toNat = rs1
        rw [rawRType_rs1 $f7 rs2 rs1 $f3 rd $opw hrs1 (by norm_num) hrd (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
      · intro d hd
        obtain ⟨d', hd', _, _, hrs2bv⟩ := decode_r_fields _ $rop
        have hdd : d = d' := Result.ok.inj (hd.symm.trans hd')
        rw [hdd]
        change d'.rs2.bv.toNat = rs2
        rw [hrs2bv]
        change (((ZiskFv.Completeness.Rv64imShapes.rawRType
          $f7 rs2 rs1 $f3 rd $opw) &&& 32505856#32) >>> 20).toNat = rs2
        rw [rawRType_rs2 $f7 rs2 rs1 $f3 rd $opw hrs2 hrs1 (by norm_num) hrd (by norm_num)]
        simp [UScalar.val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
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
      hstoreOffset, hstoreInd, hstoreReg, haSrc, haOff, haUse,
      hbSrc, hbOff, hbUse⟩ :=
    (transpile_sub rd rs1 rs2 (regidx_to_fin c.rd).isLt
      (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose_spec
  have hserialized : ∀ j : Fin trace.programLength,
      (trace.program j).line =
          (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        trace.program j = serializeExtract (trace.program j).line ext.row := by
    intro j hline
    obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
    have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
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
    have hbk : trace.program j = romMessageOfRaw (addr k)
        (ZiskFv.Completeness.Rv64imShapes.rawRType 32 rs2 rs1 0 rd 0x33) := by
      simpa only [rd, rs1, rs2] using hp
    have hser : trace.program j = serializeExtract (addr k) ext.row := by
      rw [hbk, romMessageOfRaw, hok]
      exact romRowOf_eq_serializeExtract (addr k) ext.row
    exact hser.trans (by rw [haddr])
  refine
    { h_idx := rawDecode.h_idx
      bits := romFlagBitsOfExtract ext.row
      h_bits_ieo := ?_
      h_bits_m32 := ?_
      h_bits_set_pc := ?_
      h_bits_store_pc := ?_
      h_bits_store_ind := ?_
      h_bits_store_reg := ?_
      aFacts := ?_
      bFacts := ?_
      h_prog := ?_ }
  · simpa only [ext, romFlagBitsOfExtract] using hieo
  · simpa only [ext, romFlagBitsOfExtract] using hm32
  · simpa only [ext, romFlagBitsOfExtract] using hsetpc
  · simpa only [ext, romFlagBitsOfExtract] using hstorepc
  · simp only [romFlagBitsOfExtract]
    exact decide_eq_false hstoreInd
  · exact storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
      (by simpa only [rd] using hstoreReg)
  · exact aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
      (by simpa only [ext, rs1] using haSrc)
      (by simpa only [ext, rs1] using haOff) (by simpa only [ext] using haUse) hserialized
  · exact bRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r2) ext.row
      (by simpa only [ext, rs2] using hbSrc)
      (by simpa only [ext, rs2] using hbOff) (by simpa only [ext] using hbUse) hserialized
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
        hstoreOffset, hstoreInd, hstoreReg, haSrc, haOff, haUse,
        hbSrc, hbOff, hbUse⟩ :=
      ($transpileName rd rs1 rs2 (regidx_to_fin c.rd).isLt
        (regidx_to_fin c.r1).isLt (regidx_to_fin c.r2).isLt).choose_spec
    have hserialized : ∀ j : Fin trace.programLength,
        (trace.program j).line =
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
          trace.program j = serializeExtract (trace.program j).line ext.row := by
      intro j hline
      obtain ⟨k, haddr, hraw⟩ := rawDecode.hLine j hline
      have hprimary := primary_row_at_architectural_line hbind j k haddr.symm
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
      have hbk : trace.program j = romMessageOfRaw (addr k)
          (ZiskFv.Completeness.Rv64imShapes.rawRType $f7 rs2 rs1 $f3 rd $opw) := by
        simpa only [rd, rs1, rs2] using hp
      have hser : trace.program j = serializeExtract (addr k) ext.row := by
        rw [hbk, romMessageOfRaw, hok]
        exact romRowOf_eq_serializeExtract (addr k) ext.row
      exact hser.trans (by rw [haddr])
    refine
      { h_idx := rawDecode.h_idx
        bits := romFlagBitsOfExtract ext.row
        h_bits_ieo := ?_
        h_bits_m32 := ?_
        h_bits_set_pc := ?_
        h_bits_store_pc := ?_
        h_bits_store_ind := ?_
        h_bits_store_reg := storeBit_of_store_iff ext.row (regidx_to_fin c.rd)
          (by simpa only [rd] using hstoreReg)
        aFacts := aRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r1) ext.row
          (by simpa only [rs1] using haSrc) (by simpa only [rs1] using haOff) haUse
          hserialized
        bFacts := bRegisterProgramFacts_of_serialized trace i (regidx_to_fin c.r2) ext.row
          (by simpa only [rs2] using hbSrc) (by simpa only [rs2] using hbOff) hbUse
          hserialized
        h_prog := ?_ }
    · simpa only [ext, romFlagBitsOfExtract] using hieo
    · simpa only [ext, romFlagBitsOfExtract] using hm32
    · simpa only [ext, romFlagBitsOfExtract] using hsetpc
    · simpa only [ext, romFlagBitsOfExtract] using hstorepc
    · simp only [romFlagBitsOfExtract]
      exact decide_eq_false hstoreInd
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
