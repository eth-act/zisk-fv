import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingImmediate

/-!
# Raw-program decode bridge — conditional-copyb ops (issue #159, BLOCK 3)

The five RV64IM ops whose dispatcher arm degenerates to `copyb`/`nop` for
zero-register / zero-immediate inputs, and therefore route to their real
op-builder ONLY under genuine `≠ 0` side-conditions:

  * **ADD, OR** (register, `rawRType`) — route to `create_register_op_typed`
    only when the registers are nonzero.  ADD additionally needs the
    DMA-precompile branch ruled out (`input_precompile = none`, satisfied by
    `defCtx`).  Side-conditions (matching `add_dispatch_static_pins` /
    `or_dispatch_static_pins` EXACTLY): ADD `rd ≠ 0 ∧ rs1 ≠ 0 ∧ rs2 ≠ 0`;
    OR `rs1 ≠ 0 ∧ rs2 ≠ 0`.  The symbolic `i.rd/rs1/rs2 ≠ 0#u32` are derived
    from the Nat `≠ 0` via the R-type field-recovery lemmas.
  * **ADDI, XORI, ORI** (immediate, `rawIType`) — route to
    `immediate_op_or_x0_copyb_typed`, whose op-arm (over copyb) needs
    `rs1 ≠ 0`.  XORI/ORI route there unconditionally at the dispatcher; ADDI
    needs `rd ≠ 0 ∧ imm ≠ 0` to reach the builder (matching
    `addi_dispatch_static_pins` EXACTLY).  `i.rs1 ≠ 0#u32` (and `i.rd ≠ 0#u32`
    for ADDI) are derived from the Nat `≠ 0` via I-type field recovery; the
    decoded `i.imm ≠ 0#i32` is the dispatcher's own guard, threaded as a caller
    hypothesis (it is an operand-column obligation, not derivable from the
    symbolic word's `imm` Nat alone without signext reasoning).

Sound: NO native_decide / bv_decide / new axiom / `sorry`; kernel-only closure
(`propext` / `Classical.choice` / `Quot.sound`).
-/

open Aeneas Aeneas.Std Result zisk_core
open aeneas_extract.rv64im_decode
open Goldilocks
open ZiskFv.Compliance.Extraction
  (defCtx decode_r_bounds decode_i_bounds bind_eq_ok_imp
   new_ok src_a_reg_ok src_b_imm_ok op_zisk_ok store_reg_ok j_ok build_ok insert_inst_ok
   cast_u32_u64_val hcast_u32_i64_val
   create_register_op_typed_ok register_static_pins_of create_register_op_typed_dynamic_pins
   immediate_x0_static_pins_of immediate_op_or_x0_copyb_typed_dynamic_pins
   decode_extract_ok from_inst_ok)

namespace ZiskFv.Compliance.RawProgramBinding

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32 ofNat32_shift_mask_eq tbf)
open ZiskFv.Completeness.Rv64imShapes (rawRType rawIType rawOfNat32)
open aeneas_extract (extract_transpile_rv64im_raw)

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## 1. Decoder field `.bv` recovery (register slices, op-independent). -/

/-- decode_r is `ok`-total (no signext), so each register field's `.bv` is the
    masked-shift by `rfl`. -/
theorem decode_r_fields (raw : Std.U32) (rop : RiscvOpcode) :
    ∃ d, decode_r raw rop = ok d
      ∧ d.rd.bv = (raw &&& 3968#u32).bv >>> 7
      ∧ d.rs1.bv = (raw &&& 1015808#u32).bv >>> 15
      ∧ d.rs2.bv = (raw &&& 32505856#u32).bv >>> 20 := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩ <;> rfl

/-- The `i5.bv` (rs1 shift result) extracted via `>>>`-reduction. -/
private theorem shift15_bv (i5 : Std.U32)
    (h : ((raw &&& 1015808#u32) >>> 15#i32 : Result Std.U32) = ok i5) :
    i5.bv = (raw &&& 1015808#u32).bv >>> 15 := by
  rw [show ((raw &&& 1015808#u32) >>> 15#i32 : Result Std.U32)
        = ok ⟨(raw &&& 1015808#u32).bv >>> 15⟩ from rfl, Result.ok.injEq] at h
  rw [← h]

private theorem shift7_bv (i3 : Std.U32)
    (h : ((raw &&& 3968#u32) >>> 7#i32 : Result Std.U32) = ok i3) :
    i3.bv = (raw &&& 3968#u32).bv >>> 7 := by
  rw [show ((raw &&& 3968#u32) >>> 7#i32 : Result Std.U32)
        = ok ⟨(raw &&& 3968#u32).bv >>> 7⟩ from rfl, Result.ok.injEq] at h
  rw [← h]

/-- decode_i computes `rd`/`rs1` before the `signext` (which is the only partial
    step), so peel binds to recover both `.bv`s. -/
theorem decode_i_rd_rs1_bv (raw : Std.U32) (rop : RiscvOpcode) (sh : Bool) (d : DecodedRv64im)
    (hd : decode_i raw rop sh = ok d) :
    d.rd.bv = (raw &&& 3968#u32).bv >>> 7
      ∧ d.rs1.bv = (raw &&& 1015808#u32).bv >>> 15 := by
  simp only [decode_i, DecodedRv64im.new, lift, bind_ok, Bind.bind] at hd
  obtain ⟨i1, _, hd⟩ := bind_eq_ok_imp hd   -- funct3 shift
  obtain ⟨i3, hi3, hd⟩ := bind_eq_ok_imp hd -- rd shift
  obtain ⟨i5, hi5, hd⟩ := bind_eq_ok_imp hd -- rs1 shift
  obtain ⟨i7, _, hd⟩ := bind_eq_ok_imp hd   -- imm-mask shift
  obtain ⟨i8, _, hd⟩ := bind_eq_ok_imp hd   -- signext
  cases sh
  · rw [if_neg (by decide), Result.ok.injEq] at hd; rw [← hd]
    exact ⟨shift7_bv i3 hi3, shift15_bv i5 hi5⟩
  · rw [if_pos (by decide)] at hd
    obtain ⟨i11, _, hd⟩ := bind_eq_ok_imp hd
    rw [Result.ok.injEq] at hd; rw [← hd]
    exact ⟨shift7_bv i3 hi3, shift15_bv i5 hi5⟩

/-! ## 2. Symbolic-word field recovery (mask-shift selects the register Nat). -/

private theorem and_shr_reorder (x : BitVec 32) (k : Nat) (hk : k + 5 ≤ 32) :
    (x &&& BitVec.ofNat 32 (31 <<< k)) >>> k = (x >>> k) &&& 31#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_shiftLeft]
  rcases Nat.lt_or_ge (i : Nat) 5 with h5 | h5
  · rw [decide_eq_true (show k + (i : Nat) < 32 by omega), decide_eq_true (show (i : Nat) < 32 by omega)]
    simp [show k ≤ k + (i : Nat) by omega, show k + (i : Nat) - k = (i : Nat) by omega]
  · rw [tbf (show (31 : Nat) < 2 ^ 5 by norm_num) (show 5 ≤ k + (i : Nat) - k by omega),
      tbf (show (31 : Nat) < 2 ^ 5 by norm_num) (show 5 ≤ (i : Nat) by omega)]
    simp

private theorem and3968_shr7 (x : BitVec 32) : (x &&& 3968#32) >>> 7 = (x >>> 7) &&& 31#32 := by
  have := and_shr_reorder x 7 (by norm_num); simpa using this

private theorem and1015808_shr15 (x : BitVec 32) : (x &&& 1015808#32) >>> 15 = (x >>> 15) &&& 31#32 := by
  have := and_shr_reorder x 15 (by norm_num); simpa using this

private theorem and32505856_shr20 (x : BitVec 32) : (x &&& 32505856#32) >>> 20 = (x >>> 20) &&& 31#32 := by
  have := and_shr_reorder x 20 (by norm_num); simpa using this

theorem rawRType_rd (funct7 rs2 rs1 funct3 rd opcode : Nat) (hrd : rd < 32)
    (hf3 : funct3 < 8) (hop : opcode < 128) :
    ((rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [rawRType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 7 + i) := by omega
  have e20 : ¬ (20 ≤ 7 + i) := by omega
  have e15 : ¬ (15 ≤ 7 + i) := by omega
  have e12 : ¬ (12 ≤ 7 + i) := by omega
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hop', show 7 + i - 7 = i from by omega]

theorem rawRType_rs1 (funct7 rs2 rs1 funct3 rd opcode : Nat) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 1015808#32) >>> 15 = BitVec.ofNat 32 rs1 := by
  rw [and1015808_shr15]
  simp only [rawRType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 15 + i) := by omega
  have e20 : ¬ (20 ≤ 15 + i) := by omega
  have e15 : (15 ≤ 15 + i) := by omega
  have e12 : (12 ≤ 15 + i) := by omega
  have e7 : (7 ≤ 15 + i) := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false := tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false := tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hf3', hrd', hop', show 15 + i - 15 = i from by omega]

theorem rawRType_rs2 (funct7 rs2 rs1 funct3 rd opcode : Nat) (hrs2 : rs2 < 32) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((rawRType funct7 rs2 rs1 funct3 rd opcode) &&& 32505856#32) >>> 20 = BitVec.ofNat 32 rs2 := by
  rw [and32505856_shr20]
  simp only [rawRType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 20 5 rs2 hrs2 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e25 : ¬ (25 ≤ 20 + i) := by omega
  have e20 : (20 ≤ 20 + i) := by omega
  have e15 : (15 ≤ 20 + i) := by omega
  have e12 : (12 ≤ 20 + i) := by omega
  have e7 : (7 ≤ 20 + i) := by omega
  have hrs1' : rs1.testBit (20 + i - 15) = false := tbf (show rs1 < 2 ^ 5 by omega) (by omega)
  have hf3' : funct3.testBit (20 + i - 12) = false := tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (20 + i - 7) = false := tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (20 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e25, e20, e15, e12, e7, hrs1', hf3', hrd', hop', show 20 + i - 20 = i from by omega]

theorem rawIType_rd' (imm rs1 funct3 rd opcode : Nat) (hrd : rd < 32)
    (hf3 : funct3 < 8) (hop : opcode < 128) :
    ((rawIType imm rs1 funct3 rd opcode) &&& 3968#32) >>> 7 = BitVec.ofNat 32 rd := by
  rw [and3968_shr7]
  simp only [rawIType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 7 5 rd hrd (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 7 + i) := by omega
  have e15 : ¬ (15 ≤ 7 + i) := by omega
  have e12 : ¬ (12 ≤ 7 + i) := by omega
  have e7 : (7 ≤ 7 + i) := by omega
  have hop' : opcode.testBit (7 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hop', show 7 + i - 7 = i from by omega]

theorem rawIType_rs1 (imm rs1 funct3 rd opcode : Nat) (hrs1 : rs1 < 32)
    (hf3 : funct3 < 8) (hrd : rd < 32) (hop : opcode < 128) :
    ((rawIType imm rs1 funct3 rd opcode) &&& 1015808#32) >>> 15 = BitVec.ofNat 32 rs1 := by
  rw [and1015808_shr15]
  simp only [rawIType, rawOfNat32]
  refine ofNat32_shift_mask_eq _ 15 5 rs1 hrs1 (by norm_num) ?_
  intro i hi
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  have e20 : ¬ (20 ≤ 15 + i) := by omega
  have e15 : (15 ≤ 15 + i) := by omega
  have e12 : (12 ≤ 15 + i) := by omega
  have e7 : (7 ≤ 15 + i) := by omega
  have hf3' : funct3.testBit (15 + i - 12) = false := tbf (show funct3 < 2 ^ 3 by omega) (by omega)
  have hrd' : rd.testBit (15 + i - 7) = false := tbf (show rd < 2 ^ 5 by omega) (by omega)
  have hop' : opcode.testBit (15 + i) = false := tbf (show opcode < 2 ^ 7 by omega) (by omega)
  simp [e20, e15, e12, e7, hf3', hrd', hop', show 15 + i - 15 = i from by omega]

/-- From `x.bv = ofNat32 v`, a nonzero `v < 32` makes `x` nonzero. -/
private theorem u32_ne_zero_of_bv (x : Std.U32) (v : Nat) (hv : v < 32) (hv0 : v ≠ 0)
    (hbv : x.bv = BitVec.ofNat 32 v) : x ≠ 0#u32 := by
  intro hc; rw [hc] at hbv
  have : (0 : Nat) = v % 2 ^ 32 := by
    have := congrArg BitVec.toNat hbv; simpa [BitVec.toNat_ofNat] using this
  omega

/-! ## 3. Totality for the `immediate_op_or_x0_copyb_typed` builder. -/

/-- `immediate_op_or_x0_copyb_typed` is total for in-range register fields
    (`rs1 < 32`, `rd < 32`).  Its only extra step over `immediate_op_typed` is
    an `if i.rs1 = 0` choice of `op_zisk` operand; both arms are total. -/
theorem immediate_op_or_x0_copyb_typed_ok
    (self : riscv2zisk_context.Riscv2ZiskContext)
    (i : riscv2zisk_single_row.Rv64imLoweringInput) (op : zisk_ops.ZiskOp) (inst_size : Std.U64)
    (h1 : i.rs1.val < 32) (h3 : i.rd.val < 32) :
    ∃ ctx, riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed self i op inst_size = ok ctx := by
  obtain ⟨z0, hz0⟩ := new_ok i
  obtain ⟨z1, hz1⟩ := src_a_reg_ok z0 (UScalar.cast UScalarTy.U64 i.rs1) false (by rw [cast_u32_u64_val]; exact h1)
  obtain ⟨z2, hz2⟩ := src_b_imm_ok z1 (IScalar.hcast UScalarTy.U64 i.imm)
  obtain ⟨z3, hz3⟩ : ∃ z3, (if i.rs1 = 0#u32
      then zisk_inst_builder.ZiskInstBuilder.op_zisk z2 zisk_ops.ZiskOp.CopyB
      else zisk_inst_builder.ZiskInstBuilder.op_zisk z2 op) = ok z3 := by
    split
    · exact op_zisk_ok z2 _
    · exact op_zisk_ok z2 _
  obtain ⟨z4, hz4⟩ := store_reg_ok z3 (UScalar.hcast IScalarTy.I64 i.rd) false false
    (by rw [hcast_u32_i64_val]; exact_mod_cast Nat.zero_le _)
    (by rw [hcast_u32_i64_val]; exact_mod_cast h3)
  obtain ⟨z5, hz5⟩ := j_ok z4 (UScalar.hcast IScalarTy.I64 inst_size) (UScalar.hcast IScalarTy.I64 inst_size)
  obtain ⟨z6, hz6⟩ := build_ok z5
  obtain ⟨s1, hs1⟩ := insert_inst_ok { self with extract_marker := () } i.rom_address z6
  refine ⟨{ s1 with extract_marker := () }, ?_⟩
  rw [riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed]
  simp only [lift, Bind.bind, bind_ok, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hs1]

/-! ## 4. Generic conditional transpile reductions. -/

private theorem hcast4 : (UScalar.hcast IScalarTy.I64 4#u64 : Std.I64).val = (4 : Int) := by decide

/-- Conditional register-op transpile.  `S` is the exact self-record the
    dispatcher passes to `create_register_op_typed`; `P` the routing
    side-condition (derived from the decoded fields via `hP`). -/
theorem transpile_register_cond_of
    (raw : Std.U32) (rop : RiscvOpcode) (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (S : riscv2zisk_context.Riscv2ZiskContext)
    (P : riscv2zisk_single_row.Rv64imLoweringInput → Prop)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw = aeneas_extract.rv64im_decode.decode_r raw rop)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (input : riscv2zisk_single_row.Rv64imLoweringInput), P input →
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.create_register_op_typed S input zop 4#u64
                ok { s with extract_marker := () }))
    (hP : ∀ d, aeneas_extract.rv64im_decode.decode_r raw rop = ok d →
        P { rom_address := 0#u64, rd := d.rd, rs1 := d.rs1, rs2 := d.rs2, imm := d.imm })
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
  have hPin : P input := by rw [hinput]; exact hP decoded hdecoded
  obtain ⟨ctx0, hctx0⟩ := create_register_op_typed_ok S input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrs2b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    register_static_pins_of S input zop 4#u64 ctx0 opc m32v otv hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    create_register_op_typed_dynamic_pins S input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm input hPin, hctx0]; rfl
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

/-- Conditional immediate-op transpile through the `immediate_op_or_x0_copyb_typed`
    builder. -/
theorem transpile_immediate_copyb_of
    (raw : Std.U32) (rop : RiscvOpcode) (sh : Bool)
    (srop : riscv2zisk_single_row.Rv64imSingleRowOpcode)
    (zop : zisk_ops.ZiskOp) (opc : Std.U8) (m32v : Bool) (otv : zisk_ops.OpType)
    (S : riscv2zisk_context.Riscv2ZiskContext)
    (P : riscv2zisk_single_row.Rv64imLoweringInput → Prop)
    (hdec : aeneas_extract.rv64im_decode.decode_32_core raw
      = aeneas_extract.rv64im_decode.decode_i raw rop sh)
    (hlowop : aeneas_extract.lowering_opcode rop = ok (some srop))
    (harm : ∀ (input : riscv2zisk_single_row.Rv64imLoweringInput), P input →
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
          = (do let s ← riscv2zisk_context.Riscv2ZiskContext.immediate_op_or_x0_copyb_typed S input zop 4#u64
                ok { s with extract_marker := () }))
    (hP : ∀ d, aeneas_extract.rv64im_decode.decode_i raw rop sh = ok d →
        P { rom_address := 0#u64, rd := d.rd, rs1 := d.rs1, rs2 := d.rs2, imm := d.imm })
    (hrs1ne : ∀ input, P input → input.rs1 ≠ 0#u32)
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
  have hPin : P input := by rw [hinput]; exact hP decoded hdecoded
  have hrs1in : input.rs1 ≠ 0#u32 := hrs1ne input hPin
  obtain ⟨ctx0, hctx0⟩ := immediate_op_or_x0_copyb_typed_ok S input zop 4#u64
    (by rw [hinput]; exact hrs1b) (by rw [hinput]; exact hrdb)
  obtain ⟨zib, hzib, hop2, hext2, hm322, hsp2, hstp2⟩ :=
    immediate_x0_static_pins_of S input zop 4#u64 ctx0 opc m32v otv hrs1in hcode hm32 hot hint hfc hctx0
  obtain ⟨zib', hzib', hj1, hj2⟩ :=
    immediate_op_or_x0_copyb_typed_dynamic_pins S input zop 4#u64 ctx0 hctx0
  have hzz : zib' = zib := Option.some.inj (hzib'.symm.trans hzib)
  rw [hzz] at hj1 hj2
  obtain ⟨dext, hdext⟩ := decode_extract_ok decoded
  obtain ⟨row, hrow, hrop, hrext, hrm32, hrsp, hrstp, hrj1, hrj2, _⟩ := from_inst_ok zib.i
  have hlower : riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input defCtx input srop false
      = ok { ctx0 with extract_marker := () } := by rw [harm input hPin, hctx0]; rfl
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

/-! ## 5. ADD (register, `rd ≠ 0 ∧ rs1 ≠ 0 ∧ rs2 ≠ 0`). -/

open ZiskFv.Trusted (OP_ADD OP_OR OP_XOR)

theorem transpile_add (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) = ok ext
      ∧ ext.row.op = 10#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  refine transpile_register_cond_of _ RiscvOpcode.Add
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Add zisk_ops.ZiskOp.Add 10#u8 false zisk_ops.OpType.Binary
    { defCtx with extract_marker := (), input_precompile := none }
    (fun input => input.rd ≠ 0#u32 ∧ input.rs1 ≠ 0#u32 ∧ input.rs2 ≠ 0#u32)
    ?_ rfl ?_ ?_ rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr25,
      ZiskFv.Compliance.Decode.rawRType_opcode 0 rs2 rs1 0 rd 0x33 (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct3 0 rs2 rs1 0 rd 0x33 (by norm_num) hrd (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct7 0 rs2 rs1 0 rd 0x33 (by norm_num) hrs2 hrs1
        (by norm_num) hrd (by norm_num)]
    rfl
  · intro input hP
    obtain ⟨hrd', hrs1', hrs2'⟩ := hP
    have hprec : defCtx.input_precompile = none := rfl
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
      hprec, riscv2zisk_single_row.CSR_DMA_MEMCMP_ADDR, Bind.bind, bind_ok]
    simp [ne_eq, hrd', hrs1', hrs2',
      show ((0#u32 : Std.U32) = 2068#u32) = False from by decide]
  · intro d hd
    obtain ⟨d', hd', hrdbv, hrs1bv, hrs2bv⟩ := decode_r_fields (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) RiscvOpcode.Add
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    exact ⟨u32_ne_zero_of_bv d.rd rd hrd hrd0
            (by rw [hrdbv]; exact rawRType_rd 0 rs2 rs1 0 rd 0x33 hrd (by norm_num) (by norm_num)),
          u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
            (by rw [hrs1bv]; exact rawRType_rs1 0 rs2 rs1 0 rd 0x33 hrs1 (by norm_num) hrd (by norm_num)),
          u32_ne_zero_of_bv d.rs2 rs2 hrs2 hrs20
            (by rw [hrs2bv]; exact rawRType_rs2 0 rs2 rs1 0 rd 0x33 hrs2 hrs1 (by norm_num) hrd (by norm_num))⟩

theorem add_decode_fields_of_binding (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawRType 0 rs2 rs1 0 rd 0x33)) :
    msg.op = OP_ADD ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 0 rd 0x33)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    transpile_add rd rs1 rs2 hrd hrs1 hrs2 hrd0 hrs10 hrs20
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 10#u8 OP_ADD ext (by simp [OP_ADD]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_add_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_add trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = rawRType 0 rs2 rs1 0 rd 0x33) :
    ZiskFv.Compliance.Decode_add trace i c := by
  set ext := (transpile_add rd rs1 rs2 hrd hrs1 hrs2 hrd0 hrs10 hrs20).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    (transpile_add rd rs1 rs2 hrd hrs1 hrs2 hrd0 hrs10 hrs20).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_add_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (rawRType 0 rs2 rs1 0 rd 0x33) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 10#u8 OP_ADD ext
      (by simp [OP_ADD]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

structure RawDecode_add {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_add trace i)
    (rawProgram : Fin n → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  rd : Nat
  rs1 : Nat
  rs2 : Nat
  hrd : rd < 32
  hrs1 : rs1 < 32
  hrs2 : rs2 < 32
  hrd0 : rd ≠ 0
  hrs10 : rs1 ≠ 0
  hrs20 : rs2 ≠ 0
  hLine : ∀ j : Fin n,
      (trace.program j).line
        = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      rawProgram j = rawRType 0 rs2 rs1 0 rd 0x33

noncomputable def Decode_add_from_rawProgram_b {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_add trace i)
    (rawProgram : Fin n → BitVec 32) (hbind : ProgramBinding trace rawProgram)
    (b : RawDecode_add trace i c rawProgram) : ZiskFv.Compliance.Decode_add trace i c :=
  Decode_add_from_rawProgram trace i c b.h_idx b.rd b.rs1 b.rs2 b.hrd b.hrs1 b.hrs2
    b.hrd0 b.hrs10 b.hrs20 rawProgram hbind b.hLine

/-! ## 6. OR (register, `rs1 ≠ 0 ∧ rs2 ≠ 0`). -/

theorem transpile_or (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) = ok ext
      ∧ ext.row.op = 15#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  refine transpile_register_cond_of _ RiscvOpcode.Or
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Or zisk_ops.ZiskOp.Or 15#u8 false zisk_ops.OpType.Binary
    { defCtx with extract_marker := () }
    (fun input => input.rs1 ≠ 0#u32 ∧ input.rs2 ≠ 0#u32)
    ?_ rfl ?_ ?_ rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_shr25,
      ZiskFv.Compliance.Decode.rawRType_opcode 0 rs2 rs1 6 rd 0x33 (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct3 0 rs2 rs1 6 rd 0x33 (by norm_num) hrd (by norm_num),
      ZiskFv.Compliance.Decode.rawRType_funct7 0 rs2 rs1 6 rd 0x33 (by norm_num) hrs2 hrs1
        (by norm_num) hrd (by norm_num)]
    rfl
  · intro input hP
    obtain ⟨hrs1', hrs2'⟩ := hP
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input, Bind.bind, bind_ok]
    rw [if_neg hrs1', if_neg hrs2']
  · intro d hd
    obtain ⟨d', hd', _, hrs1bv, hrs2bv⟩ := decode_r_fields (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) RiscvOpcode.Or
    have hdd : d = d' := Result.ok.inj (hd.symm.trans hd'); subst hdd
    exact ⟨u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
            (by rw [hrs1bv]; exact rawRType_rs1 0 rs2 rs1 6 rd 0x33 hrs1 (by norm_num) hrd (by norm_num)),
          u32_ne_zero_of_bv d.rs2 rs2 hrs2 hrs20
            (by rw [hrs2bv]; exact rawRType_rs2 0 rs2 rs1 6 rd 0x33 hrs2 hrs1 (by norm_num) hrd (by norm_num))⟩

theorem or_decode_fields_of_binding (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawRType 0 rs2 rs1 6 rd 0x33)) :
    msg.op = OP_OR ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawRType 0 rs2 rs1 6 rd 0x33)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    transpile_or rd rs1 rs2 hrd hrs1 hrs2 hrs10 hrs20
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 15#u8 OP_OR ext (by simp [OP_OR]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_or_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_or trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd rs1 rs2 : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs2 : rs2 < 32)
    (hrs10 : rs1 ≠ 0) (hrs20 : rs2 ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = rawRType 0 rs2 rs1 6 rd 0x33) :
    ZiskFv.Compliance.Decode_or trace i c := by
  set ext := (transpile_or rd rs1 rs2 hrd hrs1 hrs2 hrs10 hrs20).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    (transpile_or rd rs1 rs2 hrd hrs1 hrs2 hrs10 hrs20).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_or_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (rawRType 0 rs2 rs1 6 rd 0x33) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 15#u8 OP_OR ext
      (by simp [OP_OR]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

structure RawDecode_or {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_or trace i)
    (rawProgram : Fin n → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  rd : Nat
  rs1 : Nat
  rs2 : Nat
  hrd : rd < 32
  hrs1 : rs1 < 32
  hrs2 : rs2 < 32
  hrs10 : rs1 ≠ 0
  hrs20 : rs2 ≠ 0
  hLine : ∀ j : Fin n,
      (trace.program j).line
        = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      rawProgram j = rawRType 0 rs2 rs1 6 rd 0x33

noncomputable def Decode_or_from_rawProgram_b {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_or trace i)
    (rawProgram : Fin n → BitVec 32) (hbind : ProgramBinding trace rawProgram)
    (b : RawDecode_or trace i c rawProgram) : ZiskFv.Compliance.Decode_or trace i c :=
  Decode_or_from_rawProgram trace i c b.h_idx b.rd b.rs1 b.rs2 b.hrd b.hrs1 b.hrs2
    b.hrs10 b.hrs20 rawProgram hbind b.hLine

/-! ## 7. ADDI (immediate, `rd ≠ 0 ∧ imm ≠ 0 ∧ rs1 ≠ 0`; `imm ≠ 0` threaded). -/

theorem transpile_addi (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0)
    (himm : ∀ d, aeneas_extract.rv64im_decode.decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 0 rd 0x13)) = ok ext
      ∧ ext.row.op = 10#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  refine transpile_immediate_copyb_of _ RiscvOpcode.Addi false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Addi zisk_ops.ZiskOp.Add 10#u8 false zisk_ops.OpType.Binary
    { defCtx with extract_marker := () }
    (fun input => input.rd ≠ 0#u32 ∧ input.imm ≠ 0#i32 ∧ input.rs1 ≠ 0#u32)
    ?_ rfl ?_ ?_ (fun _ hP => hP.2.2) rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 0 rd 0x13 (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 0 rd 0x13 (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro input hP
    obtain ⟨hrd', himm', _⟩ := hP
    simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input, Bind.bind, bind_ok]
    rw [if_neg hrd', if_neg himm']
  · intro d hd
    obtain ⟨hrdbv, hrs1bv⟩ :=
      decode_i_rd_rs1_bv (toU32 (rawIType imm rs1 0 rd 0x13)) RiscvOpcode.Addi false d hd
    exact ⟨u32_ne_zero_of_bv d.rd rd hrd hrd0
            (by rw [hrdbv]; exact rawIType_rd' imm rs1 0 rd 0x13 hrd (by norm_num) (by norm_num)),
          himm d hd,
          u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
            (by rw [hrs1bv]; exact rawIType_rs1 imm rs1 0 rd 0x13 hrs1 (by norm_num) hrd (by norm_num))⟩

theorem addi_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32)
    (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0)
    (himm : ∀ d, aeneas_extract.rv64im_decode.decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawIType imm rs1 0 rd 0x13)) :
    msg.op = OP_ADD ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 0 rd 0x13)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    transpile_addi rd rs1 imm hrd hrs1 hrd0 hrs10 himm
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 10#u8 OP_ADD ext (by simp [OP_ADD]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_addi_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addi trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrd0 : rd ≠ 0) (hrs10 : rs1 ≠ 0)
    (himm : ∀ d, aeneas_extract.rv64im_decode.decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
      RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = rawIType imm rs1 0 rd 0x13) :
    ZiskFv.Compliance.Decode_addi trace i c := by
  set ext := (transpile_addi rd rs1 imm hrd hrs1 hrd0 hrs10 himm).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    (transpile_addi rd rs1 imm hrd hrs1 hrd0 hrs10 himm).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_addi_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (rawIType imm rs1 0 rd 0x13) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 10#u8 OP_ADD ext
      (by simp [OP_ADD]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

structure RawDecode_addi {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addi trace i)
    (rawProgram : Fin n → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  rd : Nat
  rs1 : Nat
  imm : Nat
  hrd : rd < 32
  hrs1 : rs1 < 32
  hrd0 : rd ≠ 0
  hrs10 : rs1 ≠ 0
  himm : ∀ d, aeneas_extract.rv64im_decode.decode_i (toU32 (rawIType imm rs1 0 rd 0x13))
    RiscvOpcode.Addi false = ok d → d.imm ≠ 0#i32
  hLine : ∀ j : Fin n,
      (trace.program j).line
        = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      rawProgram j = rawIType imm rs1 0 rd 0x13

noncomputable def Decode_addi_from_rawProgram_b {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_addi trace i)
    (rawProgram : Fin n → BitVec 32) (hbind : ProgramBinding trace rawProgram)
    (b : RawDecode_addi trace i c rawProgram) : ZiskFv.Compliance.Decode_addi trace i c :=
  Decode_addi_from_rawProgram trace i c b.h_idx b.rd b.rs1 b.imm b.hrd b.hrs1 b.hrd0 b.hrs10 b.himm
    rawProgram hbind b.hLine

/-! ## 8. XORI / ORI (immediate, dispatcher-unconditional; op-arm needs `rs1 ≠ 0`). -/

theorem transpile_xori (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 4 rd 0x13)) = ok ext
      ∧ ext.row.op = 16#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  refine transpile_immediate_copyb_of _ RiscvOpcode.Xori false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Xori zisk_ops.ZiskOp.Xor 16#u8 false zisk_ops.OpType.Binary
    { defCtx with extract_marker := () }
    (fun input => input.rs1 ≠ 0#u32)
    ?_ rfl (fun _ _ => rfl) ?_ (fun _ hP => hP) rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 4 rd 0x13 (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 4 rd 0x13 (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro d hd
    obtain ⟨_, hrs1bv⟩ :=
      decode_i_rd_rs1_bv (toU32 (rawIType imm rs1 4 rd 0x13)) RiscvOpcode.Xori false d hd
    exact u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
      (by rw [hrs1bv]; exact rawIType_rs1 imm rs1 4 rd 0x13 hrs1 (by norm_num) hrd (by norm_num))

theorem xori_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawIType imm rs1 4 rd 0x13)) :
    msg.op = OP_XOR ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 4 rd 0x13)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    transpile_xori rd rs1 imm hrd hrs1 hrs10
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 16#u8 OP_XOR ext (by simp [OP_XOR]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_xori_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_xori trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = rawIType imm rs1 4 rd 0x13) :
    ZiskFv.Compliance.Decode_xori trace i c := by
  set ext := (transpile_xori rd rs1 imm hrd hrs1 hrs10).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    (transpile_xori rd rs1 imm hrd hrs1 hrs10).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_xori_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (rawIType imm rs1 4 rd 0x13) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 16#u8 OP_XOR ext
      (by simp [OP_XOR]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

structure RawDecode_xori {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_xori trace i)
    (rawProgram : Fin n → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  rd : Nat
  rs1 : Nat
  imm : Nat
  hrd : rd < 32
  hrs1 : rs1 < 32
  hrs10 : rs1 ≠ 0
  hLine : ∀ j : Fin n,
      (trace.program j).line
        = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      rawProgram j = rawIType imm rs1 4 rd 0x13

noncomputable def Decode_xori_from_rawProgram_b {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_xori trace i)
    (rawProgram : Fin n → BitVec 32) (hbind : ProgramBinding trace rawProgram)
    (b : RawDecode_xori trace i c rawProgram) : ZiskFv.Compliance.Decode_xori trace i c :=
  Decode_xori_from_rawProgram trace i c b.h_idx b.rd b.rs1 b.imm b.hrd b.hrs1 b.hrs10
    rawProgram hbind b.hLine

theorem transpile_ori (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0) :
    ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 6 rd 0x13)) = ok ext
      ∧ ext.row.op = 15#u8 ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
      ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
      ∧ ext.row.jmp_offset1 = UScalar.hcast IScalarTy.I64 4#u64
      ∧ ext.row.jmp_offset2 = UScalar.hcast IScalarTy.I64 4#u64 := by
  refine transpile_immediate_copyb_of _ RiscvOpcode.Ori false
    riscv2zisk_single_row.Rv64imSingleRowOpcode.Ori zisk_ops.ZiskOp.Or 15#u8 false zisk_ops.OpType.Binary
    { defCtx with extract_marker := () }
    (fun input => input.rs1 ≠ 0#u32)
    ?_ rfl (fun _ _ => rfl) ?_ (fun _ hP => hP) rfl rfl rfl (by intro h; cases h) (by intro h; cases h)
  · simp only [aeneas_extract.rv64im_decode.decode_32_core, lift, bind_assoc, Bind.bind, bind_ok,
      ZiskFv.Compliance.Decode.toU32_and127, ZiskFv.Compliance.Decode.toU32_and7,
      ZiskFv.Compliance.Decode.toU32_shr12, ZiskFv.Compliance.Decode.toU32_ofNat,
      ZiskFv.Compliance.Decode.rawIType_opcode imm rs1 6 rd 0x13 (by norm_num),
      ZiskFv.Compliance.Decode.rawIType_funct3 imm rs1 6 rd 0x13 (by norm_num) hrd (by norm_num)]
    all_goals rfl
  · intro d hd
    obtain ⟨_, hrs1bv⟩ :=
      decode_i_rd_rs1_bv (toU32 (rawIType imm rs1 6 rd 0x13)) RiscvOpcode.Ori false d hd
    exact u32_ne_zero_of_bv d.rs1 rs1 hrs1 hrs10
      (by rw [hrs1bv]; exact rawIType_rs1 imm rs1 6 rd 0x13 hrs1 (by norm_num) hrd (by norm_num))

theorem ori_decode_fields_of_binding (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0)
    (line : FGL) (msg : ZiskRomMessage FGL)
    (hbind : msg = romMessageOfRaw line (rawIType imm rs1 6 rd 0x13)) :
    msg.op = OP_OR ∧ msg.jmp_offset1 = 4 ∧ msg.jmp_offset2 = 4
      ∧ ∃ ext, extract_transpile_rv64im_raw (toU32 (rawIType imm rs1 6 rd 0x13)) = ok ext
          ∧ ext.row.is_external_op = true ∧ ext.row.m32 = false
          ∧ ext.row.set_pc = false ∧ ext.row.store_pc = false
          ∧ msg.flags = packFlags (romFlagBitsOfExtract ext.row) := by
  obtain ⟨ext, hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    transpile_ori rd rs1 imm hrd hrs1 hrs10
  obtain ⟨ho, hjo1, hjo2, hf⟩ :=
    register_decode_fields_of_binding line msg _ 15#u8 OP_OR ext (by simp [OP_OR]) hok hop hj1 hj2 hbind
  exact ⟨ho, hjo1, hjo2, ext, hok, hieo, hm32, hsetpc, hstorepc, hf⟩

noncomputable def Decode_ori_from_rawProgram {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_ori trace i)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (rd rs1 imm : Nat) (hrd : rd < 32) (hrs1 : rs1 < 32) (hrs10 : rs1 ≠ 0)
    (rawProgram : Fin n → BitVec 32)
    (hbind : ProgramBinding trace rawProgram)
    (hLine : ∀ j : Fin n,
        (trace.program j).line
          = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
        rawProgram j = rawIType imm rs1 6 rd 0x13) :
    ZiskFv.Compliance.Decode_ori trace i c := by
  set ext := (transpile_ori rd rs1 imm hrd hrs1 hrs10).choose with hext
  obtain ⟨hok, hop, hieo, hm32, hsetpc, hstorepc, hj1, hj2⟩ :=
    (transpile_ori rd rs1 imm hrd hrs1 hrs10).choose_spec
  refine ZiskFv.Compliance.RomDecodeBinding.Decode_ori_of_program trace i c h_idx
    (romFlagBitsOfExtract ext.row) hieo hm32 hsetpc hstorepc ?_
  intro j hline
  have hbk : trace.program j
      = romMessageOfRaw (trace.program j).line (rawIType imm rs1 6 rd 0x13) :=
    (hbind j).trans (congrArg (romMessageOfRaw (trace.program j).line) (hLine j hline))
  obtain ⟨ho, hj1', hj2', hflags⟩ :=
    register_decode_fields_of_binding (trace.program j).line (trace.program j) _ 15#u8 OP_OR ext
      (by simp [OP_OR]) hok hop hj1 hj2 hbk
  exact ⟨ho, hj1', hj2', hflags⟩

structure RawDecode_ori {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_ori trace i)
    (rawProgram : Fin n → BitVec 32) where
  h_idx : i.val + 1 < trace.mainTable.table.length
  rd : Nat
  rs1 : Nat
  imm : Nat
  hrd : rd < 32
  hrs1 : rs1 < 32
  hrs10 : rs1 ≠ 0
  hLine : ∀ j : Fin n,
      (trace.program j).line
        = (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val →
      rawProgram j = rawIType imm rs1 6 rd 0x13

noncomputable def Decode_ori_from_rawProgram_b {n : Nat} (trace : ZiskFv.Compliance.AcceptedZiskTrace n)
    (i : Fin trace.numInstructions) (c : ZiskFv.Compliance.Claim_ori trace i)
    (rawProgram : Fin n → BitVec 32) (hbind : ProgramBinding trace rawProgram)
    (b : RawDecode_ori trace i c rawProgram) : ZiskFv.Compliance.Decode_ori trace i c :=
  Decode_ori_from_rawProgram trace i c b.h_idx b.rd b.rs1 b.imm b.hrd b.hrs1 b.hrs10
    rawProgram hbind b.hLine

section AxiomAudit
#print axioms transpile_add
#print axioms Decode_add_from_rawProgram
#print axioms transpile_or
#print axioms Decode_or_from_rawProgram
#print axioms transpile_addi
#print axioms Decode_addi_from_rawProgram
#print axioms transpile_xori
#print axioms Decode_xori_from_rawProgram
#print axioms transpile_ori
#print axioms Decode_ori_from_rawProgram
end AxiomAudit

end ZiskFv.Compliance.RawProgramBinding
