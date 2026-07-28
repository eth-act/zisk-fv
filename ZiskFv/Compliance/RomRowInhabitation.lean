/-
ZiskFv/Compliance/RomRowInhabitation.lean  (eth-act/zisk-fv#61, Phase-0 step S3)

INHABITATION for the ROM-row serialization of `Compliance/RomRowSerialization.lean`.

S2 proved that a serialization is faithfully transcribed from
`zisk/state-machines/rom/src/rom.rs:204-260`.  It did NOT prove that any
committed ROM row IS the serialization of the lowering of a raw 32-bit RISC-V
word.  Without that, a `ProgramBinding`-style premise could be satisfied by
nothing and every theorem over it would be green and empty.

This file runs concrete 32-bit words through the REAL production lowerer
`zisk_core.aeneas_extract.extract_transpile_rv64im_raw`
(`trust/aeneas/ProductionM2.lean:3645`), serializes the result with S2's
`romRowOf`, and compares against rows that already exist in the tree.

Kernel-sound: no `axiom` / `sorry` / `native_decide` / `bv_decide`.

## The ROM-layout (`line`) question, stated explicitly

`extract_transpile_rv64im_raw` hard-codes `rom_address := 0#u64`
(`ProductionM2.lean:3656`), so its extract always has `paddr = 0`, while a
committed ROM row sits at its real address (`rom.rs:238` emits `line :=
F::from_u64(inst.paddr)`).  S2 deliberately made `romRowOf` read `e.paddr`
rather than take `line` as a parameter, because June's parameterized
`serializeExtract` left the eleventh slot unconstrained.

The resolution here is NOT to drop the slot.  `romMessageOfRawAt` reinstates the
address by overriding `paddr`, and `ld_rom_address_reaches_only_paddr` /
`sd_rom_address_reaches_only_paddr` PROVE that this override is exactly what the
production lowerer would have produced had it been handed that address: for the
load and store arms, `rom_address` reaches the emitted instruction only through
`ZiskInstBuilder::new`'s `paddr` (`ProductionM2.lean:2164-2177`) and
`insert_inst`'s discarded key (`:2192`).  Those theorems are stated with the ROM
address universally quantified, so a future ZisK making any other row field
pc-dependent breaks them.

What the layout map still does NOT pin: that entry `k` sits where the *binary*
places word `k`.  That is the meaning of the caller's address map, not a theorem
here, and it stays a named residual (design note §6).

## Result of the spike (read this before reusing anything below)

* INHABITED, against rows already committed in `SdLdSpinWitness.lean`:
  the LD row `sdLdLdProgramRow` (the one with `b_src_ind := true`, which
  falsifies June's `SRC_IND = 3` literal) and the SD row `sdLdSdProgramRow`.
* INHABITED, sign path: `ld x5, -8(x2)` — the `i64` reinterpretation of
  `rom.rs:226-236`, where June's second defect lived.  Its committed counterpart
  is written here (`ldNegEightProgramRow`); no negative-offset load exists
  elsewhere in the tree.
* NOT INHABITED: the four ADDI/SLLI rows and the JAL row of the SAME witness.
  See §6.  This is a property of the hand-built witness, not of the ROM emitter:
  those rows were written to satisfy the AIR, and they differ from what ZisK's
  transpiler emits for the corresponding instructions.  `ProgramBinding` is
  therefore FALSE for `sdLdProgram` as it stands.
-/
import ZiskFv.Compliance.RomRowSerialization
import ZiskFv.Compliance.AeneasBridgeTrust.Decode.Leaves

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks

namespace ZiskFv.Compliance.RomRowInhabitation

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.Compliance.Decode (toU32)
open ZiskFv.Compliance.RomRowSerialization
open zisk_core.aeneas_extract (ZiskInstExtract)
open zisk_inst_builder (ZiskInstBuilder)

set_option maxRecDepth 100000

/-! ## 1. The two `Usize` register-range constants, reduced past `System.Platform.numBits`

`REGS_IN_MAIN_FROM` / `REGS_IN_MAIN_TO` are `Std.Usize`, whose width is the
OPAQUE `System.Platform.numBits`, so the builder's register-class comparisons do
not reduce.  Both constants cast to the same fixed-width value on either
platform, which is what the four lemmas below establish; from there the
comparisons are decidable. -/

theorem cast_regs_from_u64 :
    (UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_FROM : Std.U64) = 1#u64 := by
  simp only [zisk_registers.REGS_IN_MAIN_FROM, UScalar.cast, BitVec.truncate_eq_setWidth]
  apply congrArg UScalar.mk
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rfl

theorem cast_regs_to_u64 :
    (UScalar.cast UScalarTy.U64 zisk_registers.REGS_IN_MAIN_TO : Std.U64) = 31#u64 := by
  simp only [zisk_registers.REGS_IN_MAIN_TO, UScalar.cast, BitVec.truncate_eq_setWidth]
  apply congrArg UScalar.mk
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rfl

theorem hcast_regs_from_i64 :
    (UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_FROM : Std.I64) = 1#i64 := by
  simp only [zisk_registers.REGS_IN_MAIN_FROM, UScalar.hcast, BitVec.truncate_eq_setWidth]
  apply congrArg IScalar.mk
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rfl

theorem hcast_regs_to_i64 :
    (UScalar.hcast IScalarTy.I64 zisk_registers.REGS_IN_MAIN_TO : Std.I64) = 31#i64 := by
  simp only [zisk_registers.REGS_IN_MAIN_TO, UScalar.hcast, BitVec.truncate_eq_setWidth]
  apply congrArg IScalar.mk
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  rfl

/-! ## 2. Builder steps on the in-main-register-file branch

`src_a_reg` / `src_b_reg` / `store_reg` each have three register classes
(`reg = 0` → immediate zero, out-of-range → `SRC_MEM` / `STORE_MEM`, in range →
`SRC_REG` / `STORE_REG`).  With the numBits comparisons reduced by §1 the class
is decidable, so these lemmas give the exact resulting builder rather than the
"pins are preserved" statement of `Extraction/Helpers.lean`. -/

theorem src_a_reg_in_main (self : ZiskInstBuilder) (reg : Std.U64)
    (hne : ¬ (reg = 0#u64)) (hlo : ¬ (reg < 1#u64)) (hhi : ¬ (31#u64 < reg)) :
    ZiskInstBuilder.src_a_reg self reg false
      = ok { i :=
          { self.i with
            a_src := zisk_inst.SRC_REG, a_use_sp_imm1 := 0#u64, a_offset_imm0 := reg } } := by
  simp only [ZiskInstBuilder.src_a_reg, lift, Bind.bind, bind_ok,
    cast_regs_from_u64, cast_regs_to_u64, gt_iff_lt]
  rw [if_neg hne, if_neg hlo, if_neg hhi]
  simp

theorem src_b_reg_in_main (self : ZiskInstBuilder) (reg : Std.U64)
    (hne : ¬ (reg = 0#u64)) (hlo : ¬ (reg < 1#u64)) (hhi : ¬ (31#u64 < reg)) :
    ZiskInstBuilder.src_b_reg self reg false
      = ok { i :=
          { self.i with
            b_src := zisk_inst.SRC_REG, b_use_sp_imm1 := 0#u64, b_offset_imm0 := reg } } := by
  simp only [ZiskInstBuilder.src_b_reg, lift, Bind.bind, bind_ok,
    cast_regs_from_u64, cast_regs_to_u64, gt_iff_lt]
  rw [if_neg hne, if_neg hlo, if_neg hhi]
  simp

theorem store_reg_in_main (self : ZiskInstBuilder) (off : Std.I64)
    (hne : ¬ (off = 0#i64)) (hlo : ¬ (off < 1#i64)) (hhi : ¬ (31#i64 < off)) :
    ZiskInstBuilder.store_reg self off false false
      = ok { i :=
          { self.i with
            store_pc := false, store_use_sp := false,
            store := zisk_inst.STORE_REG, store_offset := off } } := by
  simp only [ZiskInstBuilder.store_reg, lift, Bind.bind, bind_ok,
    hcast_regs_from_i64, hcast_regs_to_i64, gt_iff_lt]
  rw [if_neg hne, if_neg hlo, if_neg hhi]

/-! ## 3. The LD lowering, with the ROM address left free

`ProductionM2.lean:3432-3437` sends `Ld` to `load_op_typed … CopyB 8 4`, i.e.
`load_op_with_reg_offset … 0#i64` (`:2771-2780`).  The theorem below computes the
whole arm, for ANY ROM address `a`: it is the load-family analogue of the `_pins`
lemmas of `Extraction/Helpers.lean`, but total — every field of the emitted
`ZiskInst` is pinned, not just the five static ones. -/

/-- The `ZiskInst` `load_op_typed … CopyB 8 4` builds for a load whose `rs1` and
    `rd` are both in the main register file: `a` is the ROM address, `aoff` the
    `rs1` index, `boff` the sign-extended displacement, `soff` the `rd` index. -/
def ldInstAt (a aoff boff : Std.U64) (soff : Std.I64) : zisk_inst.ZiskInst where
  paddr := a
  store_pc := false
  store_use_sp := false
  store := zisk_inst.STORE_REG
  store_offset := soff
  set_pc := false
  is_precompiled := false
  ind_width := 8#u64
  «end» := false
  a_src := zisk_inst.SRC_REG
  a_use_sp_imm1 := 0#u64
  a_offset_imm0 := aoff
  b_src := zisk_inst.SRC_IND
  b_use_sp_imm1 := 0#u64
  b_offset_imm0 := boff
  jmp_offset1 := 4#i64
  jmp_offset2 := 4#i64
  is_external_op := false
  op := 1#u8
  op_type := zisk_inst.ZiskOperationType.Internal
  m32 := false
  input_size := 0#u64
  sorted_pc_list_index := 0#usize

/-- The empty lowering context `extract_transpile_rv64im_raw` starts from
    (`ProductionM2.lean:3660-3667`). -/
def emptyCtx : riscv2zisk_context.Riscv2ZiskContext where
  extract_inst := none
  extract_marker := ()
  input_precompile := none
  output_precompile := none
  input_precompile_reg := none
  output_precompile_reg := none

set_option maxHeartbeats 2000000 in
/-- **The LD arm, computed.**  `a` is universally quantified, so the statement
    also says exactly how the ROM address reaches the row: through `paddr` and
    nothing else. -/
theorem ld_lowering_ctx (a : Std.U64) (rd rs1 rs2 : Std.U32) (imm : Std.I32)
    (hrs1ne : ¬ ((UScalar.cast UScalarTy.U64 rs1 : Std.U64) = 0#u64))
    (hrs1lo : ¬ ((UScalar.cast UScalarTy.U64 rs1 : Std.U64) < 1#u64))
    (hrs1hi : ¬ ((31#u64 : Std.U64) < (UScalar.cast UScalarTy.U64 rs1 : Std.U64)))
    (hadd : ((UScalar.hcast IScalarTy.I64 rd : Std.I64) + (0#i64 : Std.I64))
              = ok (UScalar.hcast IScalarTy.I64 rd : Std.I64))
    (hrdne : ¬ ((UScalar.hcast IScalarTy.I64 rd : Std.I64) = 0#i64))
    (hrdlo : ¬ ((UScalar.hcast IScalarTy.I64 rd : Std.I64) < 1#i64))
    (hrdhi : ¬ ((31#i64 : Std.I64) < (UScalar.hcast IScalarTy.I64 rd : Std.I64))) :
    riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input emptyCtx
        { rom_address := a, rd := rd, rs1 := rs1, rs2 := rs2, imm := imm }
        riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false
      = ok { emptyCtx with
              extract_inst := some
                { i := ldInstAt a (UScalar.cast UScalarTy.U64 rs1)
                        (IScalar.hcast UScalarTy.U64 imm) (UScalar.hcast IScalarTy.I64 rd) } } := by
  simp only [riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input,
    riscv2zisk_context.Riscv2ZiskContext.load_op_typed,
    riscv2zisk_context.Riscv2ZiskContext.load_op_with_reg_offset,
    ZiskInstBuilder.new_for_rv64im_lowering, ZiskInstBuilder.new,
    ZiskInstBuilder.Insts.CoreDefaultDefault.default,
    zisk_inst.ZiskInst.Insts.CoreDefaultDefault.default,
    ZiskInstBuilder.ind_width, ZiskInstBuilder.src_b_ind,
    ZiskInstBuilder.op_zisk, ZiskInstBuilder.set_runtime_op_fields,
    ZiskInstBuilder.j, ZiskInstBuilder.build,
    riscv2zisk_context.Riscv2ZiskContext.insert_inst,
    src_a_reg_in_main _ _ hrs1ne hrs1lo hrs1hi,
    store_reg_in_main _ _ hrdne hrdlo hrdhi,
    hadd, lift, Bind.bind, bind_ok]
  rfl

/-- The extract the ROM emitter reads, for the same row. -/
def ldExtractAt (a aoff boff : Std.U64) (soff : Std.I64) : ZiskInstExtract where
  paddr := a
  store_pc := false
  store_use_sp := false
  store := zisk_inst.STORE_REG
  store_offset := soff
  set_pc := false
  is_precompiled := false
  ind_width := 8#u64
  «end» := false
  a_src := zisk_inst.SRC_REG
  a_use_sp_imm1 := 0#u64
  a_offset_imm0 := aoff
  b_src := zisk_inst.SRC_IND
  b_use_sp_imm1 := 0#u64
  b_offset_imm0 := boff
  jmp_offset1 := 4#i64
  jmp_offset2 := 4#i64
  is_external_op := false
  op := 1#u8
  op_type_id := 1#u32
  m32 := false
  input_size := 0#u64
  sorted_pc_list_index := 0#usize

theorem from_inst_ldInstAt (a aoff boff : Std.U64) (soff : Std.I64) :
    aeneas_extract.ZiskInstExtract.from_inst (ldInstAt a aoff boff soff)
      = ok (ldExtractAt a aoff boff soff) := rfl

/-- **The ROM address reaches the LD row only through `paddr`.**  Overriding
    `paddr` on the `rom_address := 0` extract gives back exactly the extract the
    lowerer produces when handed `a`.  This is what licenses `romMessageOfRawAt`
    below to reinstate an address that `extract_transpile_rv64im_raw` hard-codes
    to `0`; a future ZisK making any other row field pc-dependent would break
    this proof rather than pass silently. -/
theorem ld_rom_address_reaches_only_paddr (a : Std.U64) (rd rs1 rs2 : Std.U32) (imm : Std.I32)
    (hrs1ne : ¬ ((UScalar.cast UScalarTy.U64 rs1 : Std.U64) = 0#u64))
    (hrs1lo : ¬ ((UScalar.cast UScalarTy.U64 rs1 : Std.U64) < 1#u64))
    (hrs1hi : ¬ ((31#u64 : Std.U64) < (UScalar.cast UScalarTy.U64 rs1 : Std.U64)))
    (hadd : ((UScalar.hcast IScalarTy.I64 rd : Std.I64) + (0#i64 : Std.I64))
              = ok (UScalar.hcast IScalarTy.I64 rd : Std.I64))
    (hrdne : ¬ ((UScalar.hcast IScalarTy.I64 rd : Std.I64) = 0#i64))
    (hrdlo : ¬ ((UScalar.hcast IScalarTy.I64 rd : Std.I64) < 1#i64))
    (hrdhi : ¬ ((31#i64 : Std.I64) < (UScalar.hcast IScalarTy.I64 rd : Std.I64))) :
    (do
      let ctx ←
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input emptyCtx
          { rom_address := a, rd := rd, rs1 := rs1, rs2 := rs2, imm := imm }
          riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false
      let zib ← core.option.Option.unwrap ctx.extract_inst
      aeneas_extract.ZiskInstExtract.from_inst zib.i)
      = (do
      let e ← (do
        let ctx ←
          riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input emptyCtx
            { rom_address := 0#u64, rd := rd, rs1 := rs1, rs2 := rs2, imm := imm }
            riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false
        let zib ← core.option.Option.unwrap ctx.extract_inst
        aeneas_extract.ZiskInstExtract.from_inst zib.i)
      ok { e with paddr := a }) := by
  rw [ld_lowering_ctx a rd rs1 rs2 imm hrs1ne hrs1lo hrs1hi hadd hrdne hrdlo hrdhi,
      ld_lowering_ctx 0#u64 rd rs1 rs2 imm hrs1ne hrs1lo hrs1hi hadd hrdne hrdlo hrdhi]
  rfl

/-! ## 4. From a raw 32-bit word to a ROM message -/

/-- The eleven-slot ROM message ZisK's `compute_trace_rom` emits for the word
    `raw` sitting at ROM address `addr`.  The `paddr` override is licensed by
    `ld_rom_address_reaches_only_paddr` / `sd_rom_address_reaches_only_paddr`,
    not assumed.  A word the lowerer rejects still returns `ok` with the default
    row and `accepted := false` (`ProductionM2.lean:3652-3653`), so a caller must
    also demand `accepted = true`; the witnesses below all establish that. -/
def romMessageOfRawAt (addr : Std.U64) (raw : BitVec 32) : Result (ZiskRomMessage FGL) := do
  let r ← aeneas_extract.extract_transpile_rv64im_raw (toU32 raw)
  ok (romRowOf { r.row with paddr := addr })

/-! ## 5. Witness 1 — the committed LD row of `SdLdSpinWitness`

`ld x3, 0(x1)` is `0x0000B183`.  `SdLdSpinWitness.sdLdLdProgramRow` sits at ROM
address 20 and is the row whose `b_src_ind` bit falsifies June's `SRC_IND = 3`
literal (design note §3.1).  Nothing about that row was written for this proof:
it is a hand-built AIR witness from `#221`.

`ldX3ZeroX1_unfold` is the step that runs the extracted decoder: it reduces
`decode_32_core` on a literal word and reads off `rd = 3`, `rs1 = 1`, `rs2 = 0`,
`imm = 0`.  The lowering itself does NOT reduce — `Std.Usize`'s width is the
opaque `System.Platform.numBits` — which is why §1-§3 exist. -/

/-- `ld x3, 0(x1)`. -/
def rawLdX3ZeroX1 : BitVec 32 := BitVec.ofNat 32 0x0000B183

/-- What the extracted decoder reports for `ld x3, 0(x1)`. -/
def ldX3ZeroX1Decode : aeneas_extract.Rv64imDecodeExtract where
  supported := true
  opcode_id := 59#u32
  format_id := 1#u32
  funct3 := 3#u32
  funct7 := 0#u32
  rd := 3#u32
  rs1 := 1#u32
  rs2 := 0#u32
  imm := 0#i32
  pred := 0#u32
  succ := 0#u32

/-- `store_reg`'s `rd + reg_offset` with `reg_offset = 0` (`ProductionM2.lean:2757`),
    for `rd = x3`.  Stated as a named lemma because elaborating it inline as a
    `rfl` argument overflows the elaborator's stack. -/
theorem hcast_x3_add_zero :
    ((UScalar.hcast IScalarTy.I64 (3#u32) : Std.I64) + (0#i64 : Std.I64))
      = ok (UScalar.hcast IScalarTy.I64 (3#u32) : Std.I64) := rfl

set_option maxHeartbeats 2000000 in
theorem ldX3ZeroX1_unfold :
    aeneas_extract.extract_transpile_rv64im_raw (toU32 rawLdX3ZeroX1)
      = (do
      let ctx ←
        riscv2zisk_single_row.Riscv2ZiskContext.lower_rv64im_single_row_input emptyCtx
          { rom_address := 0#u64, rd := 3#u32, rs1 := 1#u32, rs2 := 0#u32, imm := 0#i32 }
          riscv2zisk_single_row.Rv64imSingleRowOpcode.Ld false
      let zib ← core.option.Option.unwrap ctx.extract_inst
      let row ← aeneas_extract.ZiskInstExtract.from_inst zib.i
      ok { accepted := true, decode := ldX3ZeroX1Decode, row := row }) := by
  with_unfolding_all rfl

set_option maxHeartbeats 2000000 in
/-- **The whole production transpile of `ld x3, 0(x1)`**, decode record included.
    `accepted = true`, so this is a word the lowerer really accepts. -/
theorem ldX3ZeroX1_transpile :
    aeneas_extract.extract_transpile_rv64im_raw (toU32 rawLdX3ZeroX1)
      = ok { accepted := true, decode := ldX3ZeroX1Decode,
             row := ldExtractAt 0#u64 1#u64 0#u64 3#i64 } := by
  rw [ldX3ZeroX1_unfold,
    ld_lowering_ctx 0#u64 3#u32 1#u32 0#u32 0#i32
      (by decide) (by decide) (by decide) hcast_x3_add_zero (by decide) (by decide) (by decide)]
  rfl

/-- Placing an already-computed load extract at another ROM address moves only
    `paddr`; folds `romMessageOfRawAt`'s layout argument in. -/
theorem ldExtractAt_paddr (a b aoff boff : Std.U64) (soff : Std.I64) :
    { ldExtractAt a aoff boff soff with paddr := b } = ldExtractAt b aoff boff soff := rfl

/-- **The serialized lowering of `ld x3, 0(x1)`, at any ROM address.** -/
theorem romMessageOfRawAt_ldX3ZeroX1 (addr : Std.U64) :
    romMessageOfRawAt addr rawLdX3ZeroX1
      = ok (romRowOf (ldExtractAt addr 1#u64 0#u64 3#i64)) := by
  simp only [romMessageOfRawAt, ldX3ZeroX1_transpile, ldExtractAt_paddr,
    Bind.bind, bind_ok]

/-- **Inhabitation, witness 1.**  The committed LD row of the SD/LD spin witness
    IS the ROM serialization of the lowering of a real 32-bit RISC-V word.

    All eleven slots are pinned, `line` included: the address enters through
    `romMessageOfRawAt`'s layout argument, and `ld_rom_address_reaches_only_paddr`
    says that is exactly what the lowerer emits at that address. -/
theorem sdLdLdProgramRow_inhabited :
    romMessageOfRawAt 20#u64 rawLdX3ZeroX1
      = ok ZiskFv.Compliance.SdLdSpinWitness.sdLdLdProgramRow := by
  rw [romMessageOfRawAt_ldX3ZeroX1]
  exact congrArg ok
    (romRowOf_eq_sdLdLdProgramRow (ldExtractAt 20#u64 1#u64 0#u64 3#i64)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

end ZiskFv.Compliance.RomRowInhabitation
