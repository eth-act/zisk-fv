/-
ZiskFv/Compliance/RomRowSerialization.lean  (eth-act/zisk-fv#61, Phase-0 step S2)

Line-by-line transcription of ZisK's ROM-row emitter,
`zisk/state-machines/rom/src/rom.rs:204-260` (`RomSM::compute_trace_rom`), together
with its `zisk/core/src/zisk_inst.rs:289-308` (`ZiskInst::get_flags`) flag packing.

WHY THIS FILE EXISTS.  An accepted ZisK trace commits to a *lowered* eleven-slot
`ZiskRomMessage` per instruction, never to a 32-bit RISC-V word.  Any future
raw-word binding (`trace.program k = <serialization of the lowering of word k>`)
is only as strong as the serialization it names, and a plausible-looking but
wrong serialization yields green theorems over a false premise.  So the
serialization is written TWICE, independently, and the two forms are proven
equal:

  * `romFlagsNat` / `romRowOf` — the *Rust-shaped* transcription: the `|`/`<<`
    flag chain of `zisk_inst.rs:290-305`, the `if v >= 0 … else F::neg …`
    branches of `rom.rs:211-235`, the `SRC_IMM` gates of `rom.rs:240-244`, and
    the Fcall→CopyB opcode remap of `rom.rs:248-255`.  Every field carries its
    `rom.rs` line.
  * `romRowSpec` — the *field-shaped* form: signed slots as the ring image of
    `BitVec.toInt`, and flags as `packFlags`, the PIL-mirroring packing that
    already exists in `ZiskFv/AirsClean/Main/Circuit.lean` and that every
    committed witness row in the tree is written against.  `packFlags` was NOT
    written for this proof; the agreement theorem therefore checks the Rust
    emitter against an independently maintained in-tree definition.

`romRowOf_eq_romRowSpec` is the agreement theorem.  A slipped bit position, a
dropped `SRC_IMM` gate, or a sign error fails that proof instead of passing
silently.

WHAT THE AGREEMENT THEOREM DOES *NOT* SAY.  It is a statement about
serialization only.  It does not say that any committed `trace.program` is the
image of a raw program, it does not run the Aeneas-extracted lowerer, and it
does not fix the ROM layout (`rom.rs:205` sorts by `paddr`; `line` here is
`e.paddr`, and whether `e.paddr` is the address the binary places the word at is
not addressed by anything in this file).  Those are Phase-0 step S3 and issue #61's
`ProgramBinding`.

Kernel-sound: no `axiom` / `sorry` / `native_decide` / `bv_decide`.
-/
import ProductionM2
import ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Helpers
import ZiskFv.Compliance.SdLdSpinWitness

open Aeneas Aeneas.Std Result zisk_core
open Goldilocks

namespace ZiskFv.Compliance.RomRowSerialization

open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)
open ZiskFv.AirsClean.Main (RomFlagBits packFlags)
open ZiskFv.AirsClean (boolF)
open zisk_core.aeneas_extract (ZiskInstExtract)

/-! ## 1. Opcode codes used by the `rom.rs:248-255` Fcall→CopyB remap

`rom.rs` compares `inst.op` against `ZiskOp::{Fcall, FcallGet, FcallParam}.code()`
and rewrites those three to `ZiskOp::CopyB.code()`.  The literals below are tied
back to the extracted `ZiskOp::code` so a stale constant fails a proof. -/

/-- `ZiskOp::CopyB.code()` (`ProductionM2.lean:1594`). -/
def CODE_COPYB : Std.U8 := 1#u8
/-- `ZiskOp::FcallParam.code()` (`ProductionM2.lean:1667`). -/
def CODE_FCALL_PARAM : Std.U8 := 246#u8
/-- `ZiskOp::Fcall.code()` (`ProductionM2.lean:1668`). -/
def CODE_FCALL : Std.U8 := 247#u8
/-- `ZiskOp::FcallGet.code()` (`ProductionM2.lean:1669`). -/
def CODE_FCALL_GET : Std.U8 := 248#u8

theorem code_copyb : zisk_ops.ZiskOp.code .CopyB = ok CODE_COPYB := rfl
theorem code_fcall_param : zisk_ops.ZiskOp.code .FcallParam = ok CODE_FCALL_PARAM := rfl
theorem code_fcall : zisk_ops.ZiskOp.code .Fcall = ok CODE_FCALL := rfl
theorem code_fcall_get : zisk_ops.ZiskOp.code .FcallGet = ok CODE_FCALL_GET := rfl

/-! ## 2. The signed field conversion of `rom.rs:211-235`

Five ROM slots (`jmp_offset1`, `jmp_offset2`, `store_offset`, `a_offset_imm0`,
`b_offset_imm0`) go through the same shape:

```rust
let f = if v >= 0 { F::from_u64(v as u64) } else { F::neg(F::from_u64((-v) as u64)) };
```

For the three `i64` fields `v` is the field itself; for the two `u64` fields
(`a_offset_imm0`, `b_offset_imm0`) `rom.rs:226`/`:231` first *reinterpret* the
bits as `i64` (`inst.a_offset_imm0 as i64 >= 0`).  Both cases are the same
function of the 64 underlying bits, which is why it is written once here. -/

/-- Transcription of `rom.rs:211-235`.  `w` is the raw 64-bit machine word of the
    slot; `w.toInt` is Rust's `as i64` reinterpretation and `-w` is Rust's
    wrapping `i64` negation, so this is literal down to the `i64::MIN` edge. -/
def romSignedField (w : BitVec 64) : FGL :=
  if 0 ≤ w.toInt then          -- rom.rs:211 / :216 / :221 / :226 / :231  `v >= 0`
    ((w.toNat : ℕ) : FGL)      -- rom.rs:212 / :217 / :222 / :227 / :232  `F::from_u64(v as u64)`
  else
    -(((-w).toNat : ℕ) : FGL)  -- rom.rs:214 / :219 / :224 / :229 / :234  `F::neg(F::from_u64((-v) as u64))`

/-- The independently written form: `romSignedField` is the ring image of the
    *signed* value of the slot.  This is the identity June's `serializeExtract`
    got wrong for `a/b_offset_imm0` (it used `UScalar.val : ℕ`, the unsigned
    value). -/
theorem romSignedField_eq_intCast (w : BitVec 64) :
    romSignedField w = ((w.toInt : ℤ) : FGL) := by
  have hb : w.toNat < 2 ^ 64 := w.isLt
  have hle : w.toNat ≤ 2 ^ 64 := le_of_lt hb
  have hdef : w.toInt =
      if 2 * w.toNat < 2 ^ 64 then (w.toNat : ℤ) else (w.toNat : ℤ) - 2 ^ 64 := rfl
  unfold romSignedField
  by_cases hc : 2 * w.toNat < 2 ^ 64
  · have hInt : w.toInt = (w.toNat : ℤ) := by rw [hdef, if_pos hc]
    rw [if_pos (by rw [hInt]; positivity), hInt]
    push_cast
    ring
  · have hInt : w.toInt = (w.toNat : ℤ) - 2 ^ 64 := by rw [hdef, if_neg hc]
    have hpos : 0 < w.toNat := by omega
    have hnn : ¬ (0 ≤ w.toInt) := by rw [hInt]; push_cast; omega
    have hneg : (-w).toNat = 2 ^ 64 - w.toNat := by
      rw [BitVec.toNat_neg]; omega
    rw [if_neg hnn, hneg, Nat.cast_sub hle, hInt]
    push_cast
    ring

/-! ## 3. The flag word of `zisk_inst.rs:289-308`

`get_flags` builds a `u64` by OR-ing sixteen shifted single bits.  Every operand
is `(bool as u64) << k` with `k ≤ 15`, so the value is `< 2^16` and the `u64`
arithmetic is exact; the transcription is therefore written over `ℕ`, where
`|||` and `<<<` agree with Rust's `|` and `<<`.  `romFlagsNat_lt` proves the
`< 2^16` bound rather than assuming it. -/

/-- Rust's `bool as u64`. -/
@[reducible] def natOfBool (b : Bool) : ℕ := if b then 1 else 0

/-- Transcription of `ZiskInst::get_flags` (`zisk_inst.rs:289-308`).  Bit
    positions and predicates are copied line by line; the source constants are
    the *extracted* `zisk_inst.SRC_*` / `zisk_inst.STORE_*` — `SRC_IMM`
    (`ProductionM2.lean:2081`), `SRC_MEM` (`:2264`), `SRC_IND` (`:2704`),
    `SRC_REG` (`:2259`), `STORE_MEM` (`:2004`), `STORE_IND` (`:2636`),
    `STORE_REG` (`:1999`) — never numeric literals. -/
def romFlagsNat (e : ZiskInstExtract) : ℕ :=
  1                                                                          -- zisk_inst.rs:290
  ||| (natOfBool (decide (e.a_src = zisk_inst.SRC_IMM)) <<< 1)               -- zisk_inst.rs:291
  ||| (natOfBool (decide (e.a_src = zisk_inst.SRC_MEM)) <<< 2)               -- zisk_inst.rs:292
  ||| (natOfBool e.is_precompiled <<< 3)                                     -- zisk_inst.rs:293
  ||| (natOfBool (decide (e.b_src = zisk_inst.SRC_IMM)) <<< 4)               -- zisk_inst.rs:294
  ||| (natOfBool (decide (e.b_src = zisk_inst.SRC_MEM)) <<< 5)               -- zisk_inst.rs:295
  ||| (natOfBool e.is_external_op <<< 6)                                     -- zisk_inst.rs:296
  ||| (natOfBool e.store_pc <<< 7)                                           -- zisk_inst.rs:297
  ||| (natOfBool (decide (e.store = zisk_inst.STORE_MEM)) <<< 8)             -- zisk_inst.rs:298
  ||| (natOfBool (decide (e.store = zisk_inst.STORE_IND)) <<< 9)             -- zisk_inst.rs:299
  ||| (natOfBool e.set_pc <<< 10)                                            -- zisk_inst.rs:300
  ||| (natOfBool e.m32 <<< 11)                                               -- zisk_inst.rs:301
  ||| (natOfBool (decide (e.b_src = zisk_inst.SRC_IND)) <<< 12)              -- zisk_inst.rs:302
  ||| (natOfBool (decide (e.a_src = zisk_inst.SRC_REG)) <<< 13)              -- zisk_inst.rs:303
  ||| (natOfBool (decide (e.b_src = zisk_inst.SRC_REG)) <<< 14)              -- zisk_inst.rs:304
  ||| (natOfBool (decide (e.store = zisk_inst.STORE_REG)) <<< 15)            -- zisk_inst.rs:305

/-- The `RomFlagBits` record the in-tree PIL-mirroring `packFlags` consumes.
    Same predicates, no bit positions: `packFlags` supplies those. -/
def romFlagBitsOf (e : ZiskInstExtract) : RomFlagBits where
  a_src_imm := decide (e.a_src = zisk_inst.SRC_IMM)
  a_src_mem := decide (e.a_src = zisk_inst.SRC_MEM)
  is_precompiled := e.is_precompiled
  b_src_imm := decide (e.b_src = zisk_inst.SRC_IMM)
  b_src_mem := decide (e.b_src = zisk_inst.SRC_MEM)
  is_external_op := e.is_external_op
  store_pc := e.store_pc
  store_mem := decide (e.store = zisk_inst.STORE_MEM)
  store_ind := decide (e.store = zisk_inst.STORE_IND)
  set_pc := e.set_pc
  m32 := e.m32
  b_src_ind := decide (e.b_src = zisk_inst.SRC_IND)
  a_src_reg := decide (e.a_src = zisk_inst.SRC_REG)
  b_src_reg := decide (e.b_src = zisk_inst.SRC_REG)
  store_reg := decide (e.store = zisk_inst.STORE_REG)

/-- One link of the OR chain: OR-ing an accumulator that fits strictly below
    `2 ^ i` with a single bit shifted to position `i` is addition. -/
private theorem or_bit_step {acc i : ℕ} (h : acc < 2 ^ i) (b : Bool) :
    acc ||| (natOfBool b <<< i) = acc + (if b then 2 ^ i else 0) := by
  cases b
  · simp [natOfBool]
  · simp only [natOfBool, if_pos]
    rw [Nat.shiftLeft_eq, one_mul, Nat.or_comm]
    have := Nat.two_pow_add_eq_or_of_lt h 1
    simp only [mul_one] at this
    omega

private theorem or_bit_bound {acc i : ℕ} (h : acc < 2 ^ i) (b : Bool) :
    acc + (if b then 2 ^ i else 0) < 2 ^ (i + 1) := by
  have : (2:ℕ) ^ (i + 1) = 2 ^ i + 2 ^ i := by ring
  cases b <;> simp <;> omega

/-- The `< 2^16` bound the `ℕ`-typed transcription relies on: the Rust `u64`
    arithmetic in `get_flags` never wraps. -/
theorem romFlagsNat_lt (e : ZiskInstExtract) : romFlagsNat e < 2 ^ 16 := by
  have h0 : (1 : ℕ) < 2 ^ 1 := by norm_num
  unfold romFlagsNat
  rw [or_bit_step h0]
  have h1 := or_bit_bound h0 (decide (e.a_src = zisk_inst.SRC_IMM))
  rw [or_bit_step h1]
  have h2 := or_bit_bound h1 (decide (e.a_src = zisk_inst.SRC_MEM))
  rw [or_bit_step h2]
  have h3 := or_bit_bound h2 e.is_precompiled
  rw [or_bit_step h3]
  have h4 := or_bit_bound h3 (decide (e.b_src = zisk_inst.SRC_IMM))
  rw [or_bit_step h4]
  have h5 := or_bit_bound h4 (decide (e.b_src = zisk_inst.SRC_MEM))
  rw [or_bit_step h5]
  have h6 := or_bit_bound h5 e.is_external_op
  rw [or_bit_step h6]
  have h7 := or_bit_bound h6 e.store_pc
  rw [or_bit_step h7]
  have h8 := or_bit_bound h7 (decide (e.store = zisk_inst.STORE_MEM))
  rw [or_bit_step h8]
  have h9 := or_bit_bound h8 (decide (e.store = zisk_inst.STORE_IND))
  rw [or_bit_step h9]
  have h10 := or_bit_bound h9 e.set_pc
  rw [or_bit_step h10]
  have h11 := or_bit_bound h10 e.m32
  rw [or_bit_step h11]
  have h12 := or_bit_bound h11 (decide (e.b_src = zisk_inst.SRC_IND))
  rw [or_bit_step h12]
  have h13 := or_bit_bound h12 (decide (e.a_src = zisk_inst.SRC_REG))
  rw [or_bit_step h13]
  have h14 := or_bit_bound h13 (decide (e.b_src = zisk_inst.SRC_REG))
  rw [or_bit_step h14]
  exact or_bit_bound h14 (decide (e.store = zisk_inst.STORE_REG))

/-- The additive normal form of the OR chain. -/
theorem romFlagsNat_eq_sum (e : ZiskInstExtract) :
    romFlagsNat e =
      1
      + (if decide (e.a_src = zisk_inst.SRC_IMM) then 2 ^ 1 else 0)
      + (if decide (e.a_src = zisk_inst.SRC_MEM) then 2 ^ 2 else 0)
      + (if e.is_precompiled then 2 ^ 3 else 0)
      + (if decide (e.b_src = zisk_inst.SRC_IMM) then 2 ^ 4 else 0)
      + (if decide (e.b_src = zisk_inst.SRC_MEM) then 2 ^ 5 else 0)
      + (if e.is_external_op then 2 ^ 6 else 0)
      + (if e.store_pc then 2 ^ 7 else 0)
      + (if decide (e.store = zisk_inst.STORE_MEM) then 2 ^ 8 else 0)
      + (if decide (e.store = zisk_inst.STORE_IND) then 2 ^ 9 else 0)
      + (if e.set_pc then 2 ^ 10 else 0)
      + (if e.m32 then 2 ^ 11 else 0)
      + (if decide (e.b_src = zisk_inst.SRC_IND) then 2 ^ 12 else 0)
      + (if decide (e.a_src = zisk_inst.SRC_REG) then 2 ^ 13 else 0)
      + (if decide (e.b_src = zisk_inst.SRC_REG) then 2 ^ 14 else 0)
      + (if decide (e.store = zisk_inst.STORE_REG) then 2 ^ 15 else 0) := by
  have h0 : (1 : ℕ) < 2 ^ 1 := by norm_num
  unfold romFlagsNat
  rw [or_bit_step h0]
  have h1 := or_bit_bound h0 (decide (e.a_src = zisk_inst.SRC_IMM))
  rw [or_bit_step h1]
  have h2 := or_bit_bound h1 (decide (e.a_src = zisk_inst.SRC_MEM))
  rw [or_bit_step h2]
  have h3 := or_bit_bound h2 e.is_precompiled
  rw [or_bit_step h3]
  have h4 := or_bit_bound h3 (decide (e.b_src = zisk_inst.SRC_IMM))
  rw [or_bit_step h4]
  have h5 := or_bit_bound h4 (decide (e.b_src = zisk_inst.SRC_MEM))
  rw [or_bit_step h5]
  have h6 := or_bit_bound h5 e.is_external_op
  rw [or_bit_step h6]
  have h7 := or_bit_bound h6 e.store_pc
  rw [or_bit_step h7]
  have h8 := or_bit_bound h7 (decide (e.store = zisk_inst.STORE_MEM))
  rw [or_bit_step h8]
  have h9 := or_bit_bound h8 (decide (e.store = zisk_inst.STORE_IND))
  rw [or_bit_step h9]
  have h10 := or_bit_bound h9 e.set_pc
  rw [or_bit_step h10]
  have h11 := or_bit_bound h10 e.m32
  rw [or_bit_step h11]
  have h12 := or_bit_bound h11 (decide (e.b_src = zisk_inst.SRC_IND))
  rw [or_bit_step h12]
  have h13 := or_bit_bound h12 (decide (e.a_src = zisk_inst.SRC_REG))
  rw [or_bit_step h13]
  have h14 := or_bit_bound h13 (decide (e.b_src = zisk_inst.SRC_REG))
  rw [or_bit_step h14]

/-- **Rust emitter vs. PIL packing.**  The `|`/`<<` chain of
    `zisk_inst.rs:290-305` and the additive `packFlags` of
    `ZiskFv/AirsClean/Main/Circuit.lean` — an independently maintained in-tree
    definition mirroring the PIL `romFlagsExpr` — denote the same field element.
    A slipped bit position in either one breaks this. -/
theorem romFlagsNat_cast_eq_packFlags (e : ZiskInstExtract) :
    ((romFlagsNat e : ℕ) : FGL) = packFlags (romFlagBitsOf e) := by
  have hc : ∀ (b : Bool) (c : ℕ),
      (((if b then c else 0 : ℕ)) : FGL) = (c : FGL) * ZiskFv.AirsClean.boolF b := by
    intro b c; cases b <;> simp [ZiskFv.AirsClean.boolF]
  rw [romFlagsNat_eq_sum]
  simp only [packFlags, romFlagBitsOf, Nat.cast_add, hc]
  push_cast
  ring

/-! ## 4. The ROM row: `rom.rs:238-259`

`rom.rs` reads a `zisk_inst::ZiskInst`; the transcription below is written over
the extraction's `ZiskInstExtract`, because that is what
`extract_transpile_rv64im_raw` returns.  That substitution is only legitimate if
`ZiskInstExtract.from_inst` copies every field `rom.rs:211-259` touches
unchanged, so it is proven rather than assumed. -/

/-- `ZiskInstExtract.from_inst` (`ProductionM2.lean:1333`) preserves all eighteen
    `ZiskInst` fields the ROM emitter reads.  (It differs from `ZiskInst` only in
    replacing `op_type` by its discriminant `op_type_id`, which `rom.rs` never
    reads.)  So `romRowOf` over the extract record is the same function of the
    lowered instruction as `compute_trace_rom` is over `ZiskInst`. -/
theorem from_inst_preserves_rom_fields {i : zisk_inst.ZiskInst} {e : ZiskInstExtract}
    (h : zisk_core.aeneas_extract.ZiskInstExtract.from_inst i = ok e) :
    e.paddr = i.paddr ∧ e.jmp_offset1 = i.jmp_offset1 ∧ e.jmp_offset2 = i.jmp_offset2
      ∧ e.store_offset = i.store_offset ∧ e.a_offset_imm0 = i.a_offset_imm0
      ∧ e.b_offset_imm0 = i.b_offset_imm0 ∧ e.a_src = i.a_src
      ∧ e.a_use_sp_imm1 = i.a_use_sp_imm1 ∧ e.b_src = i.b_src
      ∧ e.b_use_sp_imm1 = i.b_use_sp_imm1 ∧ e.ind_width = i.ind_width
      ∧ e.op = i.op ∧ e.store = i.store ∧ e.store_pc = i.store_pc
      ∧ e.set_pc = i.set_pc ∧ e.is_precompiled = i.is_precompiled
      ∧ e.is_external_op = i.is_external_op ∧ e.m32 = i.m32 := by
  simp only [zisk_core.aeneas_extract.ZiskInstExtract.from_inst] at h
  obtain ⟨u, hu, hok⟩ := ZiskFv.Compliance.Extraction.bind_eq_ok_imp h
  simp only [Result.ok.injEq] at hok
  subst hok
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩

/-- Transcription of the opcode remap at `rom.rs:246-255`.  The three `Fcall`
    variants are out of RV64IM scope, but the branch is transcribed rather than
    dropped so that the claim "RV64IM never reaches it" stays a provable side
    fact instead of a silent assumption. -/
def romOpField (op : Std.U8) : FGL :=
  if op = CODE_FCALL ∨ op = CODE_FCALL_GET ∨ op = CODE_FCALL_PARAM then
    ((CODE_COPYB.val : ℕ) : FGL)   -- rom.rs:252  `F::from_u8(ZiskOp::CopyB.code())`
  else
    ((op.val : ℕ) : FGL)           -- rom.rs:254  `F::from_u8(inst.op)`

/-- **The transcription.**  `rom.rs:238-259`, field by field.

    `line` is `F::from_u64(inst.paddr)` (`rom.rs:238`), NOT a caller-supplied
    parameter: June's `serializeExtract` threaded `line` in from outside, which
    left the eleventh slot unconstrained by the binding.  A caller that wants a
    different address must justify the `paddr` it feeds in. -/
def romRowOf (e : ZiskInstExtract) : ZiskRomMessage FGL where
  line := ((e.paddr.val : ℕ) : FGL)                                -- rom.rs:238
  a_offset_imm0 := romSignedField e.a_offset_imm0.bv               -- rom.rs:226-230, :239
  a_imm1 :=                                                        -- rom.rs:240-241
    if e.a_src = zisk_inst.SRC_IMM then ((e.a_use_sp_imm1.val : ℕ) : FGL) else 0
  b_offset_imm0 := romSignedField e.b_offset_imm0.bv               -- rom.rs:231-235, :242
  b_imm1 :=                                                        -- rom.rs:243-244
    if e.b_src = zisk_inst.SRC_IMM then ((e.b_use_sp_imm1.val : ℕ) : FGL) else 0
  ind_width := ((e.ind_width.val : ℕ) : FGL)                       -- rom.rs:245
  op := romOpField e.op                                            -- rom.rs:246-255
  store_offset := romSignedField e.store_offset.bv                 -- rom.rs:221-225, :256
  jmp_offset1 := romSignedField e.jmp_offset1.bv                   -- rom.rs:211-215, :257
  jmp_offset2 := romSignedField e.jmp_offset2.bv                   -- rom.rs:216-220, :258
  flags := ((romFlagsNat e : ℕ) : FGL)                             -- rom.rs:259

/-- The field-shaped form of the same row.  Signed slots are the ring image of
    the slot's signed value; `flags` is the in-tree `packFlags`.  Written
    without reference to the `if`-branches and bit positions of `romRowOf`. -/
def romRowSpec (e : ZiskInstExtract) : ZiskRomMessage FGL where
  line := ((e.paddr.val : ℕ) : FGL)
  a_offset_imm0 := ((e.a_offset_imm0.bv.toInt : ℤ) : FGL)
  a_imm1 := if e.a_src = zisk_inst.SRC_IMM then ((e.a_use_sp_imm1.val : ℕ) : FGL) else 0
  b_offset_imm0 := ((e.b_offset_imm0.bv.toInt : ℤ) : FGL)
  b_imm1 := if e.b_src = zisk_inst.SRC_IMM then ((e.b_use_sp_imm1.val : ℕ) : FGL) else 0
  ind_width := ((e.ind_width.val : ℕ) : FGL)
  op := romOpField e.op
  store_offset := ((e.store_offset.val : ℤ) : FGL)
  jmp_offset1 := ((e.jmp_offset1.val : ℤ) : FGL)
  jmp_offset2 := ((e.jmp_offset2.val : ℤ) : FGL)
  flags := packFlags (romFlagBitsOf e)

/-- **Agreement.**  The Rust-shaped transcription and the field-shaped form
    denote the same eleven-slot ROM message.

    What it says: the `rom.rs` branch structure, the `zisk_inst.rs` bit chain,
    and the in-tree `packFlags` / `BitVec.toInt` readings coincide, for every
    lowered row.

    What it does NOT say: nothing about `trace.program`, nothing about the raw
    word, nothing about the ROM layout, and nothing about the extracted lowerer
    (which does not appear in the statement). -/
theorem romRowOf_eq_romRowSpec (e : ZiskInstExtract) : romRowOf e = romRowSpec e := by
  simp only [romRowOf, romRowSpec,
    romSignedField_eq_intCast, romFlagsNat_cast_eq_packFlags,
    Aeneas.Std.IScalar.val]

/-! ## 5. The three defects of the June serialization, confirmed against source

`a16bd97c:ZiskFv/Compliance/TraceLevelExport/RawProgramBinding.lean` wrote this
same serialization and got three things wrong.  Each is re-checked here against
the Rust and the extraction, and each is shown to *bite* (to change the emitted
field element), not merely to look different. -/

/-- **Defect 1 — the `SRC_IND` literal.**  June wrote bit 12 as
    `decide (e.b_src = 3#u64)`.  The extracted constant is `5`; `3` is
    `SRC_STEP` (`zisk_inst.rs:49`, not reachable on the RV64IM path at all). -/
theorem src_ind_eq_five : zisk_inst.SRC_IND = 5#u64 := by
  unfold zisk_inst.SRC_IND; rfl

theorem june_src_ind_literal_wrong : (3#u64 : Std.U64) ≠ zisk_inst.SRC_IND := by
  rw [src_ind_eq_five]; decide

/-- On every row the lowerer marks as indirect-`b` (every load and every store),
    the corrected bit is set. -/
theorem romFlagBitsOf_b_src_ind (e : ZiskInstExtract) (h : e.b_src = zisk_inst.SRC_IND) :
    (romFlagBitsOf e).b_src_ind = true := by
  simp [romFlagBitsOf, h]

/-- ...and June's form clears it on exactly those rows. -/
theorem june_b_src_ind_false (e : ZiskInstExtract) (h : e.b_src = zisk_inst.SRC_IND) :
    decide (e.b_src = (3#u64 : Std.U64)) = false := by
  rw [h, src_ind_eq_five]; decide

/-- The bite: bit 12 is not absorbed by the packing.  Two `RomFlagBits` that
    differ only in `b_src_ind` have different `flags` field elements, so a row
    whose `b_src_ind` is computed wrongly can never equal the committed row. -/
theorem packFlags_b_src_ind_sensitive (bits : RomFlagBits) :
    packFlags { bits with b_src_ind := true } ≠ packFlags { bits with b_src_ind := false } := by
  intro h
  have hF : ZiskFv.AirsClean.boolF false = 0 := rfl
  have hT : ZiskFv.AirsClean.boolF true = 1 := rfl
  simp only [packFlags, hF, hT] at h
  have h4096 : (4096 : FGL) = 0 := by linear_combination h
  exact absurd h4096 (by decide)

/-- **Defect 2 — the unsigned coercion.**  June serialized `a/b_offset_imm0` with
    `UScalar.val : ℕ`; `rom.rs:226-236` reinterprets the bits as `i64` first.
    The two differ by `2^64` in the field, which is `2^32 - 1 ≠ 0` in Goldilocks.
    The witness is exactly the shape the extraction produces for a negative
    load/store displacement (`IScalar.hcast` sign-extends, so `ld a0, -8(sp)`
    yields `b_offset_imm0 = 2^64 - 8`). -/
theorem romSignedField_ne_unsignedVal :
    romSignedField (BitVec.ofInt 64 (-8)) ≠ (((BitVec.ofInt 64 (-8)).toNat : ℕ) : FGL) := by
  have hInt : (BitVec.ofInt 64 (-8)).toInt = -8 := by decide
  have hNat : (BitVec.ofInt 64 (-8)).toNat = 18446744073709551608 := by decide
  rw [romSignedField_eq_intCast, hInt, hNat]
  decide

/-- **Defect 3 — the ungated `a_imm1` / `b_imm1`.**  `rom.rs:240-244` emits `0`
    unless the corresponding source is `SRC_IMM`; June copied `*_use_sp_imm1`
    unconditionally.  The transcription's gate makes the emitted value
    independent of `*_use_sp_imm1` off the immediate path, which is why the
    witness check below needs no hypothesis about those two fields. -/
theorem romRowOf_a_imm1_of_not_imm (e : ZiskInstExtract) (h : e.a_src ≠ zisk_inst.SRC_IMM) :
    (romRowOf e).a_imm1 = 0 := by
  simp [romRowOf, h]

theorem romRowOf_b_imm1_of_not_imm (e : ZiskInstExtract) (h : e.b_src ≠ zisk_inst.SRC_IMM) :
    (romRowOf e).b_imm1 = 0 := by
  simp [romRowOf, h]

/-- Partial evidence that defect 3 is harmless *on the RV64IM path* — but not
    free.  The load/store `b`-source setter writes `0` into `b_use_sp_imm1` when
    `use_sp = false`, which is the only value RV64IM callers pass.

    CORRECTION to the design note's setter list: `src_a_reg` / `src_b_reg`
    (`ProductionM2.lean:2491`, `:2269`) do NOT uniformly land on
    `SRC_REG`.  `reg = 0` delegates to `src_a_imm self 0#u64` (`:2105`, so
    `a_src` becomes `SRC_IMM`), and a register outside
    `[REGS_IN_MAIN_FROM, REGS_IN_MAIN_TO]`
    lands on `SRC_MEM`.  All branches still write `0` when `use_sp = false`, but
    the path statement ("`a_src ≠ SRC_IMM → a_use_sp_imm1 = 0` after the whole
    lowering") therefore needs a three-way case split plus the call-ordering
    argument, and belongs to Phase-0 step S3. -/
theorem src_b_ind_no_sp {self out : zisk_inst_builder.ZiskInstBuilder} {offset : Std.U64}
    (h : zisk_inst_builder.ZiskInstBuilder.src_b_ind self offset false = ok out) :
    out.i.b_src = zisk_inst.SRC_IND ∧ out.i.b_use_sp_imm1 = 0#u64 := by
  simp only [zisk_inst_builder.ZiskInstBuilder.src_b_ind, if_false,
    Bool.false_eq_true, Result.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-- **A fourth divergence from `rom.rs`, not listed in the design note.**  June's
    `serializeExtract` wrote `op := (e.op.val : FGL)` with no remap;
    `rom.rs:246-255` rewrites `Fcall` / `FcallGet` / `FcallParam` to `CopyB`.
    The remap is not a no-op, so dropping it is a real divergence — benign only
    if RV64IM provably never emits those three codes, which is *not* established
    here (it is a lowering-path fact, i.e. Phase-0 step S3). -/
theorem romOpField_remaps_fcall :
    romOpField CODE_FCALL ≠ ((CODE_FCALL.val : ℕ) : FGL) := by
  unfold romOpField CODE_COPYB CODE_FCALL CODE_FCALL_GET CODE_FCALL_PARAM
  norm_num
  decide

/-! ## 6. Sanity gate against a hand-built in-tree witness row

`ZiskFv/Compliance/SdLdSpinWitness.lean` builds `sdLdProgram` from hand-written
`ZiskRomMessage` constants chosen to satisfy the ensemble constraints — not from
any lowering.  Its LD entry sets `b_src_ind := true`, i.e. it is precisely a row
the June serialization could not have produced from an `SRC_IND` lowering.  The
theorem below checks the corrected transcription against that committed row.

Note what is and is not established.  The hypotheses fix the *lowered* row's
fields; they do not run `extract_transpile_rv64im_raw` on a raw LD word, so this
is a serialization check, not an inhabitation proof.  Closing that gap — deriving
these field values from a concrete `BitVec 32` through the extracted lowerer — is
Phase-0 step S3. -/

open ZiskFv.Compliance.SdLdSpinWitness (sdLdLdBits sdLdLdProgramRow)

/-- The LD row's flag bits are exactly what the corrected predicates compute for
    an `a`-register / `b`-indirect / register-store lowering. -/
theorem romFlagBitsOf_eq_sdLdLdBits (e : ZiskInstExtract)
    (h_a_src : e.a_src = zisk_inst.SRC_REG)
    (h_b_src : e.b_src = zisk_inst.SRC_IND)
    (h_store : e.store = zisk_inst.STORE_REG)
    (h_prec : e.is_precompiled = false)
    (h_ext : e.is_external_op = false)
    (h_store_pc : e.store_pc = false)
    (h_set_pc : e.set_pc = false)
    (h_m32 : e.m32 = false) :
    romFlagBitsOf e = sdLdLdBits := by
  unfold romFlagBitsOf sdLdLdBits
  rw [h_a_src, h_b_src, h_store, h_prec, h_ext, h_store_pc, h_set_pc, h_m32]
  unfold zisk_inst.SRC_REG zisk_inst.SRC_IND zisk_inst.SRC_IMM zisk_inst.SRC_MEM
    zisk_inst.STORE_REG zisk_inst.STORE_MEM zisk_inst.STORE_IND
  rfl

/-- **The gate.**  A lowered row with the LD shape serializes, under the
    corrected transcription, to the committed `sdLdLdProgramRow` — including the
    `b_src_ind` bit that falsifies the June form. -/
theorem romRowOf_eq_sdLdLdProgramRow (e : ZiskInstExtract)
    (h_paddr : e.paddr = 20#u64)
    (h_a_src : e.a_src = zisk_inst.SRC_REG)
    (h_a_off : e.a_offset_imm0 = 1#u64)
    (h_b_src : e.b_src = zisk_inst.SRC_IND)
    (h_b_off : e.b_offset_imm0 = 0#u64)
    (h_ind : e.ind_width = 8#u64)
    (h_op : e.op = CODE_COPYB)
    (h_store : e.store = zisk_inst.STORE_REG)
    (h_soff : e.store_offset = 3#i64)
    (h_j1 : e.jmp_offset1 = 4#i64)
    (h_j2 : e.jmp_offset2 = 4#i64)
    (h_prec : e.is_precompiled = false)
    (h_ext : e.is_external_op = false)
    (h_store_pc : e.store_pc = false)
    (h_set_pc : e.set_pc = false)
    (h_m32 : e.m32 = false) :
    romRowOf e = sdLdLdProgramRow := by
  have hbits := romFlagBitsOf_eq_sdLdLdBits e h_a_src h_b_src h_store h_prec h_ext
    h_store_pc h_set_pc h_m32
  have ha : e.a_src ≠ zisk_inst.SRC_IMM := by
    rw [h_a_src]; unfold zisk_inst.SRC_REG zisk_inst.SRC_IMM; decide
  have hbb : e.b_src ≠ zisk_inst.SRC_IMM := by
    rw [h_b_src]; unfold zisk_inst.SRC_IND zisk_inst.SRC_IMM; decide
  have hop : romOpField e.op = ZiskFv.Trusted.OP_COPYB := by
    rw [h_op]
    unfold romOpField CODE_COPYB CODE_FCALL CODE_FCALL_GET CODE_FCALL_PARAM
    norm_num [ZiskFv.Trusted.OP_COPYB]
  simp only [romRowOf, sdLdLdProgramRow, ZiskRomMessage.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hop, ?_, ?_, ?_, ?_⟩
  · rw [h_paddr]; decide
  · rw [h_a_off]; decide
  · rw [if_neg ha]
  · rw [h_b_off]; decide
  · rw [if_neg hbb]
  · rw [h_ind]; decide
  · rw [h_soff]; decide
  · rw [h_j1]; decide
  · rw [h_j2]; decide
  · rw [romFlagsNat_cast_eq_packFlags, hbits]

end ZiskFv.Compliance.RomRowSerialization
