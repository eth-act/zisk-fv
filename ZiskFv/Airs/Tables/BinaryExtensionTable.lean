import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus

/-!
ZisK binary-extension lookup table (`bus_id = 124`).

The `BinaryExtension` AIR (pilout idx 12) emits one 7-tuple per byte
against `BINARY_EXTENSION_TABLE_ID = 124`:

  `[op, byte_index, a_byte, shift_amount, c_lo_byte, c_hi_byte, op_is_shift]`

The provider side is the fixed virtual table defined by
`zisk/state-machines/binary/pil/binary_extension_table.pil`'s
deterministic `for` loop, switching on the shift opcode (SLL, SRL, SRA,
SLL_W, SRL_W, SRA_W, SEXT_B, SEXT_H, SEXT_W). Each lookup pulls the full
64-bit *contribution* of one input byte at its given byte position to the
final shift result, split into 32-bit lo/hi halves.

Same architecture as `Airs.BinaryTable` — see that file's docstring and
CLAUDE.md's trusted-surface ledger.
-/

namespace ZiskFv.Airs.Tables.BinaryExtensionTable

open Goldilocks

/-! ## Op literals (from `zisk/pil/operations.pil`) -/

/-- Shift-left logical (64-bit). -/
def OP_SLL    : ℕ := 0x21
/-- Shift-right logical (64-bit). -/
def OP_SRL    : ℕ := 0x22
/-- Shift-right arithmetic (64-bit). -/
def OP_SRA    : ℕ := 0x23
/-- Shift-left logical word (32-bit). -/
def OP_SLL_W  : ℕ := 0x24
/-- Shift-right logical word (32-bit). -/
def OP_SRL_W  : ℕ := 0x25
/-- Shift-right arithmetic word (32-bit). -/
def OP_SRA_W  : ℕ := 0x26
/-- Sign-extend byte (RV64 SEXT.B). -/
def OP_SEXT_B : ℕ := 0x27
/-- Sign-extend halfword. -/
def OP_SEXT_H : ℕ := 0x28
/-- Sign-extend word. -/
def OP_SEXT_W : ℕ := 0x29

/-! ## Bus-entry structure -/

/-- One row's `BinaryExtensionTable` lookup tuple. -/
structure BinaryExtensionTableEntry (F : Type) [Field F] where
  multiplicity : F
  op : F
  /-- Byte position 0..7 of `a_byte` within the 64-bit input. -/
  byte_index : F
  /-- The single byte of input A at position `byte_index`. -/
  a_byte : F
  /-- Shift amount (full 8-bit byte; the table masks to 5 or 6 bits as
      required by the opcode). -/
  shift_amount : F
  /-- Low 32-bit half of this byte's contribution to the 64-bit result. -/
  c_lo_byte : F
  /-- High 32-bit half of this byte's contribution to the 64-bit result. -/
  c_hi_byte : F
  /-- 1 if the opcode is a shift; 0 if a sign-extension. -/
  op_is_shift : F
  deriving BEq, DecidableEq, Inhabited

/-! ## Trusted per-row well-formedness -/

/-- Range conditions on the input byte slots. -/
def range_conditions (e : BinaryExtensionTableEntry FGL)
    : Prop :=
  e.a_byte.val < 256 ∧ e.byte_index.val < 8 ∧
  e.shift_amount.val < 256

/-- Shift-left logical: this byte's contribution at position
    `byte_index` is `(a_byte * 2^(8·byte_index)) << (shift_amount % 64)`,
    truncated to 64 bits and split into lo/hi 32-bit halves. -/
def wf_SLL (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SLL →
    let positioned : ℕ := e.a_byte.val * (256 ^ e.byte_index.val)
    let shifted : ℕ := (positioned <<< (e.shift_amount.val % 64)) % (2 ^ 64)
    e.c_lo_byte.val = shifted % (2 ^ 32) ∧
    e.c_hi_byte.val = shifted / (2 ^ 32) ∧
    e.op_is_shift.val = 1

/-- Shift-right logical: similar to SLL but right-shifted. -/
def wf_SRL (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SRL →
    let positioned : ℕ := e.a_byte.val * (256 ^ e.byte_index.val)
    let shifted : ℕ := positioned >>> (e.shift_amount.val % 64)
    e.c_lo_byte.val = shifted % (2 ^ 32) ∧
    e.c_hi_byte.val = shifted / (2 ^ 32) ∧
    e.op_is_shift.val = 1

/-- Shift-right arithmetic: as SRL but at `byte_index = 7` with the
    high bit of `a_byte` set, the output gains the sign-extension mask
    `MASK_64 << (64 - s) % 2^64 = 2^64 - 2^(64 - s)`.

    Reference: `zisk/state-machines/binary/pil/binary_extension_table.pil`,
    `case OP_SRA`. The PIL's `out | (MASK_64 << (64 - _b))` expression,
    once truncated to 64 bits via the `c0 = out & MASK_32; c1 = (out >> 32) & MASK_32`
    extraction, is equivalent to adding `2^64 - 2^(64 - s)` to the
    base shifted value (because the sign-extension mask occupies the
    high bits `[64-s, 64)` and the base shifted value occupies bits
    `[56-s, 64-s)` — disjoint, so OR = +). For `s = 0` the mask
    `2^64 - 2^64 = 0` collapses, matching Rust's `b_low != 0` guard. -/
def wf_SRA (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SRA →
    let s : ℕ := e.shift_amount.val % 64
    let positioned : ℕ := e.a_byte.val * (256 ^ e.byte_index.val)
    let base : ℕ := positioned >>> s
    let ext : ℕ :=
      if e.byte_index.val = 7 ∧ e.a_byte.val ≥ 128
      then 2 ^ 64 - 2 ^ (64 - s)
      else 0
    let full : ℕ := base + ext
    e.c_lo_byte.val = full % (2 ^ 32) ∧
    e.c_hi_byte.val = full / (2 ^ 32) ∧
    e.op_is_shift.val = 1

/-- 32-bit shift-left logical (word-mode). For `byte_index ≥ 4` the
    contribution is 0. Otherwise, let `s = shift_amount % 32` and
    `inner = (a_byte * 256^byte_index * 2^s) % 2^32` (the byte's
    contribution to the low-32 word-sized result). The byte's
    high-32 output is `2^32 - 1` if `inner ≥ 2^31` (sign bit set),
    else 0 — encoding the per-byte share of the W-mode sign extension.

    Reference: `case OP_SLL_W` in `binary_extension_table.pil` /
    `binary_extension.rs`. -/
def wf_SLL_W (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SLL_W →
    let s : ℕ := e.shift_amount.val % 32
    let positioned : ℕ := e.a_byte.val * (256 ^ e.byte_index.val)
    let inner : ℕ :=
      if e.byte_index.val < 4 then (positioned <<< s) % (2 ^ 32) else 0
    e.c_lo_byte.val = inner ∧
    e.c_hi_byte.val = (if inner ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0) ∧
    e.op_is_shift.val = 1

/-- 32-bit shift-right logical (word-mode). For `byte_index ≥ 4` the
    contribution is 0. Otherwise, let `s = shift_amount % 32` and
    `inner = (a_byte * 256^byte_index) >>> s` (the byte's contribution
    to the low-32 word-sized result; this fits in 32 bits because
    `byte_index < 4` and `a_byte < 256`). The byte's high-32 output
    is `2^32 - 1` if `inner ≥ 2^31`, else 0.

    Reference: `case OP_SRL_W`. -/
def wf_SRL_W (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SRL_W →
    let s : ℕ := e.shift_amount.val % 32
    let positioned : ℕ := e.a_byte.val * (256 ^ e.byte_index.val)
    let inner : ℕ :=
      if e.byte_index.val < 4 then positioned >>> s else 0
    e.c_lo_byte.val = inner ∧
    e.c_hi_byte.val = (if inner ≥ 2 ^ 31 then 2 ^ 32 - 1 else 0) ∧
    e.op_is_shift.val = 1

/-- 32-bit shift-right arithmetic (word-mode). For `byte_index ≥ 4`
    the contribution is 0. Otherwise, let `s = shift_amount % 32`,
    `base = (a_byte * 256^byte_index) >>> s`. At `byte_index = 3` with
    high bit of `a_byte` set, the byte additionally contributes the
    sign-extension mask `MASK_64 << (32 - s) % 2^64 = 2^64 - 2^(32 - s)`.

    Reference: `case OP_SRA_W`. -/
def wf_SRA_W (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SRA_W →
    let s : ℕ := e.shift_amount.val % 32
    let positioned : ℕ := e.a_byte.val * (256 ^ e.byte_index.val)
    let base : ℕ :=
      if e.byte_index.val < 4 then positioned >>> s else 0
    let ext : ℕ :=
      if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
      then 2 ^ 64 - 2 ^ (32 - s)
      else 0
    let full : ℕ := base + ext
    e.c_lo_byte.val = full % (2 ^ 32) ∧
    e.c_hi_byte.val = full / (2 ^ 32) ∧
    e.op_is_shift.val = 1

/-- Sign-extend byte (RV64 SEXT.B): byte_index 0 is the byte being
    sign-extended, byte_indices 1..7 contribute zero. The sign-extension
    mask `SE_MASK_8 = 0xFFFFFFFFFFFFFF00 = 2^64 - 256` applies when
    `a_byte ≥ 128` at byte_index 0.

    Reference: `case OP_SEXT_B` in `binary_extension_table.pil:149-160`. -/
def wf_SEXT_B (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SEXT_B →
    let out : ℕ :=
      if e.byte_index.val = 0 then
        if e.a_byte.val ≥ 128
        then e.a_byte.val + (2 ^ 64 - 256)
        else e.a_byte.val
      else 0
    e.c_lo_byte.val = out % (2 ^ 32) ∧
    e.c_hi_byte.val = out / (2 ^ 32) ∧
    e.op_is_shift.val = 0

/-- Sign-extend halfword (RV64 SEXT.H): byte_index 0 contributes
    the low byte unmodified; byte_index 1 contributes the high byte
    of the halfword and, when `a_byte ≥ 128`, the sign-extension mask
    `SE_MASK_16 = 0xFFFFFFFFFFFF0000 = 2^64 - 2^16`. byte_indices ≥ 2
    contribute zero.

    Reference: `case OP_SEXT_H` in `binary_extension_table.pil:162-175`. -/
def wf_SEXT_H (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SEXT_H →
    let out : ℕ :=
      if e.byte_index.val = 0 then e.a_byte.val
      else if e.byte_index.val = 1 then
        let a_pos := e.a_byte.val * 256
        if e.a_byte.val ≥ 128 then a_pos + (2 ^ 64 - 2 ^ 16) else a_pos
      else 0
    e.c_lo_byte.val = out % (2 ^ 32) ∧
    e.c_hi_byte.val = out / (2 ^ 32) ∧
    e.op_is_shift.val = 0

/-- Sign-extend word (RV64 SEXT.W): byte_indices 0..3 contribute
    `a_byte * 256^byte_index` (their natural placement in the
    32-bit word); byte_index 3 additionally contributes the
    sign-extension mask `SE_MASK_32 = 0xFFFFFFFF00000000 = 2^64 - 2^32`
    when `a_byte ≥ 128`. byte_indices ≥ 4 contribute zero.

    Reference: `case OP_SEXT_W` in `binary_extension_table.pil:177-189`. -/
def wf_SEXT_W (e : BinaryExtensionTableEntry FGL) : Prop :=
  e.op.val = OP_SEXT_W →
    let out : ℕ :=
      if e.byte_index.val < 4 then
        let a_pos := e.a_byte.val * (256 ^ e.byte_index.val)
        if e.byte_index.val = 3 ∧ e.a_byte.val ≥ 128
        then a_pos + (2 ^ 64 - 2 ^ 32)
        else a_pos
      else 0
    e.c_lo_byte.val = out % (2 ^ 32) ∧
    e.c_hi_byte.val = out / (2 ^ 32) ∧
    e.op_is_shift.val = 0

/-- The full trusted per-row well-formedness. Mirror of
    `BinaryTable.wf_properties`. -/
def wf_properties (e : BinaryExtensionTableEntry FGL) : Prop :=
  range_conditions e
  ∧ wf_SLL e
  ∧ wf_SRL e
  ∧ wf_SRA e
  ∧ wf_SLL_W e
  ∧ wf_SRL_W e
  ∧ wf_SRA_W e
  ∧ wf_SEXT_B e
  ∧ wf_SEXT_H e
  ∧ wf_SEXT_W e

-- `bin_ext_table_consumer_wf` axiom retired in T4-purge P4. All consumers
-- now use the Clean static-BinaryExtensionTable route (StaticLookupSoundness).

end ZiskFv.Airs.Tables.BinaryExtensionTable
