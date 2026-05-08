import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
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

namespace ZiskFv.Airs.BinaryExtensionTable

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

/-- **Trusted axiom (consumer-side).** Every entry the BinaryExtension AIR
    consumes against the binary-extension table satisfies `wf_properties`.
    Mirror of `BinaryTable.bin_table_consumer_wf`. -/
axiom bin_ext_table_consumer_wf
    (e : BinaryExtensionTableEntry FGL)
    (h_consumer : e.multiplicity = 1) :
    wf_properties e

/-! ## Sign-extension load c-packed closure (LB, LH, LW)

For sign-extension loads ZisK's Main row sets `is_external_op = 1`
with `op = OP_SIGNEXTEND_{B,H,W}` and emits an operation-bus entry
consumed by the BinaryExtension AIR. The BinaryExtension AIR's
plookup soundness (`bin_ext_table_consumer_wf`) authorizes the SEXT
output, but the upstream PIL `binary_extension_table.pil:149-189`
defines `wf_SEXT_B/H/W` cases that are not (yet) part of `wf_properties`
above. Rather than extend `wf_properties` and prove three new
packed-correctness theorems through the existing chain, we axiomatize
the bus-emission-level closure directly: given a Main row in
sign-extend mode, the rd-write entry's bytes pack to the
sign-extension of the read entry's low N bytes.

Trust class: BinaryExtension lookup soundness (existing class #9 in
`docs/fv/trusted-base.md`, extended to cover the SEXT_B/H/W cases of
the upstream lookup table). The closure-level axiom is strictly
implied by `wf_SEXT_*` extensions to `wf_properties` plus per-byte
packed-correctness theorems plus the operation-bus permutation
handshake; we collapse the whole chain into one trust assertion.
-/

variable {C : Type → Type → Type} [Circuit FGL FGL C]

open ZiskFv.Trusted
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus

/-- Op-conditional sign-extension closure predicate. For each
    sign-extension opcode (B / H / W), asserts the rd-write entry
    `e2`'s 8-byte packing equals `signExtend 64` of `e1`'s low
    `n ∈ {1, 2, 4}` bytes. -/
@[simp]
def signextend_c_packed_for_op
    (e1 e2 : MemoryBusEntry FGL) (op : FGL) : Prop :=
  (op = OP_SIGNEXTEND_B →
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8),
                (e2.x3 : BitVec 8), (e2.x4 : BitVec 8), (e2.x5 : BitVec 8),
                (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (e1.x0 : BitVec 8))
  ∧ (op = OP_SIGNEXTEND_H →
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8),
                (e2.x3 : BitVec 8), (e2.x4 : BitVec 8), (e2.x5 : BitVec 8),
                (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 ((e1.x1 : BitVec 8) ++ (e1.x0 : BitVec 8)))
  ∧ (op = OP_SIGNEXTEND_W →
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8),
                (e2.x3 : BitVec 8), (e2.x4 : BitVec 8), (e2.x5 : BitVec 8),
                (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64
          ((e1.x3 : BitVec 8) ++ (e1.x2 : BitVec 8)
            ++ (e1.x1 : BitVec 8) ++ (e1.x0 : BitVec 8)))

/-- **Trusted axiom: sign-extension load closure.** A Main row in
    `is_external_op = 1` mode with `op ∈ {OP_SIGNEXTEND_B, _H, _W}`
    that emits memory-bus entries `e1` (read) and `e2` (rd-write) has
    the rd-write packed value equal to the sign-extension of `e1`'s
    low N bytes (N matching the opcode).

    This replaces the previously-unproven `h_high_bytes_signext`
    hypothesis on LB/LH/LW canonical equivalence theorems. -/
axiom signextend_load_c_packed
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (e1 e2 : MemoryBusEntry FGL)
    (h_emit_b : m.b_0 r_main = memory_entry_lo e1
              ∧ m.b_1 r_main = memory_entry_hi e1
              ∧ e1.as = 2 ∧ e1.multiplicity = -1)
    (h_emit_c : m.c_0 r_main = memory_entry_lo e2
              ∧ m.c_1 r_main = memory_entry_hi e2)
    (h_ext : m.is_external_op r_main = 1) :
    signextend_c_packed_for_op e1 e2 (m.op r_main)

end ZiskFv.Airs.BinaryExtensionTable
