import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks

/-!
ZisK binary lookup table (`bus_id = 125`).

The `Binary` AIR (pilout idx 10) emits one 7-tuple per byte against
`BINARY_TABLE_ID = 125`:

  `[pos_ind, b_op, a_byte, b_byte, cin, c_byte, flags]`

where `flags = cout + 2·result_is_a + 4·use_first_byte + 8·c_is_signed_byte`.
The provider side is the fixed virtual table defined by
`vendor/zisk/state-machines/binary/pil/binary_table.pil`'s deterministic
`for` loop (a switch on `op` enumerating per-byte semantics for AND/OR/XOR,
LT/LTU/GT/EQ/LE/LEU/MIN(U)/MAX(U)/LT_ABS_*, ADD/SUB, SEXT_00/SEXT_FF).

This file mirrors the openvm-fv pattern at
`openvm-fv/OpenvmFv/Fundamentals/Interaction.lean::BitwiseBusEntry`:
the per-row semantic relation `wf_properties` is **trusted** at the
bus-entry definition site. openvm-fv never proves its bitwise / range /
program-bus tables; the relation is simply asserted as part of the
`BusEntry` instance. We adopt the same convention — see CLAUDE.md's
trusted-surface ledger. Improving the trust by porting the PIL2 generator
switch to a proven Lean theorem is welcome but out of scope.
-/

namespace ZiskFv.Airs.BinaryTable

open Goldilocks

/-! ## Op literals (from `vendor/zisk/pil/operations.pil`) -/

/-- Less-than unsigned. -/
def OP_LTU : ℕ := 0x06
/-- Less-than signed. -/
def OP_LT  : ℕ := 0x07
/-- Greater-than (signed). -/
def OP_GT  : ℕ := 0x08
/-- Equality. -/
def OP_EQ  : ℕ := 0x09
/-- Add (carry-chain byte). -/
def OP_ADD : ℕ := 0x0A
/-- Subtract (borrow byte). -/
def OP_SUB : ℕ := 0x0B
/-- Less-than-or-equal unsigned. -/
def OP_LEU : ℕ := 0x0C
/-- Less-than-or-equal signed. -/
def OP_LE  : ℕ := 0x0D
/-- Bitwise AND. -/
def OP_AND : ℕ := 0x0E
/-- Bitwise OR. -/
def OP_OR  : ℕ := 0x0F
/-- Bitwise XOR. -/
def OP_XOR : ℕ := 0x10
/-- Sign-extend with `0x00` (auxiliary; produced by `b_op_or_sext`). -/
def OP_SEXT_00 : ℕ := 0x200
/-- Sign-extend with `0xFF` (auxiliary; produced by `b_op_or_sext`). -/
def OP_SEXT_FF : ℕ := 0x201

/-! ## Bus-entry structure -/

/-- One row's `BinaryTable` lookup tuple. The Binary AIR (consumer) emits
    one of these per byte (multiplicity = 1, assume side); the virtual
    `BinaryTable` provides them (multiplicity = -1, assert side). -/
structure BinaryTableEntry (F : Type) [Field F] where
  multiplicity : F
  /-- Position indicator: 2 = first byte; 1 = last byte (lowest of 64-bit
      result); 0 = middle byte. (See `binary_table.pil`'s `POS_IND` column.) -/
  pos_ind : F
  /-- Operation literal (`b_op` from the consumer; possibly the
      `b_op_or_sext` auxiliary in upper-bytes for sign-extension paths). -/
  op : F
  /-- Input A byte (8 bits). -/
  a_byte : F
  /-- Input B byte (8 bits). -/
  b_byte : F
  /-- Carry input (1 bit). -/
  cin : F
  /-- Output C byte (8 bits). -/
  c_byte : F
  /-- Combined flags byte: `cout + 2·result_is_a + 4·use_first_byte + 8·c_is_signed_byte`. -/
  flags : F
  deriving BEq, DecidableEq, Inhabited

/-! ## Trusted per-row well-formedness

  This is the openvm-fv `wf_properties` analog: the semantic relation the
  table guarantees for any row a consumer pulls. The relation is **trusted**
  — see file-level docstring and CLAUDE.md.

  The relation is structured as a conjunction of per-op implications, so a
  downstream consumer derives only the clauses for the opcodes it cares
  about. Each clause is the per-byte specification from
  `binary_table.pil`'s `for` loop. -/

/-- Range conditions on the byte slots (`a, b, c` are 8-bit; `cin` is 1-bit).
    Always asserted regardless of opcode. -/
def range_conditions (e : BinaryTableEntry FGL) : Prop :=
  e.a_byte.val < 256 ∧ e.b_byte.val < 256 ∧
  e.c_byte.val < 256 ∧ e.cin.val < 2

/-- Bitwise AND: `c = a &&& b`; `flags` low bit (cout) is 0;
    `result_is_a = 0`, `use_first_byte = 0`. AND ignores `cin`. -/
def wf_AND (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_AND →
    e.c_byte.val = (e.a_byte.val &&& e.b_byte.val) ∧
    e.flags.val % 2 = 0  -- cout = 0

/-- Bitwise OR: `c = a ||| b`; cout = 0. -/
def wf_OR (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_OR →
    e.c_byte.val = (e.a_byte.val ||| e.b_byte.val) ∧
    e.flags.val % 2 = 0

/-- Bitwise XOR: `c = a ^^^ b`; cout = 0. -/
def wf_XOR (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_XOR →
    e.c_byte.val = (e.a_byte.val ^^^ e.b_byte.val) ∧
    e.flags.val % 2 = 0

/-- Less-than unsigned (per-byte chain). On non-final bytes
    (`pos_ind = 0`), `c = 0` and the carry chain encodes the
    less-than/equal/greater outcome:
      * `cout = 1` if `a < b`,
      * `cout = cin` if `a == b`,
      * `cout = 0` if `a > b`.
    On the final byte (`pos_ind = 1` for 64-bit / `pos_ind = mode32` at
    half-byte boundary), the same chain rule applies and `c = 0`. The
    full 64-bit result is `cout` of the final byte (use_last_cout_as_c).
    Sign handling for signed `OP_LT` modifies the final-byte outcome
    when sign bytes differ. -/
def wf_LTU (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_LTU →
    e.c_byte.val = 0 ∧
    -- cout (low bit of flags) is the chain outcome
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0)

/-- Less-than signed: same byte-level chain as LTU on non-sign-byte
    positions; on the final byte (`pos_ind = 1` or `pos_ind = mode32`),
    if the high bits of `a` and `b` differ (sign-bytes opposite), the
    outcome is determined by the sign of `a`. The byte value `c` is 0. -/
def wf_LT (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_LT →
    e.c_byte.val = 0
    -- (full sign-byte-aware semantics deferred until needed downstream)

/-- Equality: `cout = 0` (is_eq) when `cin = 0 ∧ a = b`; `cout = 1`
    (is_neq) otherwise on non-final bytes. On the final byte the
    polarity flips: `cout := 1 - cout`. `c = 0` everywhere. -/
def wf_EQ (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_EQ →
    e.c_byte.val = 0
    -- (chain semantics deferred)

/-- Add: `c = (cin + a + b) mod 256`; on non-final bytes
    `cout = (cin + a + b) >> 8`; on the final byte `cout = 0`. -/
def wf_ADD (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_ADD →
    e.c_byte.val = (e.cin.val + e.a_byte.val + e.b_byte.val) % 256

/-- Subtract: borrow semantics. `c = 256·borrow + a - cin - b`,
    `cout = borrow` on non-final bytes, `cout = 0` on the final byte. -/
def wf_SUB (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_SUB →
    -- (full borrow semantics deferred until downstream needs it)
    e.c_byte.val < 256

/-- The full trusted per-row well-formedness: range plus all per-op
    clauses. Consumers pull out the clause for their opcode. Mirrors
    openvm-fv's `BitwiseBusEntryInstance.wf_properties` in shape;
    differs only in carrying multiple ops in one entry. -/
def wf_properties (e : BinaryTableEntry FGL) : Prop :=
  range_conditions e
  ∧ wf_AND e
  ∧ wf_OR e
  ∧ wf_XOR e
  ∧ wf_LTU e
  ∧ wf_LT e
  ∧ wf_EQ e
  ∧ wf_ADD e
  ∧ wf_SUB e

/-! ## Trusted axiom

  Bus-protocol soundness: any row consumed (multiplicity = 1) by a Binary
  AIR via the `bus_id = 125` lookup satisfies the per-row spec. This is the
  trusted bridge from "the prover accepts" to "the byte-level relation
  holds." Same role as `OperationBus.matches_entry` for `bus_id = 5000`.
-/

/-- **Trusted axiom (consumer-side).** Every entry the Binary AIR consumes
    against the binary table satisfies `wf_properties`. -/
axiom bin_table_consumer_wf
    (e : BinaryTableEntry FGL)
    (h_consumer : e.multiplicity = 1) :
    wf_properties e

end ZiskFv.Airs.BinaryTable
