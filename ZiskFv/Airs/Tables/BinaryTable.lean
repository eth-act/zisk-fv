import Mathlib

import ZiskFv.Field.Goldilocks

/-!
ZisK binary lookup table (`bus_id = 125`).

The `Binary` AIR (pilout idx 10) emits one 7-tuple per byte against
`BINARY_TABLE_ID = 125`:

  `[pos_ind, b_op, a_byte, b_byte, cin, c_byte, flags]`

where `flags = cout + 2·result_is_a + 4·use_first_byte + 8·c_is_signed_byte`.
The provider side is the fixed virtual table defined by
`zisk/state-machines/binary/pil/binary_table.pil`'s deterministic
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

namespace ZiskFv.Airs.Tables.BinaryTable

open Goldilocks

/-! ## Op literals (from `zisk/pil/operations.pil`) -/

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

/-- Less-than unsigned (per-byte chain). The chain rule applies
    uniformly to every byte position (PIL `OP_LTU` branch never
    branches on `pos_ind`). At every byte:
      * `c_byte = 0`,
      * `cout = 1` if `a < b`,
      * `cout = cin` if `a == b`,
      * `cout = 0` if `a > b`.
    Composing 8 byte-entries via `cin[0] = 0`, `cin[i+1] = cout[i]`
    aggregates the chain to `cout[7] = 1 iff a64 < b64 (unsigned)`.
    The final-byte aggregation is therefore implicit in the chain rule
    and a downstream consumer derives it by induction on the byte
    chain (see `binary_ltu_chunks_eq_bv_ult`). -/
def wf_LTU (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_LTU →
    e.c_byte.val = 0 ∧
    -- cout (low bit of flags) is the chain outcome
    (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
    (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
    (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0)

/-- Less-than signed. Non-final bytes use the same byte-level chain rule
    as LTU. On the final byte (`pos_ind.val = 1`), same-sign bytes still
    use the unsigned chain rule, while sign-differing bytes override the
    chain outcome: `cout = 1` iff `a` is negative.

    Spec from `binary_table.pil`'s `case OP_LT` branch (lines 197–213):
      `if (a < b) cout = 1; else if (a == b) cout = cin; else cout = 0;`
      `c = 0;`
      `if (op == OP_LT && plast && (a & SIGN_BYTE) != (b & SIGN_BYTE))
         cout = (a & SIGN_BYTE) ? 1 : 0;` -/
def wf_LT (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_LT →
    e.c_byte.val = 0 ∧
    -- Chain rule (same as LTU) unless the final-byte sign override fires.
    (e.pos_ind.val ≠ 1 ∨ (e.a_byte.val &&& 0x80) = (e.b_byte.val &&& 0x80) →
      (e.a_byte.val < e.b_byte.val → e.flags.val % 2 = 1) ∧
      (e.a_byte.val = e.b_byte.val → e.flags.val % 2 = e.cin.val) ∧
      (e.a_byte.val > e.b_byte.val → e.flags.val % 2 = 0)) ∧
    -- Final-byte sign-byte override: at pos_ind = 1, when sign bits of
    -- a and b differ, cout = sign-bit of a.
    (e.pos_ind.val = 1 →
      (e.a_byte.val &&& 0x80) ≠ (e.b_byte.val &&& 0x80) →
      e.flags.val % 2 = (if (e.a_byte.val &&& 0x80) ≠ 0 then 1 else 0))

/-- Equality: per-byte rule with polarity flip at the final byte.
    Spec from `binary_table.pil`'s `case OP_EQ` branch (lines 233–247):

      `if (cin == 0 && a == b) cout = 0; else cout = 1;`  // is_eq / is_neq
      `c = 0;`
      `if (plast) cout = 1 - cout;`

    So at non-final bytes (`pos_ind.val ≠ 1`):
      `cout = 0 iff (cin = 0 ∧ a = b)`, else `cout = 1`.
    At the final byte (`pos_ind.val = 1`) the polarity is flipped:
      `cout = 1 iff (cin = 0 ∧ a = b)`, else `cout = 0`. -/
def wf_EQ (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_EQ →
    e.c_byte.val = 0 ∧
    -- Non-final byte rule.
    (e.pos_ind.val ≠ 1 →
      ((e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 0) ∧
      (¬ (e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 1)) ∧
    -- Final-byte rule (polarity flipped).
    (e.pos_ind.val = 1 →
      ((e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 1) ∧
      (¬ (e.cin.val = 0 ∧ e.a_byte.val = e.b_byte.val) → e.flags.val % 2 = 0))

/-- Add: `c = (cin + a + b) mod 256`; on non-final bytes
    `cout = (cin + a + b) >> 8` (i.e., `flags % 2 = (cin + a + b) / 256`);
    on the final byte (`pos_ind.val = 1`) `cout = 0`. -/
def wf_ADD (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_ADD →
    e.c_byte.val = (e.cin.val + e.a_byte.val + e.b_byte.val) % 256 ∧
    (e.pos_ind.val ≠ 1 →
      e.flags.val % 2 = (e.cin.val + e.a_byte.val + e.b_byte.val) / 256) ∧
    (e.pos_ind.val = 1 → e.flags.val % 2 = 0)

/-- Subtract: full borrow semantics from `binary_table.pil`'s
    `case OP_SUB` branch (lines 260–269):

      `borrow = if (a - cin) < b then 1 else 0`
      `c = 256·borrow + a - cin - b`
      `cout = plast ? 0 : borrow`

    Encoded as: `c_byte` equals the borrow-corrected difference, and
    on non-final bytes (`pos_ind.val ≠ 1`) the cout is the borrow
    (`flags % 2 = borrow`); on the final byte (`pos_ind.val = 1`),
    cout is forced to 0.

    The `borrow` value is derived structurally: it equals 1 iff
    `a.val < cin.val + b.val`. -/
def wf_SUB (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_SUB →
    -- Byte value equation. The PIL formula `c = 256·borrow + a - cin - b`
    -- works in signed integers; in ℕ we phrase it via the borrow case
    -- split:
    --   if a.val ≥ cin.val + b.val: c.val = a.val - cin.val - b.val
    --   else: c.val = 256 + a.val - cin.val - b.val
    (e.a_byte.val ≥ e.cin.val + e.b_byte.val →
      e.c_byte.val = e.a_byte.val - e.cin.val - e.b_byte.val) ∧
    (e.a_byte.val < e.cin.val + e.b_byte.val →
      e.c_byte.val = 256 + e.a_byte.val - e.cin.val - e.b_byte.val) ∧
    -- Non-final byte: cout = borrow.
    (e.pos_ind.val ≠ 1 →
      (e.a_byte.val ≥ e.cin.val + e.b_byte.val → e.flags.val % 2 = 0) ∧
      (e.a_byte.val < e.cin.val + e.b_byte.val → e.flags.val % 2 = 1)) ∧
    -- Final byte: cout = 0 unconditionally.
    (e.pos_ind.val = 1 → e.flags.val % 2 = 0)

/-- Sign-extend with `0x00` (auxiliary, used in W-mode upper bytes for
    non-negative low-half results). Spec from `binary_table.pil`'s
    `case OP_SEXT_00` branch (lines 309–315): `cout = cin; c = 0x00`. -/
def wf_SEXT_00 (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_SEXT_00 →
    e.c_byte.val = 0x00 ∧
    e.flags.val % 2 = e.cin.val

/-- Sign-extend with `0xFF` (auxiliary, used in W-mode upper bytes for
    negative low-half results). Spec from `binary_table.pil`'s
    `case OP_SEXT_FF` branch (lines 317–323): `cout = cin; c = 0xFF`. -/
def wf_SEXT_FF (e : BinaryTableEntry FGL) : Prop :=
  e.op.val = OP_SEXT_FF →
    e.c_byte.val = 0xFF ∧
    e.flags.val % 2 = e.cin.val

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
  ∧ wf_SEXT_00 e
  ∧ wf_SEXT_FF e

end ZiskFv.Airs.Tables.BinaryTable
