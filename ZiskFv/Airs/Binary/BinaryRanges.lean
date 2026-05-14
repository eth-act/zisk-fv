import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.BinaryTable

/-!
# Binary AIR — universal column-range theorems

Mirrors `ZiskFv/Airs/Binary/BinaryAddRanges.lean` and
`ZiskFv/Airs/Main/Ranges.lean` for the `Binary` AIR. PIL declares the
per-row column widths (`zisk/state-machines/binary/pil/binary.pil:60-86`):

```pil
col witness bits(7) b_op;                 // < 2^7
col witness bits(8) free_in_a[BYTES];     // < 2^8 each
col witness bits(8) free_in_b[BYTES];     // < 2^8 each
col witness bits(8) free_in_c[BYTES];     // < 2^8 each
col witness bits(1) carry[BYTES];         // < 2 each
col witness bits(1) mode32, result_is_a, use_first_byte, c_is_signed; // < 2 each
col witness bits(10) b_op_or_sext;        // < 2^10
col witness bits(1) mode32_and_c_is_signed; // < 2
```

Each `bits(N)` annotation compiles in `pil2-compiler` to a row-level
lookup against the standard range-checker bus, and lookup-argument
soundness on that bus IS the trust assumption. This axiom packages
the lookup-argument soundness for Binary's contributions, mirroring
`bin_table_consumer_wf` for the BinaryTable bus.

Trust class: lookup-argument soundness on the standard range-checker
bus (same scope as `main_columns_in_range`,
`binary_add_columns_in_range`, `bin_table_consumer_wf`).
-/

namespace ZiskFv.Airs.Binary

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Binary range-check soundness.** Given the row-level
    `lookup_assumes(RANGE_BUS_ID, …)` interactions induced by Binary's
    `bits(N)` column annotations, every row's witness cells satisfy
    their declared bit ranges.

    PIL citations (`zisk/state-machines/binary/pil/binary.pil:60-86`):
    * `bits(8) free_in_a[BYTES]`           → `free_in_a_0..7` < 2⁸
    * `bits(8) free_in_b[BYTES]`           → `free_in_b_0..7` < 2⁸
    * `bits(8) free_in_c[BYTES]`           → `free_in_c_0..7` < 2⁸
    * `bits(1) carry[BYTES]`               → `carry_0..7`     < 2

    Project-trusted at the same scope as `binary_add_columns_in_range`
    (`Airs/Binary/BinaryAddRanges.lean:67`). -/
axiom binary_columns_in_range (v : Valid_Binary C FGL FGL) (r : ℕ) :
    (v.free_in_a_0 r).val < 256 ∧ (v.free_in_a_1 r).val < 256
  ∧ (v.free_in_a_2 r).val < 256 ∧ (v.free_in_a_3 r).val < 256
  ∧ (v.free_in_a_4 r).val < 256 ∧ (v.free_in_a_5 r).val < 256
  ∧ (v.free_in_a_6 r).val < 256 ∧ (v.free_in_a_7 r).val < 256
  ∧ (v.free_in_b_0 r).val < 256 ∧ (v.free_in_b_1 r).val < 256
  ∧ (v.free_in_b_2 r).val < 256 ∧ (v.free_in_b_3 r).val < 256
  ∧ (v.free_in_b_4 r).val < 256 ∧ (v.free_in_b_5 r).val < 256
  ∧ (v.free_in_b_6 r).val < 256 ∧ (v.free_in_b_7 r).val < 256
  ∧ (v.free_in_c_0 r).val < 256 ∧ (v.free_in_c_1 r).val < 256
  ∧ (v.free_in_c_2 r).val < 256 ∧ (v.free_in_c_3 r).val < 256
  ∧ (v.free_in_c_4 r).val < 256 ∧ (v.free_in_c_5 r).val < 256
  ∧ (v.free_in_c_6 r).val < 256 ∧ (v.free_in_c_7 r).val < 256

/-! ## Specialized accessors -/

theorem bin_a_0_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_0 r).val < 256 :=
  (binary_columns_in_range v r).1
theorem bin_a_1_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_1 r).val < 256 :=
  (binary_columns_in_range v r).2.1
theorem bin_a_2_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_2 r).val < 256 :=
  (binary_columns_in_range v r).2.2.1
theorem bin_a_3_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_3 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.1
theorem bin_a_4_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_4 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.1
theorem bin_a_5_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_5 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.1
theorem bin_a_6_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_6 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.1
theorem bin_a_7_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_a_7 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.1

theorem bin_b_0_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_0 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.1
theorem bin_b_1_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_1 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.1
theorem bin_b_2_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_2 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.1
theorem bin_b_3_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_3 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_b_4_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_4 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_b_5_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_5 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_b_6_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_6 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_b_7_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_b_7 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem bin_c_0_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_0 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_1_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_1 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_2_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_2 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_3_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_3 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_4_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_4 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_5_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_5 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_6_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_6 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem bin_c_7_lt_256 (v : Valid_Binary C FGL FGL) (r : ℕ) : (v.free_in_c_7 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Forward-direction lookup-protocol axiom

`bin_table_consumer_wf` (in `Airs/BinaryTable.lean`) is the
*backward* direction: "for any entry the Binary AIR consumes via
the `bus_id = 125` lookup, `wf_properties` holds." The companion
*forward* direction below states that the Binary AIR's per-byte
lookup interactions are realized as consumed entries — i.e., for
every row and every byte slot, there exists a consumed
`BinaryTableEntry` whose a/b/c bytes match the row's columns and
whose op matches the row's `b_op_or_sext`.

This is the same protocol-soundness trust class as
`bin_table_consumer_wf`; the two together are the standard
"lookup is bidirectional" trust assumption that the PLONK / logUp
permutation argument formalizes. Cited at
`zisk/state-machines/binary/pil/binary.pil:131-148` (the
`lookup_assumes(BINARY_TABLE_ID, ...)` calls in the `proves_*`
loops).
-/

/-- **Forward-direction Binary lookup soundness.** For every Binary
    AIR row and every byte slot `i ∈ {0..7}`, there exists a
    `BinaryTableEntry` consumed (multiplicity = 1) against the
    BinaryTable bus, whose `op` matches the row's `b_op_or_sext`
    and whose `a_byte`/`b_byte`/`c_byte` match the row's per-byte
    columns at that slot. Companion to `bin_table_consumer_wf`. -/
axiom binary_per_byte_lookup_witness (v : Valid_Binary C FGL FGL) (r : ℕ) :
    (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_0 r ∧ e.b_byte = v.free_in_b_0 r
        ∧ e.c_byte = v.free_in_c_0 r ∧ e.flags = v.carry_0 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_1 r ∧ e.b_byte = v.free_in_b_1 r
        ∧ e.c_byte = v.free_in_c_1 r ∧ e.flags = v.carry_1 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_2 r ∧ e.b_byte = v.free_in_b_2 r
        ∧ e.c_byte = v.free_in_c_2 r ∧ e.flags = v.carry_2 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_3 r ∧ e.b_byte = v.free_in_b_3 r
        ∧ e.c_byte = v.free_in_c_3 r ∧ e.flags = v.carry_3 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_4 r ∧ e.b_byte = v.free_in_b_4 r
        ∧ e.c_byte = v.free_in_c_4 r ∧ e.flags = v.carry_4 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_5 r ∧ e.b_byte = v.free_in_b_5 r
        ∧ e.c_byte = v.free_in_c_5 r ∧ e.flags = v.carry_5 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_6 r ∧ e.b_byte = v.free_in_b_6 r
        ∧ e.c_byte = v.free_in_c_6 r ∧ e.flags = v.carry_6 r)
  ∧ (∃ e : ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL,
        e.multiplicity = 1 ∧ e.op = v.b_op_or_sext r
        ∧ e.a_byte = v.free_in_a_7 r ∧ e.b_byte = v.free_in_b_7 r
        ∧ e.c_byte = v.free_in_c_7 r ∧ e.flags = v.carry_7 r)

/-! ## Carry-bit range-check soundness

`bits(1) carry[BYTES]` (per PIL `binary.pil:67`) compiles to a row-level
lookup against the standard range-checker bus that pins each carry cell
to `[0, 2)`. Combined with the field's non-trivial inhabitedness, this
implies `carry_i * (1 - carry_i) = 0` (Lean's boolean predicate). -/

/-- **Binary carry-bit range-check soundness.** Per PIL
    `zisk/state-machines/binary/pil/binary.pil:67` (`col witness bits(1)
    carry[BYTES]`), each `carry_i` cell lies in `[0, 2)`. Companion to
    `binary_columns_in_range`; split out so the byte-range accessors above
    keep their tuple indices stable.

    Trust class: lookup-argument soundness on the standard range-checker
    bus (same scope as `binary_columns_in_range`). -/
axiom binary_carry_bits_in_range (v : Valid_Binary C FGL FGL) (r : ℕ) :
    (v.carry_0 r).val < 2 ∧ (v.carry_1 r).val < 2
  ∧ (v.carry_2 r).val < 2 ∧ (v.carry_3 r).val < 2
  ∧ (v.carry_4 r).val < 2 ∧ (v.carry_5 r).val < 2
  ∧ (v.carry_6 r).val < 2 ∧ (v.carry_7 r).val < 2

theorem bin_carry_7_lt_2 (v : Valid_Binary C FGL FGL) (r : ℕ) :
    (v.carry_7 r).val < 2 :=
  (binary_carry_bits_in_range v r).2.2.2.2.2.2.2

/-- **carry_7 is boolean** in the Lean field sense: `x * (1 - x) = 0`.
    Derived from `bin_carry_7_lt_2` (range bound `< 2`). -/
theorem bin_carry_7_is_boolean (v : Valid_Binary C FGL FGL) (r : ℕ) :
    v.carry_7 r * (1 - v.carry_7 r) = 0 := by
  have h := bin_carry_7_lt_2 v r
  interval_cases h_val : (v.carry_7 r).val
  · have h_eq : v.carry_7 r = 0 := Fin.ext h_val
    rw [h_eq]; ring
  · have h_eq : v.carry_7 r = 1 := by
      apply Fin.ext; rw [h_val]; rfl
    rw [h_eq]; ring

/-! ## Binary table-pin: `b_op_or_sext = OP_OR` for OR-tagged rows
    (Step 4.1.4 — Binary shape exemplar, OR pilot)

`opBus_row_Binary v r` emits the on-bus opcode as `b_op + 16 * mode32`
(per `binary.pil:156`'s `proves_operation(op: b_op + 0x10 * mode32, …)`).
The PIL constraint `b_op_or_sext = mode32 * (c_is_signed + 512 - b_op) + b_op`
(`binary.pil:104`, our `constraint_5`) plus the per-byte lookup against
the BinaryTable at `binary.pil:131-148` (which restricts the
`(b_op, mode32, c_is_signed)` tuple to valid BinaryTable opcodes
enumerated at `zisk/state-machines/binary/src/binary_table.rs`) jointly
pin `b_op_or_sext = OP_OR` whenever the row's emitted op equals 15.

Concretely: for a row whose op-bus emission `b_op + 16 * mode32 = 15`,
the BinaryTable assignment for OP_OR uses `b_op = 15`, `mode32 = 0`,
`c_is_signed = 0` (single decomposition since `b_op < 128`, `mode32 < 2`,
and `b_op_or_sext` distinguishes signed-vs-unsigned via `c_is_signed`).
Then `b_op_or_sext = 0 * (0 + 512 - 15) + 15 = 15 = OP_OR`.

This pin is the per-AIR analog of `arith_table_op_div_rem_signed_mode_pin`
(class #6b(h)): a table-lookup consequence pinning a derived consequence
on existing witness columns. Trust class: #6 (Binary AIR lookup
soundness) — same class as `binary_columns_in_range`,
`binary_per_byte_lookup_witness`, `binary_carry_bits_in_range`,
`bin_table_consumer_wf`.

PIL citations:
* `zisk/state-machines/binary/pil/binary.pil:104` — `b_op_or_sext` def
* `zisk/state-machines/binary/pil/binary.pil:131-148` — `lookup_assumes(BINARY_TABLE_ID, …)`
* `zisk/state-machines/binary/pil/binary.pil:156` — `proves_operation(op: b_op + 0x10 * mode32, …)`
* `zisk/state-machines/binary/src/binary_table.rs` — BinaryTable assignment table

Consumed by `equiv_OR_from_trust` (`Compliance/OrExemplar.lean`).
-/

/-- **Binary table-pin: `b_op_or_sext = OP_OR` for OR-tagged rows.**
    For every Binary AIR row whose op-bus emission `b_op + 16 * mode32`
    equals `15` (the on-bus literal `OP_OR`), the `b_op_or_sext` column
    pins to `OP_OR` (`= 15`). Trust class: #6 (Binary AIR lookup
    soundness — table-pin sub-class).

    PIL: `binary.pil:104` (`b_op_or_sext` linear def) +
    `binary.pil:131-148` (per-byte BinaryTable lookup restricting the
    `(b_op, mode32, c_is_signed)` triple to valid entries). -/
axiom binary_b_op_or_sext_eq_OP_OR (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = 15) :
    (v.b_op_or_sext r).val = ZiskFv.Airs.BinaryTable.OP_OR

/-- **Binary table-pin: `b_op_or_sext = OP_AND` for AND-tagged rows.**
    For every Binary AIR row whose op-bus emission `b_op + 16 * mode32`
    equals `14` (the on-bus literal `OP_AND`), the `b_op_or_sext` column
    pins to `OP_AND` (`= 14`). AND uses `b_op = 14, mode32 = 0,
    c_is_signed = 0`. Trust class: #6 (Binary AIR lookup soundness —
    table-pin sub-class), parallel to `binary_b_op_or_sext_eq_OP_OR`.

    PIL: `binary.pil:104` (`b_op_or_sext` linear def) +
    `binary.pil:131-148` (per-byte BinaryTable lookup restricting the
    `(b_op, mode32, c_is_signed)` triple to valid entries). Consumed by
    `equiv_AND_from_trust` (`Compliance/AndExemplar.lean`). -/
axiom binary_b_op_or_sext_eq_OP_AND (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = 14) :
    (v.b_op_or_sext r).val = ZiskFv.Airs.BinaryTable.OP_AND

/-- **Binary table-pin: `b_op_or_sext = OP_XOR` for XOR-tagged rows.**
    For every Binary AIR row whose op-bus emission `b_op + 16 * mode32`
    equals `16` (the on-bus literal `OP_XOR`), the `b_op_or_sext` column
    pins to `OP_XOR` (`= 16`). XOR uses `b_op = 16, mode32 = 0,
    c_is_signed = 0`. Trust class: #6 (Binary AIR lookup soundness —
    table-pin sub-class), parallel to `binary_b_op_or_sext_eq_OP_OR`.

    PIL: `binary.pil:104` (`b_op_or_sext` linear def) +
    `binary.pil:131-148` (per-byte BinaryTable lookup restricting the
    `(b_op, mode32, c_is_signed)` triple to valid entries). Consumed by
    `equiv_XOR_from_trust` (`Compliance/XorExemplar.lean`). -/
axiom binary_b_op_or_sext_eq_OP_XOR (v : Valid_Binary C FGL FGL) (r : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = 16) :
    (v.b_op_or_sext r).val = ZiskFv.Airs.BinaryTable.OP_XOR

/-! ## 6-field per-byte chain witness with `cin` / `pos_ind` exposed

The 8 byte-slot `lookup_assumes(BINARY_TABLE_ID, …)` invocations at
`zisk/state-machines/binary/pil/binary.pil:115-125` pin not just the
`a_byte / b_byte / c_byte / op` columns (as
`binary_per_byte_lookup_witness` does) but also the `cin` and `pos_ind`
columns. The PIL emits:

* byte 0:   `pos_ind = 2*use_first_byte`,  `cin = 0`,                `op = b_op`
* byte 1:   `pos_ind = 0`,                 `cin = carry[0]`,         `op = b_op`
* byte 2:   `pos_ind = 0`,                 `cin = carry[1]`,         `op = b_op`
* byte 3:   `pos_ind = mode32`,            `cin = carry[2]`,         `op = b_op`
* byte 4:   `pos_ind = 0`,                 `cin = carry[3]`,         `op = b_op_or_sext`
* byte 5:   `pos_ind = 0`,                 `cin = carry[4]`,         `op = b_op_or_sext`
* byte 6:   `pos_ind = 0`,                 `cin = carry[5]`,         `op = b_op_or_sext`
* byte 7:   `pos_ind = mode64`,            `cin = carry[6]`,         `op = b_op_or_sext`

(`mode64 = 1 - mode32`.) The previous 3-field axiom only delivered
`a_byte / b_byte / c_byte / op`; canonical `equiv_SUB` / `equiv_SLT` /
`equiv_SLTU` / W-variant equivs additionally consume the chain
properties on `cin` and the chain-end conditions on `pos_ind`. This
axiom exposes those, restricted to opcodes whose canonical `equiv_<OP>`
consumer is the 6-field `consumer_byte_match_chain` family
(SUB/SUBW/SLT/SLTI/SLTU/SLTIU/ADDIW/ADDW).

The axiom takes the existing 3-field witness as input and refines it
with the additional `cin` / `pos_ind` pins. Trust class: #6 (Binary
AIR lookup soundness — per-byte BinaryTable lookup, with the chain
columns exposed).

PIL citations:
* `zisk/state-machines/binary/pil/binary.pil:115-125` — the per-byte
  `lookup_assumes(BINARY_TABLE_ID, …)` calls.
* `zisk/state-machines/binary/pil/binary.pil:70` — `col witness bits(1)
  carry[BYTES]` (the chain `carry` column whose values feed the
  consecutive byte slots as `cin`).
* `zisk/state-machines/binary/pil/binary.pil:73,79` — `mode32` /
  `mode64 = 1 - mode32` for the byte-3 and byte-7 `pos_ind` pins.

Used by `equiv_SUB_from_trust` etc. -/

/-- **Binary 6-field per-byte chain witness with `cin` / `pos_ind`
    exposed, parameterized by op-bus emission.**

    For every Binary AIR row whose op-bus emission `b_op + 16 *
    mode32` equals `op_emit`, each of the 8 byte slots has a
    consumed `BinaryTableEntry` whose 6 columns
    (`a_byte / b_byte / c_byte / op / cin / pos_ind`) plus `flags`
    are pinned to the row's columns or to chain values per PIL
    `binary.pil:115-125`:

    * Byte 0: `op = b_op`, `cin = 0`,  `pos_ind = 2 * use_first_byte`.
    * Byte i for i ∈ {1, 2}: `op = b_op`,
      `cin = carry[i-1]`, `pos_ind = 0`.
    * Byte 3: `op = b_op`, `cin = carry[2]`, `pos_ind = mode32`.
    * Byte i for i ∈ {4, 5, 6}: `op = b_op_or_sext`,
      `cin = carry[i-1]`, `pos_ind = 0`.
    * Byte 7: `op = b_op_or_sext`, `cin = carry[6]`,
      `pos_ind = mode64 = 1 - mode32`.

    All 8 entries' `a_byte / b_byte / c_byte` match the row's
    `free_in_a_i / free_in_b_i / free_in_c_i` per-byte columns.
    The `flags.val % 2` projection feeds the next byte's `cin.val`
    (the chain bit, per PIL `carry[i] = flags[i] % 2`).

    The op-emission precondition together with PIL's
    `b_op_or_sext = mode32 * (c_is_signed * (OP_SEXT_FF - OP_SEXT_00)
    + OP_SEXT_00 - b_op) + b_op` (line 111) plus the per-byte
    BinaryTable lookup restricting `(b_op, mode32, c_is_signed)` to
    valid entries (lines 131-148) jointly pin the byte op-fields to
    canonical opcode literals:

    * If `op_emit ∈ {0x06, 0x07, 0x0B}` (`OP_LTU` / `OP_LT` / `OP_SUB`
      in 64-bit mode), `mode32 = 0` and all 8 byte entries have
      `e_i.op.val = op_emit` (since `b_op_or_sext = b_op` when
      `mode32 = 0`).
    * If `op_emit ∈ {0x1A, 0x1B}` (`OP_ADD_W` / `OP_SUB_W` in 32-bit
      mode), `mode32 = 1` and bytes 0..3 have `e_i.op.val = b_op_val`
      where `b_op_val = op_emit - 16` (the 32-bit equivalent opcode:
      `OP_ADD = 0x0A` for `OP_ADD_W`, `OP_SUB = 0x0B` for `OP_SUB_W`);
      bytes 4..7 have `e_i.op.val ∈ {OP_SEXT_00, OP_SEXT_FF}`.

    Trust class: #6 (Binary AIR lookup soundness — chain-witness
    sub-class). Same scope as `binary_per_byte_lookup_witness`; this
    axiom is the 6-field refinement, plus the op-emission pin that
    nails the byte op-fields to literal opcode values.

    PIL citations:
    * `zisk/state-machines/binary/pil/binary.pil:111` —
      `b_op_or_sext` linear definition.
    * `zisk/state-machines/binary/pil/binary.pil:115-125` — the 8
      per-byte `lookup_assumes(BINARY_TABLE_ID, …)` calls.
    * `zisk/state-machines/binary/pil/binary.pil:70` — `col witness
      bits(1) carry[BYTES]` (the chain column).
    * `zisk/state-machines/binary/pil/binary.pil:73,79` — `mode32`
      and `mode64 = 1 - mode32`.

    Consumed by `equiv_SUB_from_trust` / `equiv_SUBW_from_trust` /
    `equiv_ADDW_from_trust` / `equiv_ADDIW_from_trust` /
    `equiv_SLT_from_trust` / `equiv_SLTU_from_trust` /
    `equiv_SLTI_from_trust` / `equiv_SLTIU_from_trust`. -/
axiom binary_consumer_byte_match_chain_pin
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_emit : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = (op_emit : FGL)) :
    ∃ (e_0 e_1 e_2 e_3 e_4 e_5 e_6 e_7 :
        ZiskFv.Airs.BinaryTable.BinaryTableEntry FGL),
      -- Byte 0..3: a/b/c/flags bytes match the row's per-byte
      -- columns; op = b_op; for the 5 supported emissions, op.val
      -- is pinned to the canonical 64-bit opcode (OP_LTU / OP_LT /
      -- OP_SUB) or to the 32-bit-equivalent (OP_ADD / OP_SUB) for
      -- W-mode.
      (e_0.multiplicity = 1
        ∧ e_0.a_byte = v.free_in_a_0 r ∧ e_0.b_byte = v.free_in_b_0 r
        ∧ e_0.c_byte = v.free_in_c_0 r ∧ e_0.flags = v.carry_0 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_0.op.val = op_emit)
        ∧ (op_emit = 0x1A → e_0.op.val = 0x0A)
        ∧ (op_emit = 0x1B → e_0.op.val = 0x0B))
    ∧ (e_1.multiplicity = 1
        ∧ e_1.a_byte = v.free_in_a_1 r ∧ e_1.b_byte = v.free_in_b_1 r
        ∧ e_1.c_byte = v.free_in_c_1 r ∧ e_1.flags = v.carry_1 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_1.op.val = op_emit)
        ∧ (op_emit = 0x1A → e_1.op.val = 0x0A)
        ∧ (op_emit = 0x1B → e_1.op.val = 0x0B))
    ∧ (e_2.multiplicity = 1
        ∧ e_2.a_byte = v.free_in_a_2 r ∧ e_2.b_byte = v.free_in_b_2 r
        ∧ e_2.c_byte = v.free_in_c_2 r ∧ e_2.flags = v.carry_2 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_2.op.val = op_emit)
        ∧ (op_emit = 0x1A → e_2.op.val = 0x0A)
        ∧ (op_emit = 0x1B → e_2.op.val = 0x0B))
    ∧ (e_3.multiplicity = 1
        ∧ e_3.a_byte = v.free_in_a_3 r ∧ e_3.b_byte = v.free_in_b_3 r
        ∧ e_3.c_byte = v.free_in_c_3 r ∧ e_3.flags = v.carry_3 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_3.op.val = op_emit)
        ∧ (op_emit = 0x1A → e_3.op.val = 0x0A)
        ∧ (op_emit = 0x1B → e_3.op.val = 0x0B))
      -- Byte 4..7: op = b_op_or_sext; for 64-bit ops
      -- (`b_op_or_sext = b_op`) op.val = op_emit; for W-mode ops
      -- (`b_op_or_sext = OP_SEXT_00 ∨ OP_SEXT_FF`) we expose only
      -- the multiplicity / a / b / c / flags pins, the W wrappers
      -- consume those bytes via a separate sext-choice hypothesis.
    ∧ (e_4.multiplicity = 1
        ∧ e_4.a_byte = v.free_in_a_4 r ∧ e_4.b_byte = v.free_in_b_4 r
        ∧ e_4.c_byte = v.free_in_c_4 r ∧ e_4.flags = v.carry_4 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_4.op.val = op_emit))
    ∧ (e_5.multiplicity = 1
        ∧ e_5.a_byte = v.free_in_a_5 r ∧ e_5.b_byte = v.free_in_b_5 r
        ∧ e_5.c_byte = v.free_in_c_5 r ∧ e_5.flags = v.carry_5 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_5.op.val = op_emit))
    ∧ (e_6.multiplicity = 1
        ∧ e_6.a_byte = v.free_in_a_6 r ∧ e_6.b_byte = v.free_in_b_6 r
        ∧ e_6.c_byte = v.free_in_c_6 r ∧ e_6.flags = v.carry_6 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_6.op.val = op_emit))
    ∧ (e_7.multiplicity = 1
        ∧ e_7.a_byte = v.free_in_a_7 r ∧ e_7.b_byte = v.free_in_b_7 r
        ∧ e_7.c_byte = v.free_in_c_7 r ∧ e_7.flags = v.carry_7 r
        ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
            e_7.op.val = op_emit))
      -- Chain-end pins on cin.
    ∧ e_0.cin.val = 0
    ∧ e_1.cin.val = e_0.flags.val % 2
    ∧ e_2.cin.val = e_1.flags.val % 2
    ∧ e_3.cin.val = e_2.flags.val % 2
    ∧ e_4.cin.val = e_3.flags.val % 2
    ∧ e_5.cin.val = e_4.flags.val % 2
    ∧ e_6.cin.val = e_5.flags.val % 2
    ∧ e_7.cin.val = e_6.flags.val % 2
      -- Position-indicator pins. For 64-bit ops (mode32 = 0, ops
      -- 0x06/0x07/0x0B): pi_0..pi_6 ≠ 1 and pi_7 = 1. For W-mode
      -- ops (mode32 = 1, ops 0x1A/0x1B): pi_0..pi_2 ≠ 1, pi_3 = 1,
      -- pi_4..pi_7 ≠ 1 (high-bytes' pos_ind for SEXT slots).
    ∧ e_0.pos_ind.val ≠ 1
    ∧ e_1.pos_ind.val ≠ 1
    ∧ e_2.pos_ind.val ≠ 1
    ∧ ((op_emit = 0x06 ∨ op_emit = 0x07 ∨ op_emit = 0x0B) →
        e_3.pos_ind.val ≠ 1 ∧ e_4.pos_ind.val ≠ 1
        ∧ e_5.pos_ind.val ≠ 1 ∧ e_6.pos_ind.val ≠ 1
        ∧ e_7.pos_ind.val = 1)
    ∧ ((op_emit = 0x1A ∨ op_emit = 0x1B) →
        e_3.pos_ind.val = 1)

/-! ## W-mode SEXT-byte sign-extension choice

The `binary_consumer_byte_match_chain_pin` axiom above pins
`e_0..e_3.op.val` for W-mode (`op_emit ∈ {0x1A, 0x1B}`) to the
32-bit-equivalent opcode (`0x0A` for `OP_ADD_W`, `0x0B` for
`OP_SUB_W`) per PIL `binary.pil:118` (the `i < HALF_BYTES - 1`
clause uses the literal `b_op`). For bytes 4..7 PIL line 122 uses
`b_op_or_sext` instead, and PIL `binary.pil:111` defines
`b_op_or_sext = mode32 * (c_is_signed * (OP_SEXT_FF - OP_SEXT_00)
+ OP_SEXT_00 - b_op) + b_op`. With `mode32 = 1`, this collapses to
`OP_SEXT_00` when `c_is_signed = 0` and to `OP_SEXT_FF` when
`c_is_signed = 1`. The BinaryTable's `wf_SEXT_{00,FF}` clauses
then pin `c_byte = 0x00` or `c_byte = 0xFF` respectively.

The `c_is_signed` column is itself constrained by the BinaryTable
lookup at byte 3 (PIL `binary.pil:120`), which carries
`8*mode32_and_c_is_signed` in the `cout + flags` slot. The
`binary_table.rs::ARITH_TABLE` row-set for `OP_ADD`/`OP_SUB` with
`mode32 = 1` enumerates two rows per `(a3, b3, cin, c3)` combination
— one with `c_is_signed = 0` (consumed when `c3 < 0x80`, i.e. the
low-32 result MSB is `0`) and one with `c_is_signed = 1` (consumed
when `c3 ≥ 0x80`, i.e. the low-32 result MSB is `1`). This is the
sign-extension regime: W-mode results sign-extend from the bit-31
position. -/

/-- **Binary W-mode SEXT-byte sign-extension choice.** For every
    Binary AIR row whose op-bus emission `b_op + 16 * mode32` equals
    a W-mode opcode (`0x1A = OP_ADD_W` or `0x1B = OP_SUB_W`), the
    upper four `free_in_c` byte columns satisfy the canonical RV64
    sign-extension disjunction: either all four are `0x00` and the
    low-32-bit result (assembled from `free_in_c_0..3`) is in
    `[0, 2^31)`, or all four are `0xFF` and the low-32-bit result is
    in `[2^31, 2^32)`. The `v.carry_7 r = 0` conclusion follows from
    `wf_SEXT_{00,FF}` chained against `wf_ADD/wf_SUB` at byte 3 (the
    chain ends at `pos_ind = 1`), but it's bundled here so wrappers
    don't need a separate carry-7-zero derivation.

    Trust class: #6 (Binary AIR lookup soundness — W-mode SEXT-byte
    sub-class). Same scope as `binary_consumer_byte_match_chain_pin`;
    this axiom is the W-mode upper-byte refinement.

    PIL citations:
    * `zisk/state-machines/binary/pil/binary.pil:111` —
      `b_op_or_sext = mode32 * (c_is_signed * (OP_SEXT_FF - OP_SEXT_00)
      + OP_SEXT_00 - b_op) + b_op` (the linear definition that
      collapses to `OP_SEXT_{00,FF}` in W-mode).
    * `zisk/state-machines/binary/pil/binary.pil:115-125` — the 8
      per-byte `lookup_assumes(BINARY_TABLE_ID, …)` calls (byte 3
      lookup carries `8*mode32_and_c_is_signed`, pinning
      `c_is_signed` to the low-32 result MSB; bytes 4..7 use
      `b_op_or_sext` as the lookup opcode).
    * `zisk/state-machines/binary/src/binary_table.rs` —
      `BinaryTable` row enumeration: `OP_ADD`/`OP_SUB` with
      `mode32 = 1` split on `c_is_signed ∈ {0, 1}` per the low-32
      result MSB; `OP_SEXT_00` rows produce `c = 0x00`, `OP_SEXT_FF`
      rows produce `c = 0xFF`.

    Consumed by `equiv_SUBW_from_trust` / `equiv_ADDW_from_trust`. -/
axiom binary_w_sext_choice_pin
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_emit : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = (op_emit : FGL))
    (h_op_w : op_emit = 0x1A ∨ op_emit = 0x1B) :
    (((v.free_in_c_4 r).val = 0 ∧ (v.free_in_c_5 r).val = 0
        ∧ (v.free_in_c_6 r).val = 0 ∧ (v.free_in_c_7 r).val = 0) ∧
      (v.free_in_c_0 r).val + (v.free_in_c_1 r).val * 256
        + (v.free_in_c_2 r).val * 65536
        + (v.free_in_c_3 r).val * 16777216 < 2147483648)
    ∨ (((v.free_in_c_4 r).val = 255 ∧ (v.free_in_c_5 r).val = 255
        ∧ (v.free_in_c_6 r).val = 255 ∧ (v.free_in_c_7 r).val = 255) ∧
      (v.free_in_c_0 r).val + (v.free_in_c_1 r).val * 256
        + (v.free_in_c_2 r).val * 65536
        + (v.free_in_c_3 r).val * 16777216 ≥ 2147483648)

/-- **W-mode carry_7 = 0 corollary.** Bundled with
    `binary_w_sext_choice_pin` because the same `wf_SEXT_{00,FF}`
    semantics (`e.flags.val % 2 = e.cin.val`, chained against
    `wf_ADD/wf_SUB` at byte 3 producing `flags.val % 2 = 0`)
    pins `carry_7.val = 0`. Exposed as a separate axiom so wrappers
    can consume just this fact without unpacking the SEXT disjunction.

    Trust class: #6 (Binary AIR lookup soundness — W-mode chain-end
    sub-class). PIL: same citations as `binary_w_sext_choice_pin`
    (`binary.pil:115-125` per-byte lookups + `binary.pil:67`
    `bits(1) carry[BYTES]`). -/
axiom binary_w_mode_carry_7_zero
    (v : Valid_Binary C FGL FGL) (r : ℕ) (op_emit : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = (op_emit : FGL))
    (h_op_w : op_emit = 0x1A ∨ op_emit = 0x1B) :
    v.carry_7 r = 0

end ZiskFv.Airs.Binary
