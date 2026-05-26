import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Tables.BinaryTable
import ZiskFv.Channels.RangeBusSoundness

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
open ZiskFv.Channels.RangeBusSoundness


/-- **Binary range-check soundness (derived).** Given the row-level
    `lookup_assumes(RANGE_BUS_ID, …)` interactions induced by Binary's
    `bits(N)` column annotations, every row's witness cells satisfy
    their declared bit ranges.

    Previously an axiom; now derived from `range_bus_sound` via 24
    applications (one per byte column).

    PIL citations (`zisk/state-machines/binary/pil/binary.pil:60-86`):
    * `bits(8) free_in_a[BYTES]`           → `free_in_a_0..7` < 2⁸
    * `bits(8) free_in_b[BYTES]`           → `free_in_b_0..7` < 2⁸
    * `bits(8) free_in_c[BYTES]`           → `free_in_c_0..7` < 2⁸ -/
theorem binary_columns_in_range (v : Valid_Binary FGL FGL) (r : ℕ) :
    (v.free_in_a_0 r).val < U8_max ∧ (v.free_in_a_1 r).val < U8_max
  ∧ (v.free_in_a_2 r).val < U8_max ∧ (v.free_in_a_3 r).val < U8_max
  ∧ (v.free_in_a_4 r).val < U8_max ∧ (v.free_in_a_5 r).val < U8_max
  ∧ (v.free_in_a_6 r).val < U8_max ∧ (v.free_in_a_7 r).val < U8_max
  ∧ (v.free_in_b_0 r).val < U8_max ∧ (v.free_in_b_1 r).val < U8_max
  ∧ (v.free_in_b_2 r).val < U8_max ∧ (v.free_in_b_3 r).val < U8_max
  ∧ (v.free_in_b_4 r).val < U8_max ∧ (v.free_in_b_5 r).val < U8_max
  ∧ (v.free_in_b_6 r).val < U8_max ∧ (v.free_in_b_7 r).val < U8_max
  ∧ (v.free_in_c_0 r).val < U8_max ∧ (v.free_in_c_1 r).val < U8_max
  ∧ (v.free_in_c_2 r).val < U8_max ∧ (v.free_in_c_3 r).val < U8_max
  ∧ (v.free_in_c_4 r).val < U8_max ∧ (v.free_in_c_5 r).val < U8_max
  ∧ (v.free_in_c_6 r).val < U8_max ∧ (v.free_in_c_7 r).val < 256 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact range_bus_sound v (fun v r => v.free_in_a_0 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_1 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_2 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_3 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_4 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_5 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_6 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_a_7 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_0 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_1 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_2 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_3 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_4 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_5 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_6 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_b_7 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_0 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_1 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_2 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_3 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_4 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_5 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_6 r) 8 trivial r
    | exact range_bus_sound v (fun v r => v.free_in_c_7 r) 8 trivial r

/-! ## Specialized accessors -/

lemma bin_b_op_lt_128 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.b_op r).val < 128 :=
  range_bus_sound v (fun v r => v.b_op r) 7 trivial r

lemma bin_mode32_lt_2 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.mode32 r).val < 2 :=
  range_bus_sound v (fun v r => v.mode32 r) 1 trivial r

lemma bin_a_0_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_0 r).val < 256 :=
  (binary_columns_in_range v r).1
lemma bin_a_1_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_1 r).val < 256 :=
  (binary_columns_in_range v r).2.1
lemma bin_a_2_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_2 r).val < 256 :=
  (binary_columns_in_range v r).2.2.1
lemma bin_a_3_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_3 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.1
lemma bin_a_4_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_4 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.1
lemma bin_a_5_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_5 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.1
lemma bin_a_6_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_6 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.1
lemma bin_a_7_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_a_7 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.1

lemma bin_b_0_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_0 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.1
lemma bin_b_1_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_1 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.1
lemma bin_b_2_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_2 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.1
lemma bin_b_3_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_3 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_b_4_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_4 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_b_5_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_5 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_b_6_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_6 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_b_7_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_b_7 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma bin_c_0_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_0 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_1_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_1 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_2_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_2 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_3_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_3 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_4_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_4 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_5_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_5 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_6_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_6 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma bin_c_7_lt_256 (v : Valid_Binary FGL FGL) (r : ℕ) : (v.free_in_c_7 r).val < 256 :=
  (binary_columns_in_range v r).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Carry-bit range-check soundness

`bits(1) carry[BYTES]` (per PIL `binary.pil:67`) compiles to a row-level
lookup against the standard range-checker bus that pins each carry cell
to `[0, 2)`. Combined with the field's non-trivial inhabitedness, this
implies `carry_i * (1 - carry_i) = 0` (Lean's boolean predicate). -/

/-- **Binary carry-bit range-check soundness (derived).** Per PIL
    `zisk/state-machines/binary/pil/binary.pil:67` (`col witness bits(1)
    carry[BYTES]`), each `carry_i` cell lies in `[0, 2)`. Companion to
    `binary_columns_in_range`; previously an axiom, now derived from
    `range_bus_sound` via 8 applications. -/
theorem binary_carry_bits_in_range (v : Valid_Binary FGL FGL) (r : ℕ) :
    (v.carry_0 r).val < U1_max ∧ (v.carry_1 r).val < U1_max
  ∧ (v.carry_2 r).val < U1_max ∧ (v.carry_3 r).val < U1_max
  ∧ (v.carry_4 r).val < U1_max ∧ (v.carry_5 r).val < U1_max
  ∧ (v.carry_6 r).val < U1_max ∧ (v.carry_7 r).val < U1_max := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact range_bus_sound v (fun v r => v.carry_0 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_1 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_2 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_3 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_4 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_5 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_6 r) 1 trivial r
  · exact range_bus_sound v (fun v r => v.carry_7 r) 1 trivial r

lemma bin_carry_7_lt_2 (v : Valid_Binary FGL FGL) (r : ℕ) :
    (v.carry_7 r).val < 2 :=
  (binary_carry_bits_in_range v r).2.2.2.2.2.2.2

/-- **carry_7 is boolean** in the Lean field sense: `x * (1 - x) = 0`.
    Derived from `bin_carry_7_lt_2` (range bound `< 2`). -/
lemma bin_carry_7_is_boolean (v : Valid_Binary FGL FGL) (r : ℕ) :
    v.carry_7 r * (1 - v.carry_7 r) = 0 := by
  have h := bin_carry_7_lt_2 v r
  interval_cases h_val : (v.carry_7 r).val
  · have h_eq : v.carry_7 r = 0 := Fin.ext h_val
    rw [h_eq]; ring
  · have h_eq : v.carry_7 r = 1 := by
      apply Fin.ext; rw [h_val]; rfl
    rw [h_eq]; ring

/-! ## Binary table-pin: `b_op_or_sext = OP_OR` for OR-tagged rows
   

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

Consumed by `equiv_OR` (`Compliance/Wrappers/Or.lean`).
-/

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

    Consumed by `equiv_SUBW` / `equiv_ADDW`. -/
axiom binary_w_sext_choice_pin
    (v : Valid_Binary FGL FGL) (r : ℕ) (op_emit : ℕ)
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
    (v : Valid_Binary FGL FGL) (r : ℕ) (op_emit : ℕ)
    (h_emit_op : v.b_op r + 16 * v.mode32 r = (op_emit : FGL))
    (h_op_w : op_emit = 0x1A ∨ op_emit = 0x1B) :
    v.carry_7 r = 0

end ZiskFv.Airs.Binary
