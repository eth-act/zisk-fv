import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect

/-!
# BinaryExtension AIR — universal column-range theorems

Mirrors `ZiskFv/Airs/Binary/BinaryRanges.lean` for the
`BinaryExtension` AIR. PIL declares the per-row column widths
(`zisk/state-machines/binary/pil/binary_extension.pil:82-96`):

```pil
col witness bits(6)  op;
col witness bits(8)  free_in_a[BYTES];    // < 2^8 each (8 bytes)
col witness bits(8)  free_in_b;           // < 2^8 (single shift-amount byte)
col witness bits(32) free_in_c[BYTES][2]; // < 2^32 each (16 entries: 8 byte_i × {c_lo, c_hi})
col witness bits(1)  op_is_shift;         // < 2
col witness bits(32) b[2];                // < 2^32 each
```

Each `bits(N)` annotation compiles in `pil2-compiler` to a row-level
lookup against the standard range-checker bus; lookup-argument
soundness on that bus IS the trust assumption (same class as
`binary_columns_in_range`, `binary_add_columns_in_range`,
`main_columns_in_range`, `bin_table_consumer_wf`).

Trust class: lookup-argument soundness on the standard range-checker
bus.
-/

namespace ZiskFv.Airs.BinaryExtension

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **BinaryExtension range-check soundness.** Given the row-level
    `lookup_assumes(RANGE_BUS_ID, …)` interactions induced by
    BinaryExtension's `bits(N)` column annotations, every row's
    witness cells satisfy their declared bit ranges.

    PIL citations (`zisk/state-machines/binary/pil/binary_extension.pil:82-96`):
    * `bits(8) free_in_a[BYTES]` → `free_in_a_0..7` < 2⁸
    * `bits(8) free_in_b`        → `free_in_b`     < 2⁸
    * `bits(32) free_in_c[BYTES][2]` → `free_in_c_0..15` < 2³²
    * `bits(32) b[2]`            → `b_0`, `b_1`    < 2³²

    Project-trusted at the same scope as `binary_columns_in_range`. -/
axiom binary_extension_columns_in_range (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_0 r).val < 256 ∧ (e.free_in_a_1 r).val < 256
  ∧ (e.free_in_a_2 r).val < 256 ∧ (e.free_in_a_3 r).val < 256
  ∧ (e.free_in_a_4 r).val < 256 ∧ (e.free_in_a_5 r).val < 256
  ∧ (e.free_in_a_6 r).val < 256 ∧ (e.free_in_a_7 r).val < 256
  ∧ (e.free_in_b r).val < 256
  ∧ (e.free_in_c_0 r).val < 4294967296 ∧ (e.free_in_c_1 r).val < 4294967296
  ∧ (e.free_in_c_2 r).val < 4294967296 ∧ (e.free_in_c_3 r).val < 4294967296
  ∧ (e.free_in_c_4 r).val < 4294967296 ∧ (e.free_in_c_5 r).val < 4294967296
  ∧ (e.free_in_c_6 r).val < 4294967296 ∧ (e.free_in_c_7 r).val < 4294967296
  ∧ (e.free_in_c_8 r).val < 4294967296 ∧ (e.free_in_c_9 r).val < 4294967296
  ∧ (e.free_in_c_10 r).val < 4294967296 ∧ (e.free_in_c_11 r).val < 4294967296
  ∧ (e.free_in_c_12 r).val < 4294967296 ∧ (e.free_in_c_13 r).val < 4294967296
  ∧ (e.free_in_c_14 r).val < 4294967296 ∧ (e.free_in_c_15 r).val < 4294967296
  ∧ (e.b_0 r).val < 4294967296 ∧ (e.b_1 r).val < 4294967296

/-! ## Specialized accessors -/

lemma be_a_0_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_0 r).val < 256 := (binary_extension_columns_in_range e r).1
lemma be_a_1_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_1 r).val < 256 := (binary_extension_columns_in_range e r).2.1
lemma be_a_2_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_2 r).val < 256 := (binary_extension_columns_in_range e r).2.2.1
lemma be_a_3_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_3 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.1
lemma be_a_4_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_4 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.1
lemma be_a_5_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_5 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.1
lemma be_a_6_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_6 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.2.1
lemma be_a_7_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_a_7 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.2.2.1
lemma be_b_lt_256 (e : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    (e.free_in_b r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.2.2.2.1

/-! ## op_is_shift linkage -/

open ZiskFv.Trusted in
/-- **BinaryExtension AIR op_is_shift linkage.** The `op_is_shift`
    column is `bits(1)` (per `binary_extension.pil:88`: `col witness
    bits(1) op_is_shift; // 1 if operation is in the shift family;
    0 otherwise`) and the per-byte table lookup at
    `binary_extension.pil:92` binds it to the table entry's
    `op_is_shift` flag — so every row whose `op` is a shift literal
    has `op_is_shift = 1`, and every row whose `op` is a SEXT literal
    has `op_is_shift = 0`.

    Trust class: lookup-soundness on the BinaryExtension table (same
    class as `bin_ext_table_consumer_wf`, trusted-base.md class #6).
    Cited PIL: `binary_extension.pil:88` (column declaration),
    `binary_extension.pil:92` (table-lookup binding). -/
axiom binary_extension_op_is_shift_pin (v : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    ((v.op r = OP_SLL ∨ v.op r = OP_SRL ∨ v.op r = OP_SRA
      ∨ v.op r = OP_SLL_W ∨ v.op r = OP_SRL_W ∨ v.op r = OP_SRA_W)
        → v.op_is_shift r = 1)
  ∧ ((v.op r = OP_SIGNEXTEND_B ∨ v.op r = OP_SIGNEXTEND_H ∨ v.op r = OP_SIGNEXTEND_W)
        → v.op_is_shift r = 0)

end ZiskFv.Airs.BinaryExtension

namespace ZiskFv.Airs.BinaryExtension

variable {C : Type → Type → Type} [Circuit FGL FGL C]

open ZiskFv.Airs.BinaryExtensionTable in
/-- **BinaryExtension row → 8-byte table-entry witness.** For every row
    `r` of a `Valid_BinaryExtension` AIR, the 8 per-byte lookups against
    the `BinaryExtensionTable` (per PIL `binary_extension.pil:92`:
    `lookup_assumes(BINARY_EXTENSION_TABLE_ID, [op, j, free_in_a[j],
    free_in_b, free_in_c[j][0], free_in_c[j][1], op_is_shift])`) are
    witnessed by 8 `BinaryExtensionTableEntry` consumers at multiplicity
    1, one per byte slot j ∈ {0..7}.

    The struct `ByteLookupHypotheses` (in
    `Airs/Binary/BinaryExtensionPackedCorrect.lean`) packages these 8
    table entries together with the row→entry projection equations.

    Trust class: lookup-soundness on the BinaryExtension table (same
    class as `bin_ext_table_consumer_wf`, trusted-base.md class #6).
    Cited PIL: `binary_extension.pil:92` (the 8-byte lookup_assumes
    declaration). -/
axiom binary_extension_row_byte_lookups (v : Valid_BinaryExtension C FGL FGL) (r : ℕ) :
    ByteLookupHypotheses v r

end ZiskFv.Airs.BinaryExtension
