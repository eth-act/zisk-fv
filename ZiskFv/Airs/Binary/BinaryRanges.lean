import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Binary.Binary

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

end ZiskFv.Airs.Binary
