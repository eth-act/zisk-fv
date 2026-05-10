import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.Binary.BinaryAdd

/-!
# BinaryAdd AIR — universal column-range theorems

Mirrors `ZiskFv/Airs/Main/Ranges.lean` for the `BinaryAdd` AIR. PIL
declares the per-row column widths (`zisk/state-machines/binary/pil/binary_add.pil:7-10`):

```pil
col witness bits(32) a[RC];        // RC = 2 → a_0, a_1            each < 2^32
col witness bits(32) b[RC];        //               b_0, b_1       each < 2^32
col witness bits(16) c_chunks[RC*2]; //              c_chunks_0..3 each < 2^16
col witness bits(1)  cout[RC];     //               cout_0, cout_1 each < 2
```

Each `bits(N)` annotation compiles in `pil2-compiler` to a row-level
lookup against the standard range-checker bus, and lookup-argument
soundness on that bus IS the trust assumption that propagates the
bound up to Lean. This file packages that consequence as a single
axiom `binary_add_columns_in_range`, mirroring the role
`main_columns_in_range` plays for the Main AIR.

The axiom delivers the universal-over-rows column bounds that the
BinaryAdd discharge bridge
(`ZiskFv/Equivalence/Bridge/BinaryAdd.lean`) consumes in order to
drop the per-opcode `h_a_range` / `h_b_range` / `h_c_range` caller
hypotheses on `equiv_ADD` / `equiv_ADDI`.

Trust class: lookup-argument soundness on the standard range-checker
bus (same scope as `main_columns_in_range`,
`bin_table_consumer_wf`, `bin_ext_table_consumer_wf`,
`mem_align_rom_subdoubleword_load_value_1_zero`).
-/

namespace ZiskFv.Airs.BinaryAdd

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **BinaryAdd range-check soundness.** Given the row-level
    `lookup_assumes(RANGE_BUS_ID, …)` interactions induced by
    BinaryAdd's `bits(N)` column annotations, every row's witness
    cells satisfy their declared bit ranges.

    PIL citations (`zisk/state-machines/binary/pil/binary_add.pil:7-10`):
    * `bits(32) a[RC]`           → `a_0`, `a_1`         < 2³²
    * `bits(32) b[RC]`           → `b_0`, `b_1`         < 2³²
    * `bits(16) c_chunks[RC*2]`  → `c_chunks_0..3`     < 2¹⁶
    * `bits(1)  cout[RC]`        → `cout_0`, `cout_1`  < 2

    Project-trusted at the same scope as `main_columns_in_range`
    (`Airs/Main/Ranges.lean:67`) — lookup-argument soundness on the
    standard range-checker bus, scoped to BinaryAdd's contributions. -/
axiom binary_add_columns_in_range (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.a_0 r).val < 4294967296
  ∧ (b.a_1 r).val < 4294967296
  ∧ (b.b_0 r).val < 4294967296
  ∧ (b.b_1 r).val < 4294967296
  ∧ (b.c_chunks_0 r).val < 65536
  ∧ (b.c_chunks_1 r).val < 65536
  ∧ (b.c_chunks_2 r).val < 65536
  ∧ (b.c_chunks_3 r).val < 65536
  ∧ (b.cout_0 r).val < 2
  ∧ (b.cout_1 r).val < 2

/-! ## Specialized accessors

Per-component projections of `binary_add_columns_in_range`. -/

theorem ba_a_lo_lt_2_32 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.a_0 r).val < 4294967296 :=
  (binary_add_columns_in_range b r).1

theorem ba_a_hi_lt_2_32 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.a_1 r).val < 4294967296 :=
  (binary_add_columns_in_range b r).2.1

theorem ba_b_lo_lt_2_32 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.b_0 r).val < 4294967296 :=
  (binary_add_columns_in_range b r).2.2.1

theorem ba_b_hi_lt_2_32 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.b_1 r).val < 4294967296 :=
  (binary_add_columns_in_range b r).2.2.2.1

theorem ba_c_chunk_0_lt_2_16 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.c_chunks_0 r).val < 65536 :=
  (binary_add_columns_in_range b r).2.2.2.2.1

theorem ba_c_chunk_1_lt_2_16 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.c_chunks_1 r).val < 65536 :=
  (binary_add_columns_in_range b r).2.2.2.2.2.1

theorem ba_c_chunk_2_lt_2_16 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.c_chunks_2 r).val < 65536 :=
  (binary_add_columns_in_range b r).2.2.2.2.2.2.1

theorem ba_c_chunk_3_lt_2_16 (b : Valid_BinaryAdd C FGL FGL) (r : ℕ) :
    (b.c_chunks_3 r).val < 65536 :=
  (binary_add_columns_in_range b r).2.2.2.2.2.2.2.1

end ZiskFv.Airs.BinaryAdd
