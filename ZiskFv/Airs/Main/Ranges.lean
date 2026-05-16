import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Main.Main

/-!
# Main AIR — universal column-range theorems

PIL declares Main's primary witness columns with explicit `bits(N)`
annotations
(`zisk/state-machines/main/pil/main.pil:94-148`):

```pil
col witness bits(32) a[RC];        // RC = 2 → a_0, a_1   each < 2^32
col witness bits(32) b[RC];        //               b_0, b_1   each < 2^32
col witness bits(32) c[RC];        //               c_0, c_1   each < 2^32
col witness bits(32) pc;           // pc                  < 2^32
col witness bits(8)  op;           // op                  < 2^8
col witness bits(4)  ind_width;    // ind_width           < 2^4
col witness bits(1)  ...           // boolean selectors — handled by per-row constraints
```

Each `bits(N)` annotation compiles in `pil2-compiler` to a row-level
lookup against the standard range-checker bus, and the lookup-argument
soundness IS the trust assumption that propagates the bound up to
Lean. This file packages that consequence as a **single axiom**
`main_columns_in_range`, mirroring the role
`bin_table_consumer_wf` plays for the BinaryTable bus.

The axiom delivers the universal-over-rows column bounds the per-shape
discharge bridges
(`ZiskFv/Equivalence/Bridge/<Shape>.lean`, see of
`docs/fv/plans/op-bus-and-global-compliance.md` and the resolution
plan at `/home/cody/.claude/plans/plan-to-completely-resolve-per-opcode-discharge.md`)
need to drop the per-opcode `h_a_range` / `h_b_range` / `h_c_range`
caller hypotheses.

Trust class: lookup-argument soundness on the standard range-checker
bus (same scope as `bin_table_consumer_wf`,
`bin_ext_table_consumer_wf`, `mem_align_rom_subdoubleword_load_value_1_zero`).
-/

namespace ZiskFv.Airs.Main

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Main range-check soundness.** Given the row-level
    `lookup_assumes(RANGE_BUS_ID, …)` interactions induced by Main's
    `bits(N)` column annotations, every row's witness cells satisfy
    their declared bit ranges. This delivers the universal-over-rows
    bounds the per-shape discharge bridges depend on.

    PIL citations:
    * `bits(32) a[RC]` (`zisk/state-machines/main/pil/main.pil:94`)
    * `bits(32) b[RC]` (`main.pil:95`)
    * `bits(32) c[RC]` (`main.pil:96`)
    * `bits(32) pc` (`main.pil:98`)
    * `bits(8) op` (`main.pil:136`)
    * `bits(4) ind_width` (`main.pil:131`)

    Project-trusted at the same scope as `bin_table_consumer_wf`
    (`Airs/BinaryTable.lean:281`) — lookup-argument soundness on the
    standard range-checker bus, scoped to Main's contributions. -/
axiom main_columns_in_range (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.a_0 r).val < 4294967296
  ∧ (m.a_1 r).val < 4294967296
  ∧ (m.b_0 r).val < 4294967296
  ∧ (m.b_1 r).val < 4294967296
  ∧ (m.c_0 r).val < 4294967296
  ∧ (m.c_1 r).val < 4294967296
  ∧ (m.pc r).val < 4294967296
  ∧ (m.op r).val < 256
  ∧ (m.ind_width r).val < 16

/-! ## Specialized accessors

Per-component projections of `main_columns_in_range`. Provided as
`def`s so callers can reach the exact bound they need without
destructuring the tuple. -/

/-- `m.a_0 r < 2^32`. -/
lemma main_a_lo_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.a_0 r).val < 4294967296 :=
  (main_columns_in_range m r).1

/-- `m.a_1 r < 2^32`. -/
lemma main_a_hi_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.a_1 r).val < 4294967296 :=
  (main_columns_in_range m r).2.1

/-- `m.b_0 r < 2^32`. -/
lemma main_b_lo_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.b_0 r).val < 4294967296 :=
  (main_columns_in_range m r).2.2.1

/-- `m.b_1 r < 2^32`. -/
lemma main_b_hi_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.b_1 r).val < 4294967296 :=
  (main_columns_in_range m r).2.2.2.1

/-- `m.c_0 r < 2^32`. -/
lemma main_c_lo_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.c_0 r).val < 4294967296 :=
  (main_columns_in_range m r).2.2.2.2.1

/-- `m.c_1 r < 2^32`. -/
lemma main_c_hi_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.c_1 r).val < 4294967296 :=
  (main_columns_in_range m r).2.2.2.2.2.1

/-- `m.pc r < 2^32`. -/
lemma main_pc_lt_2_32 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.pc r).val < 4294967296 :=
  (main_columns_in_range m r).2.2.2.2.2.2.1

/-- `m.op r < 2^8`. -/
lemma main_op_lt_2_8 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.op r).val < 256 :=
  (main_columns_in_range m r).2.2.2.2.2.2.2.1

/-- `m.ind_width r < 2^4`. -/
lemma main_ind_width_lt_2_4 (m : Valid_Main C FGL FGL) (r : ℕ) :
    (m.ind_width r).val < 16 :=
  (main_columns_in_range m r).2.2.2.2.2.2.2.2

end ZiskFv.Airs.Main
