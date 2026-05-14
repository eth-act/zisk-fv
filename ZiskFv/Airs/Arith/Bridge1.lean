import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import Extraction.Arith
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
**Bridge 1: constraint-46 normalization.**

Arith's `bus_res1` (stage-1 column 40) is the range-checked high-32
witness column emitted on the operation bus. PIL constraint 46
(`zisk/state-machines/arith/pil/arith.pil:263`, extracted at
`Extraction/Arith.lean:165-167`) pins its value via

```
bus_res1 = sext * 0xFFFF_FFFF
         + (1 - m32) * (  (1 - main_mul - main_div) * (d[2] + d[3]*65536)
                        + main_mul                   * (c[2] + c[3]*65536)
                        + main_div                   * (a[2] + a[3]*65536) )
```

For the three unsigned modes:

* **MUL-unsigned** (`sext = 0, m32 = 0, main_mul = 1, main_div = 0`):
  `bus_res1 = c[2] + c[3] * 65536` — the high 16 + 16 bits of the
  low 64-bit lane packed from 16-bit chunks.

* **DIV-primary** (`sext = 0, m32 = 0, main_mul = 0, main_div = 1`):
  `bus_res1 = a[2] + a[3] * 65536` — the high half of the quotient
  (Arith packs quotient into `a[]` on DIV rows).

* **REM-secondary** (`sext = 0, m32 = 0, main_mul = 0, main_div = 0`,
  so `secondary = 1`): `bus_res1 = d[2] + d[3] * 65536` — the high
  half of the remainder.

These specializations, combined with the carry-chain identity in
`Airs/Arith/CarryChain.lean` and the packed-correct theorems in
`Airs/Arith/{Mul,Div}.lean`, let us rewrite `arith_c_packed` from
`Spec/Mul.lean` (and the DIV/REM analogues) as the named-chunk packing
`c_chunks_packed`, bridging the "bus-projection" form to the
"polynomial-identity" form.
-/

namespace ZiskFv.Airs.ArithBridge1

open Goldilocks
open Arith.extraction

variable {C : Type → Type → Type} {F ExtF : Type}
  [Field F] [Field ExtF] [Circuit F ExtF C]

/-- **Bridge 1 for MUL-unsigned.** Under MUL-mode witnesses, constraint
    46 collapses `bus_res1` to the high-chunk pack `c[2] + c[3] * 65536`. -/
lemma mul_bus_res1_eq_c_hi
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C F ExtF) (row : ℕ)
    (h_c46 : constraint_46_every_row v.circuit row)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_main_mul : v.main_mul row = 1) (h_main_div : v.main_div row = 0) :
    v.bus_res1 row = v.c_2 row + v.c_3 row * 65536 := by
  -- Unfold constraint 46 and rewrite raw extraction columns to named columns.
  simp only [constraint_46_every_row,
             ← v.bus_res1_def, ← v.sext_def, ← v.m32_def,
             ← v.main_mul_def, ← v.main_div_def,
             ← v.c_2_def, ← v.c_3_def,
             ← v.a_2_def, ← v.a_3_def,
             ← v.d_2_def, ← v.d_3_def] at h_c46
  -- Substitute the MUL-mode witnesses.
  simp only [h_sext, h_m32, h_main_mul, h_main_div,
             zero_mul, one_mul,
             sub_zero, add_zero, zero_add, sub_self] at h_c46
  -- Close via linear_combination over the residual equation.
  linear_combination h_c46

/-- **Bridge 1 for DIV-primary.** Under DIV-primary mode witnesses
    (`main_div = 1`), constraint 46 collapses `bus_res1` to the
    quotient high-chunk pack `a[2] + a[3] * 65536`. -/
lemma div_bus_res1_eq_a_hi
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C F ExtF) (row : ℕ)
    (h_c46 : constraint_46_every_row v.circuit row)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_main_mul : v.main_mul row = 0) (h_main_div : v.main_div row = 1) :
    v.bus_res1 row = v.a_2 row + v.a_3 row * 65536 := by
  simp only [constraint_46_every_row,
             ← v.bus_res1_def, ← v.sext_def, ← v.m32_def,
             ← v.main_mul_def, ← v.main_div_def,
             ← v.c_2_def, ← v.c_3_def,
             ← v.a_2_def, ← v.a_3_def,
             ← v.d_2_def, ← v.d_3_def] at h_c46
  simp only [h_sext, h_m32, h_main_mul, h_main_div,
             zero_mul, one_mul,
             sub_zero, add_zero, zero_add, sub_self] at h_c46
  linear_combination h_c46

/-- **Bridge 1 for MUL-secondary (high-half MUL).** Under
    secondary-mode witnesses (`main_mul = 0`, `main_div = 0`,
    i.e. `secondary = 1`) on an ArithMul row, constraint 46 collapses
    `bus_res1` to the high-half product's high-chunk pack
    `d[2] + d[3] * 65536`. Used by the MULH / MULHU / MULHSU
    discharge wrappers — Family A.

    Same algebraic shape as `rem_bus_res1_eq_d_hi` (the ArithDiv
    analog); they unfold the same constraint 46 against different
    `Valid_<AIR>` views. -/
lemma mulh_bus_res1_eq_d_hi
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C F ExtF) (row : ℕ)
    (h_c46 : constraint_46_every_row v.circuit row)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_main_mul : v.main_mul row = 0) (h_main_div : v.main_div row = 0) :
    v.bus_res1 row = v.d_2 row + v.d_3 row * 65536 := by
  simp only [constraint_46_every_row,
             ← v.bus_res1_def, ← v.sext_def, ← v.m32_def,
             ← v.main_mul_def, ← v.main_div_def,
             ← v.c_2_def, ← v.c_3_def,
             ← v.a_2_def, ← v.a_3_def,
             ← v.d_2_def, ← v.d_3_def] at h_c46
  simp only [h_sext, h_m32, h_main_mul, h_main_div,
             zero_mul, one_mul,
             sub_zero, add_zero, zero_add] at h_c46
  linear_combination h_c46

/-- **Bridge 1 for REM-secondary.** Under REM-secondary mode witnesses
    (`main_mul = 0`, `main_div = 0`, i.e. `secondary = 1`), constraint 46
    collapses `bus_res1` to the remainder high-chunk pack
    `d[2] + d[3] * 65536`. -/
lemma rem_bus_res1_eq_d_hi
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C F ExtF) (row : ℕ)
    (h_c46 : constraint_46_every_row v.circuit row)
    (h_sext : v.sext row = 0) (h_m32 : v.m32 row = 0)
    (h_main_mul : v.main_mul row = 0) (h_main_div : v.main_div row = 0) :
    v.bus_res1 row = v.d_2 row + v.d_3 row * 65536 := by
  simp only [constraint_46_every_row,
             ← v.bus_res1_def, ← v.sext_def, ← v.m32_def,
             ← v.main_mul_def, ← v.main_div_def,
             ← v.c_2_def, ← v.c_3_def,
             ← v.a_2_def, ← v.a_3_def,
             ← v.d_2_def, ← v.d_3_def] at h_c46
  simp only [h_sext, h_m32, h_main_mul, h_main_div,
             zero_mul, one_mul,
             sub_zero, add_zero, zero_add] at h_c46
  linear_combination h_c46

end ZiskFv.Airs.ArithBridge1
