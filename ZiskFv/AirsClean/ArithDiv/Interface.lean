import ZiskFv.AirsClean.ArithDiv.Circuit

/-!
# Consumer-facing ArithDiv interface

The canonical consumer row is `ArithDivRow`; its chunks, flags, auxiliaries,
Arith-table tuple, and operation-bus messages are exposed directly by
`Row.lean` and `Constraints.lean`.

## Q2 constraint correspondence

The audit compares every predicate in `Airs/Arith/Div.lean` with the Clean
ArithDiv `Constraints`/`Spec` supply.

| Legacy predicate | Clean supply | Outcome |
|---|---|---|
| `fab_eq_div`, `na_fb_eq_div`, `nb_fa_eq_div` | first three `assertZero`s of `main`; `Spec` clauses 1–3 | exact |
| `carry_eq_0_div`–`carry_eq_7_div` | remaining eight `assertZero`s of `main`; `Spec` clauses 4–11 | exact |
| `div_carry_chain_holds` | `Spec` | exact |
| Arith-table membership and indexed ranges | lookups in `mainWithArithTable`; `FullSpec` projections | exact |
| chunk and carry ranges | dedicated lookup-aware variants; `FullSpec` projections | exact |
| primary/secondary operation-bus rows | `primaryOpBusMessageExpr` / `secondaryOpBusMessageExpr` | exact |
| `main_mul_div_disjoint`; all mode booleans | no corresponding Clean `assertZero` | **missing** |
| W-mode high-lane-zero constraints | no corresponding Clean `assertZero` | **missing** |
| `div_by_zero_forces_*` and `div_overflow_forces_*` boundary constraints | no corresponding Clean `assertZero` | **missing** |
| inverse-sum zero-divisor constraint using legacy `inv_sum_all_bs` | canonical row has no witness column and no corresponding operation | **missing** |
| zero/overflow scope and disjointness constraints | no corresponding Clean `assertZero` | **missing** |
| `bus_res1_eq_div` (constraint 46) | bus field is projected, but its defining equality is not emitted | **missing** |

The Q2 deletion gate therefore does **not** pass for ArithDiv.  The missing
boundary constraints are also exactly where the declared DIV/REM defect
boundary is maintained; migrating them without a faithful Clean supply could
alter the theorem claim.  The legacy Div model and defect-gate consumers must
remain unchanged until these operations (including the inverse witness) are
modeled and proved in Clean.
-/

namespace ZiskFv.AirsClean.ArithDiv

/-- A canonical ArithDiv trace is a family of Clean rows. -/
abbrev Trace (F : Type) := ℕ → ArithDivRow F

/-- Select a canonical row from an ArithDiv trace. -/
@[reducible] def rowAt {F : Type} (trace : Trace F) (row : ℕ) : ArithDivRow F := trace row

end ZiskFv.AirsClean.ArithDiv
