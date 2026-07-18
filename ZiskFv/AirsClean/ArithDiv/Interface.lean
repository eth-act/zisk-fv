import ZiskFv.AirsClean.ArithDiv.Circuit
import ZiskFv.AirsClean.ArithCompleteConstraints

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
| `main_mul_div_disjoint`; all mode booleans | generated mirrors in `mainWithArithTable` | exact operation supply |
| W-mode high-lane-zero constraints | generated constraints 47–48 in `mainWithArithTable` | exact operation supply |
| `div_by_zero_forces_*` and `div_overflow_forces_*` | generated constraints 9–24 in `mainWithArithTable` | exact operation supply |
| inverse-sum zero-divisor constraint | `ArithDivAux.inv_sum_all_bs`; generated constraint 25 | exact operation supply |
| zero/overflow scope and disjointness constraints | generated constraints 26–30 | exact operation supply |
| `bus_res1_eq_div` (constraint 46) | generated constraint 46 in `mainWithArithTable` | exact operation supply |

The operation-level Q2 correspondence now has an exact generated mirror for every
previously missing legacy predicate. The separate migration/deletion gate remains
blocked until these new operations are projected through `FullSpec` and all existing
consumers are mechanically retargeted.
-/

namespace ZiskFv.AirsClean.ArithDiv

/-- A canonical ArithDiv trace is a family of Clean rows. -/
abbrev Trace (F : Type) := ℕ → ArithDivRow F

/-- Select a canonical row from an ArithDiv trace. -/
@[reducible] def rowAt {F : Type} (trace : Trace F) (row : ℕ) : ArithDivRow F := trace row

end ZiskFv.AirsClean.ArithDiv
