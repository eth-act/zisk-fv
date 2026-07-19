import ZiskFv.AirsClean.ArithMul.Circuit
import ZiskFv.AirsClean.ArithCompleteConstraints

/-!
# Consumer-facing ArithMul interface

The canonical consumer row is `ArithMulRow`; its chunks, flags, carries,
Arith-table tuple, and operation-bus messages are exposed directly by
`Row.lean` and `Constraints.lean`.

## Q2 constraint correspondence

The audit compares every predicate in the retired-target legacy model
`Airs/Arith/Mul.lean` with the operations currently emitted by the Clean
ArithMul circuits.

| Legacy predicate | Clean supply | Outcome |
|---|---|---|
| `mul_constraint_6_named`–`mul_constraint_8_named` | first three `assertZero`s of `main`; `Spec` clauses 1–3 | exact |
| `mul_constraint_31_named`–`mul_constraint_38_named` | remaining eight `assertZero`s of `main`; `Spec` clauses 4–11 | exact |
| `mul_carry_chain_holds` | `Spec` | exact |
| Arith-table membership | lookup in `mainWithArithTable`; `FullSpec.arithTable` | exact |
| sixteen chunk ranges | lookups in `mainWithChunkRanges`; `FullSpec.chunkRanges` | exact |
| seven carry ranges | lookups in `mainWithUnsignedCarryRanges` / `mainWithSignedCarryRanges`; `FullSpec.carryRanges` | exact |
| eight indexed ranges | lookups in `mainWithArithTable`; `FullSpec.indexedRanges` | exact |
| primary/secondary operation-bus rows | `primaryOpBusMessageExpr` / `secondaryOpBusMessageExpr` | exact |
| `main_mul_div_disjoint` | `mainComplete`; `ModeSpec` clause 1 | exact |
| `boolean_m32`, `boolean_na`, `boolean_nb`, `boolean_nr`, `boolean_np`, `boolean_sext` | `mainComplete`; `ModeSpec` clauses 2–7 | exact |
| `mul_constraint_46_named` (`bus_res1`) | `mainComplete`; `C46Spec` | exact |

The completed lookup-aware circuit now supplies every constraint in the legacy
ArithMul consumer predicate surface, so the ArithMul Q2 constraint-correspondence
gate passes. Consumer migration and deletion remain separate reference-count gates.
-/

namespace ZiskFv.AirsClean.ArithMul

/-- A canonical ArithMul trace is a family of Clean rows. -/
abbrev Trace (F : Type) := ℕ → ArithMulRow F

/-- Select a canonical row from an ArithMul trace. -/
@[reducible] def rowAt {F : Type} (trace : Trace F) (row : ℕ) : ArithMulRow F := trace row

end ZiskFv.AirsClean.ArithMul
