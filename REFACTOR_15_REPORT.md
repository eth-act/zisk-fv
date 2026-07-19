# Refactor 15 report

## Item 1 — constructibility precheck (completed before proof-code changes)

The shared physical provider is instantiated in the compliance construction layer by six balance-selected rows: `mulwArow`, `mulhuArow`, `divuArow`, `divuwArow`, `remuArow`, and `remuwArow`. The ordinary MUL-family path uses the same physical Arith provider through the accepted ensemble; there is no additional literal `mulArow` constructor. A repository-wide constructor search found one non-live generic completeness fixture, `arithMulRowOf`, and no Arith spin witness. All six named `*Arow` definitions are `Classical.choose` projections of a row already present in the live provider table, rather than independently synthesized literals. Thus the load-bearing repair is to put the missing physical column in `ArithMulRow` and validate it in the live component; selected rows then carry the committed value rather than construction code fabricating one.

### Completed-constraint precheck

Legend: **S** = already satisfied from existing table flags/chunks or existing C46 supply; **V** = needs the real `inv_sum_all_bs` witness value; **N/A** = gated to zero for that mode. No row was found genuinely unsatisfiable.

| Concrete/live row family | bool/disjoint 0–5 | boundary 9–24 | inverse 25 | scope 26–30 | mode 39–45 | C46 | W-mode 47–48 | repair |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| MUL (shared accepted-table rows) | S | N/A | N/A | N/A | S | S | N/A | add committed column; value `0` is valid because `div = 0` |
| `mulwArow` | S | N/A | N/A | N/A | S | S | S (high operand lanes already zero) | committed value `0` |
| `mulhuArow` (covers high-MUL family selection) | S | N/A | N/A | N/A | S | S | N/A | committed value `0` |
| `divuArow` | S | S | **V** | S | S | S | N/A | if divisor chunk sum `s ≠ 0`, use `s⁻¹`; if `div_by_zero = 1`, use `0` |
| `remuArow` | S | S | **V** | S | S | S | N/A | same real inverse rule as DIVU |
| `divuwArow` | S | S | **V** | S | S | S | S (32-bit high-lane equations) | same inverse rule, with W-mode zero high divisor lanes |
| `remuwArow` | S | S | **V** | S | S | S | S | same inverse rule, with W-mode zero high divisor lanes |
| `arithMulRowOf` generic completeness fixture (not live) | mode-dependent | mode-dependent | mode-dependent | mode-dependent | mode-dependent | mode-dependent | mode-dependent | its free columns must mechanically gain `inv_sum_all_bs`; `0` remains valid for its multiplication-only assumptions |
| spin/other fixture rows | — | — | — | — | — | — | — | none found by repository-wide `ArithMulRow` constructor search |

Here `s = b_0 + b_1 + b_2 + b_3` in `FGL`. The required equation is `(div - div_by_zero) * (1 - inv_sum_all_bs * s) = 0`. Therefore `s⁻¹` is the real value on active nonzero DIV/REM rows, while `0` is valid precisely on multiplication rows and division-by-zero rows. The prior `vOfDivuRow` constant `0` is invalid for ordinary nonzero DIV/REM and must be replaced by projection of the committed physical column.

The precheck also confirms why validation must occur at the provider: because the named construction rows are selected from the ensemble, no caller premise or post-selection patch can honestly repair them. The completed provider's `constraints_hold` must establish every listed fact.

## Item 2 — shared row and complete circuit: done

Added `ArithMulCarries.inv_sum_all_bs`, with the required stage-1-column/constraint/PIL provenance, and propagated it through the generic unsigned constructor, constant-expression adapters, legacy-row adapter, and component proofs. `sharedMainComplete` now carries the full frozen generated local list: 0–5, 9–30, 39–48, with the existing `mainWithArithTable` prefix supplying carry constraints, C46/ranges/lookups (the duplicate C46 in the full list is the cited generated assertion). `ArithDiv.mainComplete` remains the equivalent family view. No generated file changed.

## Item 3 — live provider swap: done

Added the completed elaborated circuit/component and proved its soundness by projecting the exact `mainWithArithTable` prefix and reusing the established `FullSpec` soundness. Swapped `fullRv64imSoundEnsemble`, `arithMulProviderComponent`, classification, row extraction, Arith balance proofs, concrete fixtures, and all six Construction modules to `componentComplete`. `vOfDivuRow` now projects `arow.carries.inv_sum_all_bs`; it no longer fabricates zero. All selected rows therefore retain the real committed physical witness, and the full appended assertions are checked by the live table's `constraints_hold`, without a caller premise.

## Item 4 — R14 contract/wrapper follow-through: verified remaining blocker

The load-bearing provider remediation is live and green, but the `ArithDivTableWitness` API upgrade and deletion of wrapper binders were not landed. The precise remaining seam is `FullEnsemble/Balance/RowExtraction.lean:arithMul_fullSpec_of_component_spec`: the stable component `Spec` deliberately remains the old six-part `ArithMul.FullSpec`, while the complete local facts exist in the table's `constraints_hold`. The six construction modules currently retain only `h_spec` after selecting the provider row; they do not transport that row's `constraints_hold` proof into an ArithDiv-view `mainComplete` proof. Extending `ArithMul.FullSpec` itself would break its established conjunction ABI across the construction layer; instead a follow-up must add a named complete-local projection from the selected table constraints, transport it through `vOfDivuRow`, and feed that to an upgraded `arithDivTableWitness_of_fullSpec` (or a renamed builder). Deleting wrapper obligations before that projection would still be obligation laundering.

Per wrapper, the requested two bundles therefore remain **2 → 2**: `Div`, `Divu`, `Divw`, `Divuw`, `Rem`, `Remu`, `Remw`, and `Remuw`. The four `StepStrongLoadMext` call sites continue to build the old witness. This item was attempted after the green provider swap and stopped at this exact data-flow boundary rather than weakening the contract.

## Item 5 — final sweep

- Proof-code delta from the authoritative checkpoint (excluding this report/summary): **+259 / −98, net +161 lines**.
- Remaining Div wrapper bundle obligations: eight wrappers at 2 each (16 total); unchanged because item 4's projection seam remains.
- The owner-gated `Equivalence/` tree is byte-unchanged. No new compatibility binder was introduced.
- `trust/generated/` is byte-unchanged.
- `root_soundness`, `root_completeness`, `ZiskFv/Audit.lean`, `Compliance/Defects.lean`, `Equivalence/`, build pins, and lockfiles are byte-unchanged.
- Full `lake build ZiskFv`: passed (9,015 jobs).
- Standard trust checks 1–12 and 14–16: all passed. Check 13 was deferred exactly as authorized because the supplied tree has no `zisk` submodule.
- Semantic trust checks 1–16: all passed (the expected false-consistency probe was rejected).
- Non-generated zero-sorry gate: passed; no prohibited construct was introduced.
