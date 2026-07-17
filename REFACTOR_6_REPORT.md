# Refactor 6 run report

## Work-order status

| Item | Status | Result |
|---|---|---|
| 1. Q2 correspondence report | Done | Added the correspondence table and range/op-bus accounting to `ZiskFv/AirsClean/BinaryAdd/Interface.lean`. No constraint divergence was found. |
| 2. Rewire BinaryAdd consumers | Done | ADD/ADDI EquivCore, write-value proofs, wrappers, dispatch, and construction/StepStrong feeds now consume `BinaryAddRow`, `ComponentSpecFacts`, `binary_add_chunks_eq_bv_add_of_component_spec`, and the Clean op-bus projection directly. Sail-space conclusions and `OpEnvelope` constructor arities are unchanged. |
| 3. Delete bridge and expose interface | Done | Deleted `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`; `ZiskFv.lean` now imports `ZiskFv.AirsClean.BinaryAdd.Interface`. |
| 4. Delete `Valid_BinaryAdd` | Done | Deleted the legacy definition, predicates, packed-correctness file, obsolete EquivCore bridge, operation-bus legacy arm/projection, and unused witness/compositional compatibility surfaces. No consumers remain. |
| 5. Final sweep | Done, with mandated check-13 deferral | Full build and every runnable trust gate passed. Check 13 was not run because the supplied tree has no `zisk` submodule, as pre-acknowledged in the work order. |

## Q2 constraint correspondence

The four legacy predicates and four Clean assertions agree exactly after projecting the same ten row columns. The only syntactic difference after elaboration is subtraction (`x - y = 0`) versus addition of a negation (`x + -y = 0`).

| Legacy predicate | Clean assertion in `BinaryAdd.main` |
|---|---|
| `boolean_cout_0` | `assertZero (cout_0 * (1 - cout_0))` |
| `carry_chain_0` | `assertZero ((a_0 + b_0) - (cout_0 * 2^32 + c_chunks_1 * 2^16 + c_chunks_0))` |
| `boolean_cout_1` | `assertZero (cout_1 * (1 - cout_1))` |
| `carry_chain_1` | `assertZero ((a_1 + b_1 + cout_0) - (cout_1 * 2^32 + c_chunks_3 * 2^16 + c_chunks_2))` |

The Clean circuit additionally performs eight static lookups: 32-bit lookups for `a_0`, `a_1`, `b_0`, and `b_1`, and 16-bit lookups for `c_chunks_0` through `c_chunks_3`. On the legacy side these were the separate `a_chunks_in_range`, `b_chunks_in_range`, and `c_chunks_in_range` predicates supplied by range-table soundness rather than included in `core_every_row`.

The Clean `OpBusChannel.push (opBusMessageExpr row)` corresponds to the legacy BinaryAdd operation-bus projection and permutation/balance proof. It likewise was separate from the four legacy algebraic predicates. Therefore the constraint sets do not diverge: Clean makes explicit the same range and operation-bus obligations previously carried in separate layers.

## Consumer sweep

- Before: 16 Lean files and 49 textual occurrences of `Valid_BinaryAdd`.
- After: 0 files and 0 occurrences.
- Remaining consumers: none.
- `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`: deleted.
- Legacy `ZiskFv/Airs/Binary/BinaryAdd.lean`: deleted.
- Legacy `ZiskFv/Airs/Binary/BinaryAddPackedCorrect.lean`: deleted.
- Obsolete `ZiskFv/EquivCore/Bridge/BinaryAdd.lean`: deleted.

## Verification

- Authoritative tarball installation: all 819 regular tarball files were compared byte-for-byte immediately after overlay; 0 mismatches.
- `lake exe cache get`: completed; cache already present.
- `lake build ZiskFv`: passed (9009 jobs).
- `trust/scripts/check-all.sh`, excluding only check 13: checks 1–12 and 14–16 all passed.
- Check 13 (`check-aeneas-production-boundary.py`): precisely deferred because the supplied tree omits the `zisk` submodule.
- `trust/scripts/check-all-semantic.sh`: all 16 semantic checks passed.
- `trust/generated/`: byte-for-byte unchanged (pre/post SHA-256 manifests compare equal).
- `ZiskFv/Audit.lean`: unchanged; SHA-256 before and after is `28d8be7076d710fbc9e5a2a11f82a04b0ded176852ca954cd7c48dcef5376ad6`.
- `root_soundness` and `root_completeness`: statements remain byte-for-byte identical to the installed authoritative tree.
- Zero-sorry gate: passed for every non-generated ZiskFv Lean source.
