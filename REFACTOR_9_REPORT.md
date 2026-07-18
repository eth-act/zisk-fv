# Refactor 9 report — Binary family

## Summary

The Binary family is now fully on the canonical Clean row spine. The legacy named-record model, legacy packed-correctness path, Clean compatibility bridge, and `EquivCore` Binary bridge have been retired. All consumers use declarations in `ZiskFv.AirsClean.Binary`.

## Work-order status

1. **Consumer map — complete.** The refreshed map found the 3,848-line `EquivCore/Bridge/Binary.lean` plus direct consumers in four groups:
   - shared balance/static-table: `AirsClean/BinaryFamily/Balance.lean`, `AirsClean/FullEnsemble/Balance/*`, `Compliance/SharedBundles.lean`, and concrete row reductions;
   - compare: `Slt`, `Sltu`, `Slti`, `Sltiu`, compare write-value proofs, wrappers, constructions, and equivalence exports;
   - logic: `And`, `Or`, `Xor` and immediate variants, logic write-value proofs, wrappers, constructions, and equivalence exports;
   - arithmetic/input and remaining: `Add`, `Sub`, W variants, input-packing helpers, branch-flag and arithmetic bridges, operation-bus consumers, trace exports, and construction modules.
   The old bridge exported 57 declarations. The externally used declarations and their consumer counts were audited before migration; the largest shared surfaces were `logic_row_mode_pins_of_emit_op_lt_16_of_static_spec` and `byte_chain_discharge_64_of_static_row` (16 consumer files each), `e2_byte_ranges_discharge` (16), `byte_chain_discharge_logic_of_static_row` (11), and `all_byte_matches_wf_at_row` (10).
2. **Shared balance/static-table consumers — complete.** Concrete table projection now directly produces a canonical-row trace (`ℕ → BinaryRow FGL`), and all balance imports target `ConsumerFacts`.
3. **Bridge groups — complete.** Compare, logic, arithmetic/input, and remaining bridge results now live in `AirsClean/Binary/ConsumerTheorems.lean`; retained packed semantics moved to `AirsClean/Binary/PackedCorrect.lean`. `AirsClean/Binary/Trace.lean` defines traces as canonical Clean rows and supplies readable projections.
4. **Bridge retirement — complete.** `AirsClean/Binary/Bridge.lean` became `ConsumerFacts.lean`; `EquivCore/Bridge/Binary.lean` was moved into the Clean family as `ConsumerTheorems.lean`. There are zero old Binary bridge imports or qualified references.
5. **Legacy deletion — complete.** Deleted:
   - `ZiskFv/Airs/Binary/Binary.lean`
   - `ZiskFv/Airs/Binary/BinaryPackedCorrect.lean`
   - `ZiskFv/AirsClean/Binary/Bridge.lean` (replaced by `ConsumerFacts.lean`)
   - `ZiskFv/EquivCore/Bridge/Binary.lean` (moved to the Clean family)
6. **Final sweep — complete.** See gates below.

## Reference counts

- Before: 3,848 bridge lines and 59 direct legacy-path references recorded by the prior audit; the refreshed declaration map covered 57 bridge declarations and all shared consumer groups above.
- After: **0** imports or qualified references to `ZiskFv.Airs.Binary`, `ZiskFv.EquivCore.Bridge.Binary`, or `ZiskFv.AirsClean.Binary.Bridge` (excluding the distinct BinaryExtension bridge name).

## Size delta

Migration commit: **895 lines added, 1,141 deleted, net −246 lines** across 87 files. Git recognized the two retained semantic bodies and the compatibility facts as high-similarity moves rather than rewrites.

## Verification

- Authoritative archive installed non-destructively; 826 archive files verified byte-for-byte immediately after extraction.
- `lake build ZiskFv`: **passed**, 9,014 jobs.
- `trust/scripts/check-all-semantic.sh`: **all 16 checks passed**.
- `trust/scripts/check-all.sh`: checks **1–12 and 14–16 passed**; check 13 was deferred exactly as directed because `zisk/core/src/aeneas_extract.rs` is absent with the missing `zisk` submodule.
- Non-generated zero-sorry gate: **passed** (trust check 5).
- `trust/generated/`: **byte-unchanged**.
- `ZiskFv/Soundness.lean`, `ZiskFv/Completeness.lean`, and `ZiskFv/Audit.lean`: **byte-unchanged**.
- No new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`, or `@[implemented_by]` was introduced; no `OpEnvelope` arity changed.
