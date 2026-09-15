# Plan - Resolve #169: Arith range-table fidelity

## Summary

Issue #169 supplies the extraction/fidelity layer needed by #151. The goal is to make indexed
Arith range-table lookups live in the Clean AIR model, then expose balance-derived bridge lemmas
for the signed witness sign facts currently carried as external `h_sign_*` hypotheses.

This stream starts from a fresh worktree at `origin/main` and stops before #151's row-local
defect-region rewrite. Existing public theorem binders may remain; #169 provides the facts needed
to discharge them later.

Current digression: proof-tree visualizer layout alignment. The top overview and
bottom drill-down should share global depth/order cues so the comparison shows
collapse/expansion differences, not unrelated layout choices.

## Implementation checklist

- [x] Create branch `issue-169-arith-range-table` at `.worktrees/issue-169-arith-range-table`.
- [x] Initialize `STATUS.md`, `docs/ai/PROJECTS.md`, and this plan.
- [x] Re-inspect `ArithMul`, `ArithDiv`, `RangeTables`, `FullEnsemble`, and trust residual docs on
  the fresh base.
- [x] Finish proof-tree layout alignment digression.
- [ ] Add a Clean static `ArithRangeTable` model matching upstream `arith_range_table.pil` /
  `arith_range_table_helpers.rs`.
- [ ] Add specs/helper lemmas for `FULL`, `POS`, `NEG`, and carry range IDs.
- [ ] Add indexed range-table lookups to `ArithMul.mainWithArithTable`.
- [ ] Mirror indexed range-table lookups into the parallel `ArithDiv` lookup-aware/full spec path.
- [ ] Keep existing generic `rangeTable16` checks intact for compatibility.
- [ ] Extend `FullSpec`/bridge projections with indexed range facts.
- [ ] Add row-level sign lemmas deriving current `h_sign_a`/`h_sign_b` shapes from table facts.
- [ ] Update `FullEnsemble`/balance wiring if extra assumptions or classifications are required.
- [ ] Update trust docs to reflect that the sign-range residual is modeled by #169.
- [ ] Run focused file/module checks during implementation.
- [ ] Run final build, trust gates, semantic gates, diff check, and axiom scan.
- [ ] Commit the semantically complete #169 implementation.

## Public interfaces

- New or extended Clean static table API for indexed Arith range checks.
- New indexed range spec/projection lemmas under the existing Arith bridge style.
- New sign derivation lemmas for signed 64-bit rows and signed W rows, with no new axioms,
  `sorry`, `native_decide`, `trustCompiler`, or `ofReduceBool`.

## Verification plan

- Inner loop: `rtk lake env lean` on touched Lean files.
- Focused targets: `ZiskFv.AirsClean.ArithMul.Bridge`, `ZiskFv.AirsClean.ArithDiv.Bridge`,
  `ZiskFv.AirsClean.FullEnsemble`, and `ZiskFv.Compliance.OpBusProviderMatch`.
- Final gates: `rtk lake build`, `rtk trust/scripts/check-all.sh`,
  `rtk trust/scripts/check-all-semantic.sh`, `rtk git diff --check`.
- Axiom scan: use the existing trust gate or `check_axioms_inline.sh --report-only` on new public
  lemmas; closure must not add project axioms or compiler trust.

## Assumptions

- Base is latest fetched `origin/main` at stream start, observed as `019a2381`.
- #151 predicate rewrites/provider uniqueness are out of scope.
- Prefer source-level Clean static table definitions over new generated extraction artifacts unless
  the implementation proves generation is required by the existing architecture.
- The final code commit should include the implementation and trust docs, but not the AI tracking
  trail if those files are meant to remain uncommitted.
