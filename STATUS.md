Active plan: docs/ai/plan/PLAN_RV64IM_COMPLETENESS_RESTACK.md

Current focus: Phase 4 verification for `rv64im-completeness-v2`.
The worktree was created from fetched `origin/main` at `6aa01c3e`; generated
inputs were populated with `nix run .#populate`; `lake exe cache get`
completed after the initial expected fresh-worktree path-dependency failure;
`zisk` was fast-forwarded from `03e886f6` to `4148c25e`.

Blocking: none.

Phase 1-2 progress: payload, root imports, Aeneas script extension, no-sorry
gate, and `nix/test.nix` Aeneas wiring are committed as `3d889970` and
`da5be91d`. Focused checks passed; generated trust ledgers stayed
byte-identical with 0 source axioms and 0 global-closure entries.

Phase 3 progress: `README.md`, `trust/README.md`, `CLAUDE.md`, and
`trust/defects.md` now frame `rv64im_completeness` as RV64IM
acceptance/coverage completeness, document Aeneas interface mediation, and
explicitly preserve the demoted Clean completeness non-claims. Phase 3
checkpoint committed as `7914198c` (`Document RV64IM completeness framing`).

Phase 4 progress: `nix develop --command lake build` passed (8674 jobs);
`trust/scripts/check-all.sh` passed 17/17; `trust/scripts/check-all-semantic.sh`
passed 5/5. A narrow V1 production-boundary gate update was needed so the
new raw materialization helper is recognized and required to delegate through
the accepted-raw helper.

Explicit Aeneas RV64IM completeness extraction passed after the JALR
target-mask extractor was updated for main's current Sail-side JALR shape:
69 starts, 202 declarations, and 1759 generated Lean jobs built.

Cargo verification: all four required `zisk/` tests passed (two `riscv`
decoder tests and two `zisk-core --features aeneas_extract` raw-extraction
gate tests).

Aggregate verification: `nix run .#test` passed all 8 stages, including the
wired Aeneas production extraction and V1/V2 trust gates.

Final hygiene: submodule tracked build artifacts were restored; only ignored
build dirs remain in `zisk/`. `git diff --check` and the generated-ledger drift
check passed.

Next step: push `rv64im-completeness-v2` and open the PR.
