Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: PR #65 is open for review before landing.
`LoadPromises.mem_read` is gone and load arms consume the public
`MemoryTimelineEvidence` boundary.

Completion route: generated/full-ensemble production of Mem sidecar facts is
the explicit generated-artifact producer for this plan. Generated artifacts
build `MemoryTimelineEvidence` through `FullWitnessGeneratedTimelineEvidence`
and the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`).

Latest verification before PR #65:
- `nix run .#test` passed all 8 checks: cargo tests, generated Mem wrapper,
  zisk-core extraction tests, Aeneas harness, full `lake build`, both trust
  gates, and flake repro.
- Standalone `trust/scripts/check-all.sh` and
  `trust/scripts/check-all-semantic.sh` passed.
- Closure print for `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` had
  0 stdout lines; stderr only had TrustGate `String.trim` deprecation warnings.
- `git diff --check` passed.

PR: https://github.com/eth-act/zisk-fv/pull/65

Context:
- PR #64 was accidentally squash-merged, then `main` was reset to reopen review.
- Backup branch preserving the mistaken main tip:
  `backup/main-before-reopen-pr64-20260610-100723`.
- The old `memory-trust-gap` worktree/branch is intentionally preserved while
  Cody reviews this PR.

Next step: review PR #65. Do not delete `memory-trust-gap` during review.
