Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: PR #64 has landed on `origin/main`; post-landing cleanup is
deferred while Cody reviews the code.
`LoadPromises.mem_read` is gone and load arms consume the public
`MemoryTimelineEvidence` boundary.

Completion route: generated/full-ensemble production of Mem sidecar facts is
the explicit generated-artifact producer for this plan. Generated artifacts
build `MemoryTimelineEvidence` through `FullWitnessGeneratedTimelineEvidence`
and the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`).

Latest verification before landing:
- `nix run .#test` passed all 8 checks: cargo tests, generated Mem wrapper,
  zisk-core extraction tests, Aeneas harness, full `lake build`, both trust
  gates, and flake repro.
- Standalone `trust/scripts/check-all.sh` and
  `trust/scripts/check-all-semantic.sh` passed.
- Closure print for `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` had
  0 stdout lines; stderr only had TrustGate `String.trim` deprecation warnings.
- `git diff --check` passed.

PR: https://github.com/eth-act/zisk-fv/pull/64
Landed: 2026-06-10 as squash commit `64c7165a`.

Digression: root `AGENTS.md` carries the build/test cadence update: use
targeted checks during inner-loop work, with broader gates after coherent
groups of changes, before commits, and before claiming completion.

Next step: wait for Cody's review before deleting the old `memory-trust-gap`
branch/worktree or removing its superseded plan/history notes.
