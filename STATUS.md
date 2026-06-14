Active plan: docs/ai/plan/PLAN_CI_AENEAS_TRACKED_EXTRACTION.md.

Current focus: replacement for closed PR #92 is implemented and staged:
`trust/aeneas/ProductionM2.lean` is tracked, `scripts/aeneas-production-extract.sh`
can update/check it, and workflow `proofs` has a separate
`Aeneas extraction diff` job.

Blocking: none. PR #92 is closed.

Verification passed: shell syntax, workflow YAML parse, `nix flake check
--no-build`, `nix run .#aeneas-production-extract-check-tracked`,
`trust/scripts/check-all.sh`, and default `nix run .#aeneas-production-extract`.

Next step: commit and open the replacement PR.
