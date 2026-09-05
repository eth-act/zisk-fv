# Maintaining extraction fidelity in CI

The hardening work uses the existing pinned ZisK release. It does not upgrade
ZisK, Sail, Lean, or the other locked inputs. Mutations operate on disposable
source copies and the production checkout remains unchanged.

The `proofs` workflow runs an aggregate status named `required proof checks` on
pull requests, merge groups, main pushes, scheduled runs, and manual runs.
Workflow-level path filters do not hide this status. The input classifier treats
proof code, extraction tools, test tools, trust policy, Nix recipes, and version
pins as proof inputs. Documentation-only changes still run the fast trust gate.

For proof changes, the repository test command builds the complete generated
Lean inventory and the maintained library, runs the polynomial round trips,
checks the production MemAlign ROM builder, checks structural coverage, and runs
both trust gates. The existing Aeneas production check runs in its parallel CI
job and is required by the aggregate status.

The same proof job then runs the mutation suite:

- Ordinary proof changes run the boundary profile covering the repaired table,
  byte-lookup, opcode, arithmetic-result, and virtual-table interfaces.
- Extraction inputs, toolchains, and fidelity tooling changes run all 52 rounds.
- Scheduled and manual runs also run all 52 rounds.

A timeout, failed baseline, missing artifact, wrong diagnostic, surviving
expected kill, or rejected equivalence control fails the suite. Round 27 retains
its documented range-scope disposition; it is not counted as a proved weld.
Read `tools/adversarial-mutations/README.md` for the exact evidence protocol.
The uploaded artifact contains per-round reports and logs, plus a compact
coverage-change report. Historical verdicts are not evidence for the current
checkout.

PR and merge-group code runs on GitHub-hosted runners with read-only repository
permissions and without cache-publishing credentials. Trusted main and scheduled
runs retain the repository's existing runner selection. Mutable proof caches
must stay private to each mutation suite.

After this workflow is merged and has produced the status, repository branch
protection must require **required proof checks**, with code-owner review for
protected extraction and gate files. A workflow file cannot itself enable
branch protection. Do not require a new status before its workflow is present
on the protected branch. Missing, cancelled, failed, and unexpectedly skipped
required jobs are rejected by the aggregate job.

For a future intentional source update, refresh generated inputs with
`nix run .#populate`, inspect the coverage report and any manifest changes,
repair the affected source-to-model proofs, and rerun `nix run .#test` plus the
full mutation suite. Do not refresh trust allowlists or weaken validators to
turn a regression green. No source update is part of this implementation.

These gates check extraction fidelity and the modeled proof surface. They do
not turn polynomial logup equations into exact multiset balance or prove a raw
physical trace satisfies the public model's acceptance predicate. Those claims
require their own Lean constructions and explicit existing protocol assumptions.
