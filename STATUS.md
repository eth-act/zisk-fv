Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: PR #64 is open; waiting on review/landing.
`LoadPromises.mem_read` is gone and load arms consume one global
memory-timeline boundary.

Completion route: generated/full-ensemble production of Mem sidecar facts is
the explicit generated-artifact producer for this plan. Load arms require
`MemoryTimelineEvidence`; generated artifacts build it through
`FullWitnessGeneratedTimelineEvidence` and the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`).

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; Mem range lookup witness
definitions exist, but the active component does not emit them, and segment
ranges are sidecar-global rather than row inputs. Clean `Table`/`EnsembleWitness`
carry rows/data/spec/interactions, not these sidecar proofs.

Current slice: generated Mem source facts now have source-level sidecar target.
`MemGeneratedConstraintBridge.lean` maps extracted constraints and bit-width
inequalities to raw split constraints/ranges, and now also repackages raw
source facts into a witness-wide `ExtractedSidecarFacts` callback.

Digression: main `AGENTS.md` commit `f8072326` relaxes build/test cadence;
this worktree has no local `AGENTS.md`, so apply that cadence operationally.

Current proof surface: `FullWitnessMemReplayBridge` derives accepted replay
from generated-row/range facts; `FullWitnessGeneratedTimelineEvidence` carries
ProverData witness facts and proves they match the stored sidecars; `pil-extract`
emits the generated artifact/bridge wrappers.

Latest verification:
- `nix run .#test` passes all 8 checks: cargo tests, generated Mem wrapper,
  zisk-core extraction tests, Aeneas harness, full `lake build`, both trust
  gates, and flake repro.
- Standalone `trust/scripts/check-all.sh` and
  `trust/scripts/check-all-semantic.sh` pass.
- Closure print for `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` has
  0 stdout lines; stderr only has TrustGate `String.trim` deprecation warnings.
- `git diff --check` passes.
- `nix/test.nix` now invokes the generated-Mem wrapper through a ShellCheck-clean
  helper; this fixed the final `nix run .#test` wrapper gate.

PR: https://github.com/eth-act/zisk-fv/pull/64

Next step: monitor/review PR #64. Post-landing cleanup of `memory-trust-gap`
still requires approval after the PR lands.
