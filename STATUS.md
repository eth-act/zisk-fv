Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure; `LoadPromises.mem_read` is gone and
load arms consume one global memory-timeline boundary.

Design decision: generated/full-ensemble production of Mem sidecar facts is the
remaining boundary. Load arms require `FullWitnessGeneratedTimelineEvidence`,
which wraps the full-witness timeline evidence and carries the concrete
`witness.data` target (`FullWitnessMemAirSourceProverDataWitnessFacts`) for the
witness-selected Mem table.

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
- Full `cargo test --manifest-path tools/pil-extract/Cargo.toml` (73 tests).
- Regenerated local `Circuit.lean`, `Mem.lean`, `MemGeneratedArtifact.lean`,
  and `MemGeneratedConstraintBridge.lean` under `build/extraction/Extraction`.
- Exact generated-Mem gate sequence passes: compile `Circuit.lean` to
  `Circuit.olean`, compile `Mem.lean` and `MemGeneratedArtifact.lean` to
  oleans, then compile `MemGeneratedConstraintBridge.lean` with
  `LEAN_PATH=$(pwd)/build/extraction:$(lake env printenv LEAN_PATH)`.
- Latest bridge regen compiles `MemGeneratedConstraintBridge.lean` with the
  same `LEAN_PATH` after adding raw→extracted adapters.
- Post-`be7aed0e` broad checks: `trust/scripts/check-all.sh`,
  `nix flake check --no-build`, and `git diff --check`.
- Last full `nix run .#test`: `98202ebc`.

Next step: choose the completion route: either treat those ProverData-backed Mem
sidecar facts as the explicit generated artifact boundary and run Phase D gates,
or authorize broadening the Clean table/component model so it represents those
sidecar assertion/range operations generically.
