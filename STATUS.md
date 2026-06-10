Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure; `LoadPromises.mem_read` is gone and
load arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Load arms
now require `FullWitnessGeneratedTimelineEvidence`, which wraps the full-witness
timeline evidence and carries the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`) for the witness-selected Mem table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; Mem range lookup witness
definitions exist, but the active component does not emit them, and segment
ranges are sidecar-global rather than row inputs.

Current slice: generated Mem source facts now have source-level sidecar target.
`MemGeneratedConstraintBridge.lean` maps extracted constraints and bit-width
inequalities to raw split constraints/ranges, then packages them as
`ExtractedSidecarFacts`.

Digression: main `AGENTS.md` commit `f8072326` relaxes build/test cadence;
this worktree has no local `AGENTS.md`, so apply that cadence operationally.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessGeneratedTimelineEvidence` carries ProverData witness facts and
  proves the stored sidecars match the generated sidecar packager.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `pil-extract` reports the Mem contract and emits generated artifact/bridge
  wrappers through `ExtractedSidecarFacts` to raw/witness/timeline builders.

Latest verification:
- Full `cargo test --manifest-path tools/pil-extract/Cargo.toml` (73 tests).
- Regenerated local `Circuit.lean`, `Mem.lean`, `MemGeneratedArtifact.lean`,
  and `MemGeneratedConstraintBridge.lean` under `build/extraction/Extraction`.
- Exact generated-Mem gate sequence passes: compile `Circuit.lean` to
  `Circuit.olean`, compile `Mem.lean` and `MemGeneratedArtifact.lean` to
  oleans, then compile `MemGeneratedConstraintBridge.lean` with
  `LEAN_PATH=$(pwd)/build/extraction:$(lake env printenv LEAN_PATH)`.
- Post-`be7aed0e` broad checks: `trust/scripts/check-all.sh`,
  `nix flake check --no-build`, and `git diff --check`.
- Last Lean compliance gate: `lake build ZiskFv.Compliance` at `465470dc`;
  last full `nix run .#test`: `98202ebc`.

Next step: prove/populate `ExtractedSidecarFacts` for mutable Mem tables from
generated sidecar data; Clean component broadening remains a fallback.
