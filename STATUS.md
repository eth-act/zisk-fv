Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone; load
arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Load arms
now require `FullWitnessGeneratedTimelineEvidence`, which wraps the full-witness
timeline evidence and carries the concrete `witness.data` target
(`FullWitnessMemAirSourceProverDataWitnessFacts`) for the witness-selected Mem
table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; stage-2 `gsum`/`im`,
table-global segment/permutation constants, challenges, ranges, and generated
assertions are outside the component.

Current slice: generated artifact production is reproducible and gated.
`pil-extract mem-generated-artifact` emits a typed Lean wrapper that defines
`WitnessFacts witness = FullWitnessMemAirSourceProverDataWitnessFacts witness`
from three per-table callbacks, then feeds it to the generated timeline builder.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessGeneratedTimelineEvidence` carries ProverData witness facts and
  proves the stored sidecars match the generated sidecar packager.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range
  hints, ProverData keys, generated timeline constructor, and the per-table
  artifact contract.
- `tools/pil-extract mem-generated-artifact` emits
  `buildWitnessFacts` and `buildTimelineEvidence`; trust docs name the gate.

Latest verification:
- Focused generated-artifact wrapper test.
- Full `cargo test --manifest-path tools/pil-extract/Cargo.toml` (71 tests).
- Generated `/tmp` + populated wrappers; `lake env lean` elaborates both.
- New `nix run .#test` step compiles the populated wrapper; command verified.
- `nix flake check --no-build` sees the updated `test` app.
- `git diff --check` clean.
- Latest Lean/trust gate: `lake build ZiskFv.Compliance` and
  `trust/scripts/check-all.sh` at commit `e788d386`.
- Rustfmt check has broad pre-existing churn outside this slice.
- Last full `nix run .#test`: commit `98202ebc`.

Next step: generate/prove `FullWitnessMemAirSourceProverDataWitnessFacts` in
the generated artifact. Broadening the Clean table/component model is only the
fallback if that artifact must be checked inside the generic full ensemble.
Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
