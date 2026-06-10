Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone; load
arms consume one global memory-timeline boundary.

Blocking: generated/full-ensemble production of Mem sidecar facts. Lean now has
a concrete `witness.data` witness target
(`FullWitnessMemAirSourceProverDataWitnessFacts`), but generated code still
must supply it for the witness-selected mutable Mem table.

Latest audit: structural gap, not a missing lemma. `componentWithDualMemBus`
emits only row constraints plus MemBus provider rows; stage-2 `gsum`/`im`,
table-global segment/permutation constants, challenges, ranges, and generated
assertions are outside the component.

Current slice: generated code now has a direct ProverData witness-facts entry
point. `fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts` packages
ProverData-backed Clean assertion/lookup witnesses into the stored timeline
boundary plus the residual Sail timeline facts.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed columns, active rows, and nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` carries full witness +
  `FullWitnessMemAirSourceRawSidecars`; source/bridge/replay are accessors.
- `tools/pil-extract mem-air-facts` reports generated constraints, range
  hints, sidecar ProverData keys, pilout sources, and the direct constructor.
- `MemTableGeneratedAirSource` remains the table-level path from Clean
  assertion/lookup witnesses.

Latest verification:
- Lean LSP diagnostics on `Balance.lean`: clean after direct constructor edit.
- `lean_verify` on `fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts`:
  no source warnings.
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`.
- Focused mem-air-facts report test and full
  `cargo test --manifest-path tools/pil-extract/Cargo.toml` (69 tests).
- Regenerated `/tmp/mem-air-facts-report.md`; it names the direct constructor.
- `git diff --check` clean.
- Latest broader gate: `lake build ZiskFv.Compliance` and
  `trust/scripts/check-all.sh` at commit `3a30639f`.
- Rustfmt check has broad pre-existing churn outside this slice.
- Last full `nix run .#test`: commit `98202ebc`.

Next step needs a design choice: supply
`FullWitnessMemAirSourceProverDataWitnessFacts` as the generated artifact, or
broaden the Clean table/component model so the full ensemble constrains those
sidecar operations.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
