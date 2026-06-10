Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone, and
load arms consume the single global memory-timeline boundary.

Blocking: populate `MemTableGeneratedAirSource.facts` for the witness-selected
Mem table from generated extractor output or concrete Clean/pilout proofs.

Current proof surface:
- `FullWitnessMemReplayBridge` packages the concrete Mem table, generated-row
  bridge, row/segment ranges, fixed-column facts, active-row equality, and
  nonempty evidence.
- `FullWitnessMemoryTimelineEvidence` is the Compliance-facing load boundary;
  it stores accepted replay plus residual timeline facts, and its full-witness
  constructors derive accepted replay from `FullWitnessMemReplayBridge`.
- The public boundary no longer mentions `fullRv64imEnsemble`, keeping Clean
  completeness axioms out of the global theorem closure.
- Outer load surfaces no longer carry the legacy
  `mem.addr r_mem = bus.e1.ptr` pin.
- `tools/pil-extract mem-air-facts` now reports the Mem generated constraint
  groups, range-check hints, witness/fixed columns, and `mem.pil` range/bit
  source lines needed by `MemTableGeneratedAirFacts`.
- `MemTableGeneratedAirSource` is now the typed Lean target for those source
  columns/facts; replay and timeline evidence constructors consume it.

Latest verification:
- Lean LSP diagnostics: `ZiskFv/AirsClean/FullEnsemble/Balance.lean`
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `trust/scripts/check-all.sh`
- `cargo test --manifest-path tools/pil-extract/Cargo.toml`
- `cargo run --manifest-path tools/pil-extract/Cargo.toml --quiet -- \
  mem-air-facts --pilout build/zisk.pilout --air Mem \
  --pil-source zisk/state-machines/mem/pil/mem.pil \
  --output /tmp/mem-air-facts-report.md`
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `lake build ZiskFv.Compliance`
- `trust/scripts/check-all.sh`
- `rg -n "h_mem_legacy_addr|_h_mem_legacy_addr|mem_legacy_addr" ZiskFv/Compliance`
  returns no hits.

Last full `nix run .#test`: commit `98202ebc`.

Next step: make the extractor or a generated Lean module populate
`MemTableGeneratedAirSource.facts`; existing Clean table soundness does not
expose stage-2 generated columns or range metadata.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
