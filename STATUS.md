Active plan: docs/ai/plan/PLAN_MEM_READ_DISCHARGE.md

Current focus: Phase B/C bridge closure. `LoadPromises.mem_read` is gone, and
load arms consume the single global memory-timeline boundary.

Blocking: derive or expose `MemTableGeneratedAirFacts` for the witness-selected
Mem table from concrete extraction/Clean witness data.

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

Latest verification:
- `lake build ZiskFv.AirsClean.FullEnsemble.Balance`
- `lake build ZiskFv.Compliance`
- `trust/scripts/check-all.sh`
- `rg -n "h_mem_legacy_addr|_h_mem_legacy_addr|mem_legacy_addr" ZiskFv/Compliance`
  returns no hits.

Last full `nix run .#test`: commit `98202ebc`.

Next step: connect `MemTableGeneratedAirFacts` to concrete extractor/Clean
witness data; existing Lean has selected-load MemClean row bridges but no
whole-table AIR-facts source from `EnsembleWitness` yet.

Context: Phase A is committed at `0c222595`; old memory-trust-gap is salvage only.
