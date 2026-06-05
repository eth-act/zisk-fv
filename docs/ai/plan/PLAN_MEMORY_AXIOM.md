# Retire `row_models_sail_state_load`

## Goal

Remove the source axiom `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load` and replace it with explicit trace-indexed memory agreement between selected Mem AIR provider rows and the Sail `state.mem` used by load equivalence proofs.

## Checklist

- [x] Create project bookkeeping.
- [x] Add Mem trace/agreement vocabulary.
- [x] Add byte-address row matching for Mem provider rows.
- [x] Refactor `MemModel` load correctness to consume agreement.
- [x] Thread agreement through Clean load witnesses and wrappers.
- [x] Build and fix Lean fallout.
- [x] Regenerate trust ledgers.
- [x] Run trust checks and final suite.

## Current Notes

The old axiom is retired from the live source and generated trust closure. The replacement makes agreement explicit at the selected load event and active load discharge now uses the byte-address relation `ptr = addr * 8`; stale `mem_legacy_addr` binders remain on some wrapper/envelope surfaces as cleanup, but they are no longer the source of load memory facts.
