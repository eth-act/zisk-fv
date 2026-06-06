# Expose Compliance Completeness Burden

## Goal

Make the hidden completeness/witness assumptions visible at the public compliance theorem boundary without claiming a global accepted-trace completeness proof.

## Checklist

- [x] Create project bookkeeping.
- [x] Add `OpEnvelope.completenessBurden`.
- [x] Require the burden at `zisk_riscv_compliant_program_bus`.
- [x] Update theorem call sites and trust/docs references.
- [x] Build and run trust checks.
- [x] Commit the verified change.
- [x] Expose load replay obligations through `LoadPromises.memoryBurden`.
- [x] Route load `OpEnvelope.memoryBurden` arms to the load promise burden.
- [x] Remove the trivial `OpEnvelope.completenessBurden_of_env` discharge.
- [x] Rebuild and rerun trust checks for the strengthened burden surface.
- [x] Commit the strengthened burden-surface change.

## Current Notes

The global theorem now takes an explicit `OpEnvelope.completenessBurden` premise. Load arms now unfold their memory burden to the replay-sound accepted trace, selected-event split, read tag, and Sail/replay cursor agreement carried by `LoadPromises`; the old trivial `completenessBurden_of_env` discharge has been removed. `lake build`, trust regeneration/checks, explicit global closure print, and `nix run .#test` pass; the remaining proof-strengthening pass is still the accepted-trace-to-envelope construction that proves these obligations from top-level trace data instead of constructor-carried witnesses.
