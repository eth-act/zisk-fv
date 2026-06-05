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

## Current Notes

The global theorem now takes an explicit `OpEnvelope.completenessBurden` premise. The current burden predicates are audit markers over the existing constructor-carried row specs, table/provider evidence, memory agreement, and route facts; a later proof-strengthening pass should replace the default `completenessBurden_of_env` discharge with an accepted-trace-to-envelope construction.
