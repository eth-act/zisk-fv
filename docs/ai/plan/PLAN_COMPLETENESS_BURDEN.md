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
- [x] Require `LoadPromises.memoryBurden` when projecting load memory agreement.
- [x] Thread load memory burden through clean load wrappers and equivalence theorems.
- [x] Pass the public compliance burden into load dispatchers.
- [x] Rebuild and rerun trust checks for the burden-consuming load proofs.
- [x] Commit the burden-consuming load proof change.
- [x] Remove hidden `mem_trace_context` from `LoadPromises`.
- [x] Rebuild and rerun trust checks for standalone load memory burden.
- [x] Commit standalone load memory burden change.
- [x] Split load-memory replay evidence out of `OpEnvelope.completenessBurden`.
- [x] Add `OpEnvelope.AcceptedMemoryTraceConstruction` and derive `env.memoryBurden` from it.
- [x] Regenerate trust ledgers and run gates for the accepted-memory-trace theorem surface.
- [x] Commit accepted-memory-trace theorem-surface change.
- [x] Split public load-memory evidence into `AcceptedProgramMemoryTrace` plus selected-load coverage.
- [x] Scope public accepted-memory evidence to load envelopes only.

## Current Notes

The global theorem now takes an explicit `OpEnvelope.completenessBurden` premise for row/table/route evidence and a load-scoped `OpEnvelope.acceptedProgramMemoryTraceBurden` for load-memory replay. Load arms consume a standalone `LoadMemoryBurden` proposition derived from one accepted Mem trace for the current Sail state plus selected-event membership in that trace; non-load arms discharge the public memory burden as `True`. The new public theorem surface derives the dispatcher-facing `env.memoryBurden`; the earlier `acceptedMemoryTraceBurden` slice passed `lake build`, trust gates, semantic gates, closure print, targeted scans, and `nix run .#test`.

The shared trace-context and `AcceptedMemoryTraceConstruction` slices have
passed `lake build`, trust regeneration, both trust gate scripts, global
closure print, targeted retired-memory scans, and `nix run .#test`. The
program-level trace plus coverage split has passed `lake build`, trust
regeneration, both trust gate scripts, global closure print, and targeted
retired-memory scans; `nix run .#test` also passed.

No current theorem in this branch constructs `OpEnvelope` from accepted full-trace data. Until that global construction exists, `env.completenessBurden` remains a real public hypothesis rather than a discharged completeness theorem.
