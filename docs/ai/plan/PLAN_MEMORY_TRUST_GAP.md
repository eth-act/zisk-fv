# Close Load Memory Trust Gap

## Goal

Remove caller-supplied per-load Sail memory byte facts from load promises and replace them with a trace-indexed context whose agreement theorem is derived from accepted Mem trace data.

## Checklist

- [x] Create project bookkeeping.
- [x] Add Mem trace vocabulary and a first accepted-trace context.
- [x] Replace `LoadPromises.mem_trace_agreement` with a trace context.
- [x] Update load wrappers and envelope constructors.
- [x] Remove stale `mem_legacy_addr` load address pins from active load paths.
- [x] Replace `AcceptedMemTrace.readAgreement` with replay-derived selected-read agreement.
- [x] Build and fix Lean fallout.
- [x] Regenerate trust ledgers.
- [x] Run trust checks and final suite.
- [x] Decouple `LoadPromises.memoryBurden` from hidden constructor-carried trace context.
- [x] Verify and commit standalone load memory burden surface.
- [x] Expose accepted load-memory trace evidence at the public compliance theorem boundary.
- [x] Remove raw `env.memoryBurden` from `OpEnvelope.completenessBurden`.
- [ ] Add a top-level accepted Mem trace object to the global construction layer.
- [ ] Prove each load `OpEnvelope.memoryBurden` from selected-event membership in that accepted trace.
- [ ] Replace the public `acceptedMemoryTraceBurden` hypothesis with a proof from the global construction theorem.

## Current Notes

The active load path no longer carries `LoadTraceContext` inside `LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over the selected load event, suitable for proof from top-level accepted trace data. The public theorem now takes `OpEnvelope.acceptedMemoryTraceBurden` separately from structural `completenessBurden` and derives the dispatcher-facing `env.memoryBurden` from it. `AcceptedMemTrace` carries whole-trace `TraceReplaySound`; selected-read replay agreement is proved by induction over the prior-event prefix, then combined with state-vs-replay cursor agreement. The remaining gap is still global: there is no accepted-trace-to-`OpEnvelope` theorem that can produce selected-event membership and Sail/replay cursor agreement for each load arm from full-trace data.

The public theorem-surface slice has passed `lake build`, regenerated trust ledgers, both trust check scripts, the global closure print, targeted retired-memory scans, and `nix run .#test`.
