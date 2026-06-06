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

## Current Notes

The active load path now carries `LoadTraceContext` through `LoadPromises`, and the stale `mem_legacy_addr` pins have been removed from load wrappers, witnesses, dispatchers, and `OpEnvelope`. `AcceptedMemTrace` now carries whole-trace `TraceReplaySound`; selected-read replay agreement is proved by induction over the prior-event prefix, then combined with state-vs-replay cursor agreement. `lake build`, trust gates, the explicit global closure print, and `nix run .#test` pass. The broader accepted-trace-to-`OpEnvelope` theorem remains the post-PR #60 composition target tracked by issue #61.
