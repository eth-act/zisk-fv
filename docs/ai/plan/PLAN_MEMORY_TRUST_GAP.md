# Close Load Memory Trust Gap

## Goal

Remove caller-supplied per-load Sail memory byte facts from load promises and replace them with a trace-indexed context whose agreement theorem is derived from accepted Mem trace data.

## Checklist

- [x] Create project bookkeeping.
- [x] Add accepted Mem trace context and derived agreement theorem.
- [x] Replace `LoadPromises.mem_trace_agreement` with the trace context.
- [x] Update load wrappers and envelope constructors.
- [x] Remove stale `mem_legacy_addr` load address pins or rename them to byte-address pins.
- [x] Build and fix Lean fallout.
- [x] Regenerate trust ledgers.
- [x] Run trust checks and final suite.

## Current Notes

The active load path now carries `LoadTraceContext` through `LoadPromises`, and the stale `mem_legacy_addr` pins have been removed from load wrappers, witnesses, dispatchers, and `OpEnvelope`. `lake build`, trust gates, the explicit global axiom-closure print, and `nix run .#test` all pass. The broader accepted-trace-to-`OpEnvelope` theorem remains the post-PR #60 composition target tracked by issue #61; this plan closes the memory sub-obligation needed by that theorem.
