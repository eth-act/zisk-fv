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
- [x] Add a top-level accepted Mem trace object to the global construction layer.
- [x] Prove each load `OpEnvelope.memoryBurden` from selected-event membership in that accepted trace.
- [x] Replace the public `acceptedMemoryTraceContext` hypothesis with a proof from the global construction theorem.
- [x] Replace the public `OpEnvelope.AcceptedMemoryTraceConstruction` premise with a program-level accepted Mem trace plus selected-load coverage.
- [x] Scope the public accepted-memory trace burden to load envelopes only.
- [x] Expose load-scoped `AcceptedFullMemoryTrace` plus selected-load coverage at the public theorem boundary.
- [x] Replace the public full-memory trace `Prop` with structured envelope-at-cursor construction data.
- [ ] Prove load-scoped `OpEnvelope.AcceptedFullMemoryTraceAtEnvelope` from accepted full-trace data rather than taking it as caller evidence.

## Current Notes

The active load path no longer carries `LoadTraceContext` inside `LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over the selected load event. The public theorem now takes `OpEnvelope.AcceptedFullMemoryTraceAtEnvelope`, which is `Unit` for non-load envelopes and, for load envelopes, packages `AcceptedFullMemoryTrace` for the current Sail state plus selected-load coverage. `AcceptedMemTrace` carries whole-trace `TraceReplaySound`; selected-read replay agreement is proved by induction over the prior-event prefix, then combined with state-vs-replay cursor agreement. The remaining gap is still global: there is no accepted full-trace theorem that builds the load-scoped full-memory trace construction.

The public theorem-surface, shared trace-context, and
`AcceptedMemoryTraceConstruction` slices have passed `lake build`, regenerated
trust ledgers, both trust check scripts, the global closure print, targeted
retired-memory scans, and `nix run .#test`. The program-level trace plus
coverage split has passed `lake build`, regenerated trust ledgers, both trust
check scripts, the global closure print, and targeted retired-memory scans;
`nix run .#test` also passed. The full-memory-trace boundary slice has passed
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, regenerated trust
ledgers, both trust check scripts, global closure print, targeted
retired-memory scans, and `nix run .#test`. The structured envelope-at-cursor
construction slice has passed `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, regenerated trust ledgers, both trust check scripts,
global closure print, targeted retired-memory scans, and `nix run .#test`.

The local `rv64im-completeness` branch was checked non-destructively. It adds
raw-instruction completeness and `OpEnvelope`/Aeneas bridge predicates, but it
does not introduce a Mem replay trace, Sail/replay cursor agreement, or
selected Mem event coverage theorem. The remaining memory gap therefore cannot
be closed by simply consuming the PR #60 interface; it needs a new accepted
Mem full-trace construction layer.
