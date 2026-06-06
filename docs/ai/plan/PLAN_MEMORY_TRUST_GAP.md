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
- [x] Narrow `AcceptedFullMemoryTraceAtEnvelope` to accepted trace plus selected split plus cursor agreement.
- [x] Add generic accepted execution-memory replay steps that prove cursor agreement by prefix induction.
- [x] Add an `OpEnvelope` constructor from accepted execution-memory trace plus selected cursor data.
- [x] Replace public `AcceptedFullMemoryTraceAtEnvelope` with accepted execution-memory trace evidence.
- [x] Add chronological memory-bus replay construction for read/write bus events.
- [x] Expose an `OpEnvelope` constructor from accepted memory-bus execution trace data.
- [x] Replace public accepted execution-memory trace evidence with chronological memory-bus trace evidence.
- [x] Prove load-scoped `OpEnvelope.AcceptedFullMemoryTraceAtEnvelope` from accepted full-trace data rather than taking it as caller evidence.
- [x] Replace public `AcceptedFullMemoryBusTraceAtEnvelope` evidence with raw chronological memory-bus row evidence.
- [x] Replace public packed raw-row trace evidence with granular row-trace construction evidence.
- [ ] Prove `OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` from accepted AIR/Main/Mem full-trace data.

## Current Notes

The active load path no longer carries `LoadTraceContext` inside `LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over the selected load event. The public theorem now takes `OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`, which is `Unit` for non-load envelopes and, for load envelopes, packages accepted chronological raw memory-bus rows, row-projected `TraceReplaySound`, initial memory agreement, and a selected read-row cursor pinned to the envelope's concrete read row. Those rows are projected internally to chronological memory-bus read/write events by `memoryBusTraceEventsOfRows`, then packed into `AcceptedMemoryBusRowsTrace`; selected-read replay agreement is proved by induction over the prior-event prefix and combined with cursor agreement derived by replaying prior bus events. The remaining gap is still global: there is no accepted AIR/Main/Mem theorem that proves chronological raw memory-bus rows, row-projected replay soundness, selected read-row coverage, and the selected Sail state cursor from accepted trace data.

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
The selected-cursor narrowing slice passed `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, regenerated trust ledgers, both trust check scripts,
global closure print, targeted retired-memory scans, and `nix run .#test`.
The execution-replay layer introduces `AcceptedExecutionMemoryTrace`, proves
prefix cursor agreement from `EventReplayStep`s, and constructs
`OpEnvelope.AcceptedFullMemoryTraceAtEnvelope` from an accepted execution trace
plus structured selected cursor data. It has passed `lake build
ZiskFv.ZiskCircuit.MemTrace` and `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, regenerated trust ledgers, both trust check scripts,
global closure print, targeted retired-memory scans, and `nix run .#test`.
The current implementation slice is proving reusable per-event replay facts for
memory-bus entries: memory reads preserve Sail/replay agreement, and memory
writes update Sail memory in the same eight-byte shape as `replayStoreEvent`.
These facts are intended to instantiate the existing `EventReplayStep` layer
once accepted Mem/Main trace data identifies the selected chronological event.
The slice now also includes a width-parametric store replay theorem:
`eventReplayStep_store_event_replay_state` proves any store `MemEvent` is an
`EventReplayStep` when the Sail post-state uses `replayStoreEvent` on the
pre-state memory, avoiding an eight-byte-only interpretation for actual Mem
AIR store rows.
This per-event replay lemma slice passed `lake build
ZiskFv.ZiskCircuit.MemTrace`, `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
global closure print, retired-memory scans, and `nix run .#test`. Regeneration
left the project axiom baseline and global compliance closure at zero entries.
The public compliance theorem now consumes load-scoped
`OpEnvelope.AcceptedExecutionMemoryTraceAtEnvelope` evidence instead of a
pre-collapsed `AcceptedFullMemoryTraceAtEnvelope`; the theorem derives the old
selected full-memory trace cursor internally. This exposes the actual execution
replay data needed at the theorem boundary while preserving `Unit` for non-load
envelopes. Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed for this slice.
The current slice adds a bus-level chronological replay bridge: read bus events
leave memory unchanged, write bus events update Sail memory in the same
eight-byte shape as replay, and selected load cursor agreement should be
derivable from an accepted memory-bus event list plus initial memory agreement.
The bus-level bridge is implemented by
`ZiskFv.ZiskCircuit.MemTrace.AcceptedMemoryBusExecutionTrace` and
`OpEnvelope.AcceptedMemoryBusExecutionTraceAtEnvelope`; it passed focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, global closure print with
zero project axiom names, retired-memory scans, and `nix run .#test`.
The public compliance theorem now consumes
`OpEnvelope.AcceptedMemoryBusExecutionTraceAtEnvelope` directly and derives the
selected full-memory cursor internally via the bus replay bridge. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, global closure print with
zero project axiom names, retired-memory scans, and `nix run .#test` passed for
this public-boundary slice.
The current public boundary slice strengthens that evidence again:
`AcceptedFullMemoryBusTraceAtEnvelope` carries the accepted chronological
memory-bus trace and a selected cursor whose split contains the envelope's
concrete `MemoryBusTraceEvent.read bus.e1`; the lower
`AcceptedMemoryBusExecutionTraceAtEnvelope` and then
`AcceptedFullMemoryTraceAtEnvelope` are derived internally. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, global closure print with
zero project axiom names, retired-memory scans, and `nix run .#test` passed for
this slice. The remaining open theorem is deriving
`AcceptedFullMemoryBusTraceAtEnvelope` from accepted AIR/Main/Mem full-trace
data.
The latest row-projection slice strengthens the public boundary one more step:
`AcceptedFullMemoryBusRowsTraceAtEnvelope` carries chronological raw
memory-bus rows, `AcceptedMemoryBusRowsTrace` accepts the read/write projection
of those rows, and `acceptedFullMemoryBusTraceAtEnvelope_of_rowsTraceAtEnvelope`
derives the previous event-list boundary internally. Focused `lake build
ZiskFv.ZiskCircuit.MemTrace ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed for this slice. Full `lake build`, trust regeneration, both trust gates,
global closure print with zero project axiom names, targeted retired-memory
scans, the broad plan scan, and `nix run .#test` also passed. The remaining open theorem is
deriving `AcceptedFullMemoryBusRowsTraceAtEnvelope` from accepted AIR/Main/Mem
full-trace data, including row chronology, Mem continuity/read-value
soundness, initial memory agreement, selected read-row coverage, and selected
Sail state cursor equality.
The latest construction-boundary slice exposes the replay-soundness burden one
level earlier: `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` carries
`AcceptedMemoryBusRowsTraceConstruction`, whose fields name initial memory,
initial Sail/replay agreement, row-projected `TraceReplaySound`, and the
store/order/segment/dual soundness placeholders before packing
`AcceptedMemoryBusRowsTrace`. Focused `lake build
ZiskFv.ZiskCircuit.MemTrace ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed. Full `lake build`, trust regeneration, both trust gates, global
closure print with zero project axiom names, targeted retired-memory scans,
the broad plan scan, and `nix run .#test` also passed.

The local `rv64im-completeness` branch was checked non-destructively. It adds
raw-instruction completeness and `OpEnvelope`/Aeneas bridge predicates, but it
does not introduce a Mem replay trace, Sail/replay cursor agreement, or
selected Mem event coverage theorem. The remaining memory gap therefore cannot
be closed by simply consuming the PR #60 interface; it needs a new accepted
Mem full-trace construction layer.
