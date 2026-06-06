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
- [x] Replace direct row-projected `TraceReplaySound` burden with row-level read/write replay soundness.
- [x] Add a named global Mem row-trace spec and derive the lower row construction from it.
- [x] Replace recursive row-level read/write replay evidence with prefix-indexed row obligations.
- [x] Derive selected load cursor read facts from row tags and the global prefix-indexed trace spec.
- [x] Add raw memory-bus row prefix replay helpers for selected cursor construction.
- [x] Prove raw-row selected prefix state agreement from initial trace agreement.
- [x] Derive selected load byte agreement from the global row spec plus selected cursor.
- [x] Replace anonymous global Mem trace placeholder props with named row-level obligations.
- [x] Add a dual-aware Clean MemBus emission surface and dual-row adapters.
- [x] Add local dual-row load correctness from replay agreement.
- [ ] Prove `OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` from accepted AIR/Main/Mem full-trace data.

## Current Notes

The active load path no longer carries `LoadTraceContext` inside `LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over the selected load event. The public theorem now takes `OpEnvelope.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`, which is `Unit` for non-load envelopes and, for load envelopes, packages a global Mem row-trace spec plus a selected read-row cursor pinned to the envelope's concrete read row. The global spec names chronological raw memory-bus rows, prefix-indexed read replay soundness, initial memory agreement, same-address preservation, write update, segment carry, and dual-event obligations; the recursive `MemoryBusRowsReadWriteSound` consumed by lower replay code is derived internally from the prefix-indexed row obligation. Raw row replay now has an explicit equivalence to projected Mem-event replay, and selected row cursors can be built from row splits plus ordinary memory-read tags. The selected prefix read agreement is projected from the global trace spec, while selected Sail cursor agreement is still derived by replaying prior bus events. The remaining gap is still global: there is no accepted AIR/Main/Mem theorem that proves the global Mem row-trace spec, selected read-row coverage, and the selected Sail state cursor from accepted trace data.

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
initial Sail/replay agreement, row-level read/write replay soundness, and the
store/order/segment/dual soundness placeholders before packing
`AcceptedMemoryBusRowsTrace`. `MemTrace.traceReplaySound_of_memoryBusRowsReadWriteSound`
now proves the projected `TraceReplaySound` internally from
`MemoryBusRowsReadWriteSound`. Focused `lake build
ZiskFv.ZiskCircuit.MemTrace ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed. Full `lake build`, trust regeneration, both trust gates, global
closure print with zero project axiom names, targeted retired-memory scans,
the broad plan scan, and `nix run .#test` also passed for this slice.
The current global-spec slice adds `ZiskFv.AirsClean.Mem.TraceSpec` with
`AcceptedFullMemoryBusRowsTrace`, a named full-trace Mem object for
chronological rows, same-address value preservation, write-update soundness,
event ordering, segment carry, dual emission, row-level read/write replay
soundness, and initial memory agreement. `OpEnvelope` load arms now carry this
global spec plus the selected read-row cursor; the prior granular row
construction is derived internally by
`AcceptedFullMemoryBusRowsTrace.toRowsTraceConstruction`. Focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed. Full `lake build`, trust regeneration, both trust gates, global
closure print with zero project axiom names, targeted retired-memory scans,
the broad plan scan, and `nix run .#test` also passed for this slice.

The local `rv64im-completeness` branch was checked non-destructively. It adds
raw-instruction completeness and `OpEnvelope`/Aeneas bridge predicates, but it
does not introduce a Mem replay trace, Sail/replay cursor agreement, or
selected Mem event coverage theorem. The remaining memory gap therefore cannot
be closed by simply consuming the PR #60 interface; it needs a new accepted
Mem full-trace construction layer.

The raw-row replay helper slice proves
`replayMemoryAfterBusRows_eq_replayEvents`, adds `stateAfterMemoryBusRows`,
and updates selected cursor constructors to use the raw-row state alias.
Focused build, full `lake build`, trust regeneration, both trust gates,
compliance closure print with zero project names, targeted retired-memory
scans, the broad plan scan, and `nix run .#test` passed for this slice.

The selected-prefix helper slice changes `SelectedLoadMemoryBusReadRowCursor`
to store raw-row state equality directly, proves
`replayAgreement_after_memoryBusRows`, and proves
`AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor.selectedPrefixStateAgreement`
from the global trace's initial agreement and selected raw-row prefix. Focused
`lake build ZiskFv.ZiskCircuit.MemTrace ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
compliance closure print with zero project names, targeted retired-memory
scans, the broad plan scan, and `nix run .#test` passed for this slice.
The selected-load byte-agreement slice adds
`ZiskCircuit.MemTrace.memoryTraceAgreement_of_replayAgreement` and
`AcceptedLoadFullMemoryBusRowsGlobalTraceAtCursor.selectedMemoryTraceAgreement`,
so the concrete `MemoryTraceAgreement` consumed by local load correctness is
now derived directly from the global prefix read fact and selected prefix
Sail/replay state agreement. Focused `lake build ZiskFv.ZiskCircuit.MemTrace
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, compliance closure print with zero project
names, retired-memory scans, generated zero-entry count checks, and
`nix run .#test` passed for this slice. The remaining implementation target
is not another local load proof; it is extracting or rebinding the skipped
mixed F/ExtF Mem constraints in `build/extraction/Extraction/Mem.lean` into
the clean/global trace layer so
`AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` can be proved from
accepted AIR/Main/Mem full-trace data.
The current row-obligation naming slice replaces the anonymous
`chronologicalRows`, same-address preservation, write-update, event-ordering,
segment-carry, and dual-emission `Prop` fields in
`AirsClean.Mem.TraceSpec.AcceptedFullMemoryBusRowsTrace` with named predicates
over public chronological `MemoryBusEntry` rows:
`MemoryBusRowsChronological`,
`MemoryBusRowsSameAddressValuePreservation`,
`MemoryBusRowsWriteUpdateSound`, `MemoryBusRowsEventOrderingSound`,
`MemoryBusRowsSegmentCarrySound`, and `MemoryBusRowsDualEventsSound`.
The lower `AcceptedMemoryBusRowsTraceConstruction` adapter still exposes the
named propositions at the older construction layer. Focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
compliance closure print with zero project names, retired-memory scans,
generated zero-entry count checks, and `nix run .#test` passed for this slice.
The current dual-emission slice adds `memWithDualMemBusElaborated`,
`circuitWithDualMemBus`, `componentWithDualMemBus`, and a concrete dual-row
payload adapter for the pinned `dual_mem = 1` PIL emission. The existing
primary-only `componentWithMemBus` remains unchanged for current FullEnsemble
compatibility, while the new surface exposes both primary and dual provider
rows for future global trace construction. Focused build, full `lake build`,
trust regeneration, both trust gates, compliance closure print with zero
project names, generated zero-entry count checks, and targeted retired-memory
scan passed for this slice; `nix run .#test` also passed.
The current dual-load theorem slice adds
`ZiskCircuit.MemModel.mem_dual_load_correct_of_provider_row`, consuming the
new dual Mem row predicate plus `MemoryTraceAgreement` and projecting the
same eight byte facts as the primary provider-row theorem. Focused `lake build
ZiskFv.ZiskCircuit.MemModel ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed, as did full `lake build`, trust regeneration, both trust gates,
compliance closure print with zero project names, retired-memory scans,
generated zero-entry count checks, and `nix run .#test`.

The current active-ensemble slice switches `fullRv64imEnsemble` from the
primary-only Mem provider table to `AirsClean.Mem.componentWithDualMemBus`.
`FullEnsemble.Balance` now extracts Mem provider rows as either primary or
dual MemBus emissions and threads that branch through the spec- and
entry-match-carrying bridge lemmas. Focused `lake build
ZiskFv.AirsClean.FullEnsemble ZiskFv.AirsClean.FullEnsemble.Balance` and
`lake build ZiskFv.EquivCore.Bridge.MemCleanFullEnsemble
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed, as did full
`lake build`, trust regeneration, both trust gates, compliance closure print
with zero project names, retired-memory scans, generated zero-entry count
checks, and `nix run .#test`.

The current selected-prefix-constructor slice narrows the load cursor burden.
`OpEnvelope` now has `SelectedLoadMemoryBusRowPrefixCursor`, which records only
the selected row split and Sail prefix-state equality. The constructor
`acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_globalTraceAndPrefix`
combines that prefix cursor with a shared
`AirsClean.Mem.AcceptedFullMemoryBusRowsTrace`, deriving the selected row's
`as = 2` and `multiplicity = -1` facts from each load envelope's existing
Main-side `bMem` match instead of asking callers for raw read tags. Focused
`lake build ZiskFv.Compliance.OpEnvelope`, `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
compliance closure print with zero project names, retired-memory scans,
generated zero-entry count checks, and `nix run .#test` passed.

The current pure-obligation slice reduces the visible global Mem row-trace
burden again. `AirsClean.Mem.TraceSpec` now proves raw-row write-update
soundness directly from `replayMemoryAfterBusRows`, proves event ordering and
segment-prefix facts from `MemoryBusRowsChronological`, and proves active
read/write rows project to replay events. Consequently
`AcceptedFullMemoryBusRowsTrace` no longer asks callers for write-update,
event-ordering, segment-carry, dual-event projection, or unused same-address
value-preservation evidence; its remaining semantic fields are chronological
rows, prefix-indexed read replay soundness, and initial Sail/replay memory
agreement.
Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed, as did full
`lake build`, trust regeneration, both trust gates, compliance closure print
with zero project names, retired-memory scans, generated zero-entry count
checks, and `nix run .#test`.

The current same-address-burden slice removes
`sameAddressValuePreservation` from
`AirsClean.Mem.AcceptedFullMemoryBusRowsTrace`. That predicate was not
consumed by the replay bridge, and deriving the chunk-level
`value_0/value_1` equality from byte replay soundness alone would require
additional 32-bit chunk range facts, so keeping it in the active caller burden
was unnecessary trust surface rather than useful proof input. The remaining
global trace fields are chronological rows, prefix-indexed read replay
soundness, and initial Sail/replay memory agreement. Focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
compliance closure print with zero project names, retired-memory scans,
generated zero-entry count checks, and `nix run .#test` passed.
