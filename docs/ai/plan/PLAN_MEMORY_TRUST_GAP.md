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
- [x] Add FullEnsemble selected Mem read-row replay projections.
- [x] Factor selected-prefix cursor construction into row coverage plus split-indexed state equality.
- [x] Decompose load-scoped selected-prefix coverage into row membership plus prefix-state equality at the accepted trace boundary.
- [x] Connect selected Mem provider read projections to accepted chronological row membership through an explicit embedding obligation.
- [x] Expose selected-row membership and split-indexed prefix-state equality directly in the public compliance theorem signature.
- [x] Factor selected-row membership through an explicit FullEnsemble Mem read-replay row embedding obligation.
- [x] Add an accepted trace/table bridge constructor for the current public Mem evidence.
- [x] Derive selected table projection membership from concrete primary/dual Mem provider-row evidence.
- [x] Expose accepted trace/table/provider/prefix bridge inputs directly at the public compliance theorem boundary.
- [x] Derive the public trace/table bridge from a full-ensemble Mem-table bridge object.
- [x] Narrow selected Mem provider-row coverage to envelope Mem-row table occurrence.
- [x] Factor the remaining full-execution Mem obligations into `OpEnvelope.AcceptedFullExecutionMemoryExtractionAtEnvelope`.
- [x] Replace the top-level split-indexed memory extraction boundary with cursor-shaped `OpEnvelope.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope`.
- [x] Remove the obsolete split-indexed full-execution memory extraction target.
- [x] Check inside `zisk_riscv_compliant_program_bus` that the selected envelope Mem-row occurrence carried by cursor extraction implies selected accepted-row membership.
- [x] Derive cursor extraction from FullEnsemble-aligned Mem-table, selected envelope row, and prefix-state equality facts.
- [x] Prove that any full RV64IM ensemble witness contains a mutable dual-Mem table and add a constructor that selects it for the Mem trace/table bridge.
- [x] Name the witness-level mutable-Mem read-row embedding obligation consumed by the Mem trace/table bridge.
- [x] Add envelope-level constructors that use the witness-selected Mem table to build the cursor-extraction target.
- [x] Derive cursor extraction from accepted trace construction plus witness-selected Mem-table obligations.
- [x] Expose accepted trace construction plus witness-selected Mem-table obligations at the public theorem boundary.
- [x] Verify and commit named load-scoped full-execution memory construction package.
- [x] Verify and commit split public memory boundary with shared full-execution trace plus per-envelope coverage.
- [x] Verify and commit inverse packaging from load-scoped construction to shared trace plus coverage.
- [ ] Prove shared `AcceptedFullExecutionMemoryTrace` and per-envelope coverage from the accepted full execution trace.

## Current Notes

The active load path no longer carries `LoadTraceContext` inside `LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over the selected load event. The public theorem now takes `OpEnvelope.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope`, a named full-execution Mem extraction target whose fields carry shared accepted AIR/Main/Mem full-trace data, a `fullRv64imEnsemble` witness, a concrete Mem table in that witness, selected envelope Mem-row occurrence in that table, and the selected raw-row prefix cursor. The shared accepted construction names generated Mem row constraints, chronological raw memory-bus rows, prefix-indexed read soundness, and initial memory agreement; the lower trace/table object, packed accepted-at-envelope construction, generated Mem burden, packed row construction, recursive `MemoryBusRowsReadWriteSound`, projected `TraceReplaySound`, ordinary selected-row membership, and selected memory cursor are derived internally. Raw row replay has an explicit equivalence to projected Mem-event replay, and selected row cursors can be built from row splits plus ordinary memory-read tags. The remaining gap is still global: there is no theorem that constructs the extraction target from accepted full execution trace data.

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
The latest uncommitted cursor-construction slice adds
`OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_construction`, recovering
the shared accepted AIR/Main/Mem trace object from the load-scoped accepted
trace construction. Focused `lake build ZiskFv.Compliance.OpEnvelope` passed.
This is a small verified reduction: it removes one separately supplied selected
prefix cursor from the planned next constructor, but it does not yet prove the
remaining full-execution embedding or selected Mem-row occurrence obligations.
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

The current uncommitted cleanup replaces the anonymous nested Sigma/PLift
public memory-construction payload with
`OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionWithWitness`. This does
not close the memory trust gap; it makes the remaining full-execution load
obligation readable and theorem-shaped. The first focused build failed on a
universe mismatch after the structure introduction; the boundary was raised to
`Type 2`. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, both trust gates, and `nix run .#test`
passed.
The FullEnsemble selected Mem replay projection slice adds
`memPrimaryReadReplayEntryOfRow`, `memDualReadReplayEntryOfRow`,
`memReadReplayRowsOfTable`, and table-row/matched-entry membership lemmas in
`ZiskFv.AirsClean.FullEnsemble.Balance`. This exposes selected primary and
dual Mem provider rows as replayable read `MemoryBusEntry` rows without
claiming chronological ordering, row-level read/write soundness, or Sail/replay
state agreement. Focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance`,
full `lake build`, trust regeneration, both trust gates, compliance closure
print with zero project axiom names, targeted retired-memory scans, extractor
skip scan, generated zero-entry checks, and `nix run .#test` passed for this
slice.
The selected-prefix factoring slice adds
`SelectedLoadMemoryBusRowPrefixCursor.of_mem_state_for_split`, which builds
the cursor from membership in the accepted chronological row list plus a
split-indexed proof that the current Sail state is the replayed prefix state.
This gives the remaining FullEnsemble/global integration a smaller proof
target: row coverage can come from the selected Mem replay-row projection,
while instruction-state alignment remains a separate prefix theorem. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, compliance closure print
with zero project axiom names, targeted retired-memory scans, extractor skip
scan, generated zero-entry checks, and `nix run .#test` passed for this slice.
The selected-prefix boundary-decomposition slice adds load-scoped row
membership and split-indexed prefix-state predicates at the accepted
AIR/Main/Mem trace boundary, plus an adapter from those two obligations to
`SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope`. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, compliance closure print with zero project
axiom names, targeted retired-memory scans, extractor skip scan, generated
zero-entry checks, and `nix run .#test` passed for this slice.
The public theorem boundary slice exposes the accepted
trace/table/provider/prefix bridge inputs directly at
`zisk_riscv_compliant_program_bus`; focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, compliance closure print with zero project
axiom names, targeted retired-memory scans, extractor skip scan, generated
zero-entry checks, and `nix run .#test` passed for this slice.
The full-ensemble Mem-table boundary slice adds
`AcceptedAirMainMemFullTraceWithFullEnsembleMemTable`, lowers it to the
previous trace/table bridge, and updates `zisk_riscv_compliant_program_bus` to
consume that full-ensemble bridge object instead of an arbitrary table bridge.
Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, compliance closure print
with zero project axiom names, targeted retired-memory scans, extractor skip
scan, generated zero-entry checks, and `nix run .#test` passed for this slice.
The selected Mem row-embedding slice names
`FullEnsemble.MemReadReplayRowsEmbeddedInTrace` and proves primary/dual
selected Mem provider row membership in the accepted chronological row list
from that embedding plus the existing matched-entry projection lemmas. Focused
`lake build ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`, trust
regeneration, both trust gates, compliance closure print with zero project
axiom names, targeted retired-memory scans, extractor skip scan, generated
zero-entry checks, and `nix run .#test` passed for this slice.
The public compliance theorem-boundary slice changes
`zisk_riscv_compliant_program_bus` to consume selected-row membership and
split-indexed prefix-state equality directly, then derives
`SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope` internally. Focused
`lake build ZiskFv.Compliance`, full `lake build`, trust regeneration, both
trust gates, compliance closure print with zero project axiom names, targeted
retired-memory scans, extractor skip scan, generated zero-entry checks, and
`nix run .#test` passed for this slice.
The current extractor slice removes the mixed F/ExtF skip-stub source:
`tools/pil-extract` now emits constraints that mention challenges or exposed
values as single-field `[Circuit F F C]` definitions, preserving the PIL fact
for the active ZisK validator shape without requiring a generic `F -> ExtF`
coercion. After `nix run .#populate`,
`build/extraction/Extraction/Mem.lean` contains definitions for the former
mixed witness/challenge Mem constraints; the remaining skipped Mem constraints
are the distinct positive-row-offset cases. `cargo test --manifest-path
tools/pil-extract/Cargo.toml`, full `lake build`, trust regeneration, both
trust gates, compliance closure print, generated zero-entry checks, and
`nix run .#test` passed for this slice.
The open work is now rebinding these generated single-field constraints, plus
the remaining row-offset facts, into the Clean/global trace construction.
The current row-offset extractor slice removes the remaining generated
constraint holes: signed witness/fixed row offsets now render as `row + k` or
`row - k` with rotation 0. After `nix run .#populate`,
`build/extraction/Extraction/Mem.lean` contains definitions for all
constraints 0-33, including former positive-row-offset constraints 9-12 and
33, and `rg "skipped:|not yet supported" build/extraction/Extraction` returns
no matches. `cargo test --manifest-path tools/pil-extract/Cargo.toml`, full
`lake build`, trust regeneration, both trust gates, compliance closure print,
generated zero-entry checks, and `nix run .#test` passed for this slice. The
open work is now entirely in the main Lean rebinding layer:
mirror the complete generated Mem constraint surface as named Clean/global
facts and use those facts to construct the accepted chronological Mem row
trace plus selected prefix cursors.
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

The current compliance-boundary refinement adds
`OpEnvelope.AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope`: load envelopes
carry the shared `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace` plus a selected
row-prefix cursor, and non-load envelopes carry `Unit`. The top-level
`zisk_riscv_compliant_program_bus` theorem now consumes this predecessor
burden and derives `AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope`
internally by combining the prefix cursor with the envelope's Main-side
memory-read match. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance` passed, as did full `lake build`, trust regeneration, both
trust gates, compliance closure print with zero project names,
retired-memory scans, generated zero-entry count checks, and `nix run .#test`.

The current local-Mem projection slice adds named consequences of
`AirsClean.Mem.Spec`: selector/write boolean projections, `sel_dual => sel`,
`wr => sel`, the `read_same_addr` identity, and the two zero-value facts for
read rows at an address change. These facts are direct projections of the
existing nine local F-typed constraints and are intended as reusable leaves for
the eventual cross-row/global trace construction. Focused `lake build
ZiskFv.AirsClean.Mem.Spec ZiskFv.AirsClean.Mem.Bridge
ZiskFv.AirsClean.Mem.TraceSpec` passed, as did full `lake build`, trust
regeneration, both trust gates, compliance closure print with zero project
names, retired-memory scans, generated zero-entry count checks, and
`nix run .#test`.

The current replay-soundness bridge slice proves
`ZiskCircuit.MemTrace.memoryBusRowsPrefixReadSound_of_readWriteSound`, the
converse direction from recursive raw-row replay soundness to prefix-indexed
read soundness. `AirsClean.Mem.AcceptedFullMemoryBusRowsTrace.ofReadWriteSound`
uses that theorem so the final AIR bridge can construct the global Mem trace
from chronological rows, a sequential row replay proof, and initial
Sail/replay memory agreement. Focused `lake build ZiskFv.ZiskCircuit.MemTrace
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance` passed, as did full `lake build`, trust regeneration, both
trust gates, compliance closure print with zero project names, retired-memory
scans, generated zero-entry count checks, and `nix run .#test`.

The current compliance-boundary split changes
`zisk_riscv_compliant_program_bus` to take the shared
`AirsClean.Mem.AcceptedFullMemoryBusRowsTrace initialState memoryBusRows` and
the load-scoped `env.SelectedLoadMemoryBusRowsPrefixAtEnvelope initialState
memoryBusRows` separately. The theorem derives
`AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` internally with
`acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_globalTraceAndPrefix`,
so the remaining AIR theorem has two precise targets: one global Mem row-trace
proof and one selected prefix cursor per load envelope. Focused `lake build
ZiskFv.Compliance` passed, as did full `lake build`, trust regeneration, both
trust gates, compliance closure print with zero project names, retired-memory
scans, generated zero-entry count checks, and `nix run .#test`.

The current packed-boundary cleanup removes the obsolete
`AcceptedFullMemoryBusRowsTraceAndPrefixAtEnvelope`,
`AcceptedLoadFullMemoryBusRowsGlobalTraceAndPrefixAtCursor`, and
`acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_traceAndPrefix`
surface from `OpEnvelope`. The active memory route is now only the split
interface: a shared global Mem trace plus
`SelectedLoadMemoryBusRowsPrefixAtEnvelope`, lowered by
`acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_globalTraceAndPrefix`.
Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed,
as did full `lake build`, trust regeneration, both trust gates, compliance
closure print with zero project names, retired-memory and removed-boundary
scans, generated zero-entry count checks, and `nix run .#test`.

The current direct-construction-boundary slice changes
`zisk_riscv_compliant_program_bus` to take
`env.AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` directly. The
theorem no longer receives a loose pair of
`AirsClean.Mem.AcceptedFullMemoryBusRowsTrace initialState memoryBusRows` plus
`env.SelectedLoadMemoryBusRowsPrefixAtEnvelope initialState memoryBusRows`
arguments only to repack them immediately; callers now see the exact
load-scoped construction burden consumed by the compliance proof. Focused
`lake build ZiskFv.Compliance` passed, as did full `lake build`, trust
regeneration, both trust gates, compliance closure print with zero project
names, retired-memory scans, generated zero-entry count checks, and
`nix run .#test`. This is still a boundary-tightening slice, not the final AIR
proof: the remaining open item is deriving this construction burden from
accepted AIR/Main/Mem full-trace data.

The current Mem-source-rebinding slice adds source-level names for generated
Mem constraints 0-23. `Airs.Mem.SegmentColumns` records the exposed and
preprocessed segment columns, `Airs.Mem.segment_every_row` mirrors the
generated segment/continuity constraints, and
`Airs.Mem.core_every_row_of_segment_every_row` proves the existing 9-local
Mem bridge surface is a projection of those generated facts.
`AirsClean.Mem.Bridge.constraints_at_of_segment_every_row` connects that
projection to the Clean bridge. Focused `lake build ZiskFv.Airs.Mem
ZiskFv.AirsClean.Mem.Bridge ZiskFv.AirsClean.Mem.TraceSpec`, full
`lake build`, trust regeneration, both trust gates, compliance closure print,
generated zero-entry checks, retired-memory scans, and `nix run .#test`
passed. This still leaves generated permutation constraints 24-33 and the
chronological replay proof to bind before
`AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` can be derived from
accepted AIR/Main/Mem full-trace data.

The current permutation-rebinding slice adds source-level names for generated
Mem constraints 24-33. `Airs.Mem.PermutationColumns` records the `std_sum`
challenges, `__L1__`, and six exposed direct accumulator values,
`Airs.Mem.permutation_every_row` mirrors the generated accumulator formulas,
and `Airs.Mem.generated_every_row` bundles the segment and permutation
surfaces. `Airs.Mem.core_every_row_of_generated_every_row` and
`AirsClean.Mem.Bridge.constraints_at_of_generated_every_row` prove the current
local Mem bridge remains a projection of the complete generated row surface.
Focused/full builds, trust regeneration, both trust gates, compliance closure
print, generated zero-entry checks, retired-memory scans, and `nix run .#test`
passed. The remaining open proof is semantic: derive chronological rows,
replay soundness, selected read-row coverage, and selected Sail cursor
agreement from accepted AIR/Main/Mem full-trace data.

The current generated-construction-target slice adds
`AirsClean.Mem.GeneratedMemFullTraceConstruction`, rooted in
`GeneratedMemRows`, so the future accepted AIR/Main/Mem bridge has a concrete
target containing the generated Mem row constraints, chronological raw rows,
sequential read/write replay soundness, and initial Sail/replay agreement.
`GeneratedMemFullTraceConstruction.toAcceptedFullMemoryBusRowsTrace` lowers
that object to the existing global replay trace, and
`core_every_row_of_generated_full_trace` projects the local Mem bridge facts
from the generated row surface. `OpEnvelope` now has
`acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedTraceAndPrefix`,
which combines this generated trace object with the selected load prefix cursor
to supply the current compliance theorem's memory construction burden.
Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, compliance closure print, generated zero-entry
checks, retired-memory scans, and `nix run .#test` passed. The remaining open
proof is still semantic: derive the generated construction's replay fields and
the selected prefix cursor from accepted AIR/Main/Mem full-trace data.

The current public-generated-boundary slice changes
`zisk_riscv_compliant_program_bus` to take
`env.GeneratedMemFullTraceConstructionAtEnvelope` directly. Load envelopes now
expose generated Mem full-trace construction plus the selected prefix cursor
at the theorem boundary; the theorem lowers that burden to the previous packed
`AcceptedFullMemoryBusRowsTraceConstructionAtEnvelope` internally before
deriving replay facts. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance` passed, as did full `lake build`, trust regeneration, both
trust gates, compliance closure print, generated zero-entry checks,
retired-memory scans, generated skip scan, and `nix run .#test`. The remaining
open proof is unchanged: derive the generated construction's replay fields and
the selected prefix cursor from accepted AIR/Main/Mem full-trace data.

The current remaining-target audit checked the in-tree FullEnsemble balance
surface as the closest accepted AIR/Main/Mem source. That layer can extract
selected Main memory interactions, balanced provider interactions, and
selected provider rows, but it does not define a chronological Mem row list or
connect replay of such a list to the Sail state at an instruction cursor.
Therefore `OpEnvelope.GeneratedMemFullTraceConstructionAtEnvelope` cannot be
proved from existing accepted data alone; the next real implementation step is
to introduce an accepted full-trace interface carrying chronological Mem rows,
prefix read/write replay soundness, initial Sail/replay agreement, and
selected prefix cursor coverage, then prove those fields from the generated
Mem constraints and full-trace execution model.

The current accepted-interface slice introduces
`AirsClean.Mem.AcceptedAirMainMemFullTraceConstruction`, parameterized by the
concrete `Valid_Main` trace, and
`OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope`. The public
compliance theorem now consumes that accepted AIR/Main/Mem full-trace burden
and derives `GeneratedMemFullTraceConstructionAtEnvelope`, the packed row
construction, and replay evidence internally. Focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance` passed, as did full `lake build`, trust regeneration, both
trust gates, compliance closure print, generated zero-entry checks,
retired-memory scans, extractor skip scan, and `nix run .#test`. The remaining
open proof is now precisely deriving this accepted interface from the full
execution trace.

The current split-boundary slice introduces
`AirsClean.Mem.AcceptedAirMainMemFullTrace` as the shared program-level trace
object and separates selected load cursor coverage into
`OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope`. The public
compliance theorem consumes those two pieces and derives the previous packed
`OpEnvelope.AcceptedAirMainMemFullTraceConstructionAtEnvelope`,
`GeneratedMemFullTraceConstructionAtEnvelope`, and replay evidence internally.
Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed, as did full
`lake build`, trust regeneration, both trust gates, compliance closure print,
generated zero-entry checks, retired-memory scans, extractor skip scan, and
`nix run .#test`. The remaining open proof is deriving the shared trace object
and selected-prefix coverage from FullEnsemble/full execution data.

The selected-row evidence factoring slice adds
`OpEnvelope.SelectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope` and
`OpEnvelope.AcceptedAirMainMemTraceEvidenceAtEnvelope`. The public compliance
theorem now takes that evidence object and derives ordinary selected-row
membership from a FullEnsemble Mem read-replay row embedding before building
the selected prefix cursor. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
global compliance closure print, targeted retired-memory scans, extractor skip
scan, generated zero-entry checks, and `nix run .#test` passed for this slice.
The remaining open proof is deriving that evidence object from accepted
FullEnsemble/full execution data.

The current trace/table bridge slice adds
`AcceptedAirMainMemFullTraceWithMemTable`,
`OpEnvelope.AcceptedAirMainMemFullTraceWithMemTableAtEnvelope`,
`OpEnvelope.SelectedMemReadReplayRowInTraceTableAtEnvelope`, and
`OpEnvelope.acceptedAirMainMemTraceEvidenceAtEnvelope_of_traceTable`. This is
the next upstream shape for accepted full execution integration: a shared
accepted AIR/Main/Mem trace, a concrete FullEnsemble Mem table whose projected
read-replay rows embed in that trace, selected load membership in that table
projection, and split-indexed Sail prefix-state equality construct the current
public `AcceptedAirMainMemTraceEvidenceAtEnvelope`. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed for this slice. The
remaining open proof is unchanged but sharper: derive the shared accepted trace
and table embedding once, and derive selected table projection membership plus
prefix-state equality for each load cursor from accepted full execution data.

The provider-row projection slice adds
`OpEnvelope.SelectedMemProviderReadReplayRowInTraceTableAtEnvelope`,
`OpEnvelope.selectedMemReadReplayRowInTraceTableAtEnvelope_of_providerRow`,
and
`OpEnvelope.acceptedAirMainMemTraceEvidenceAtEnvelope_of_traceTableProvider`.
This derives selected table projection membership from a concrete Mem provider
row whose primary or dual read projection matches the load row, using the
existing FullEnsemble table-row projection lemmas. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed for this slice. The
remaining open proof is now to derive the shared accepted trace/table
embedding, concrete provider-row selection, and selected prefix-state equality
from accepted full execution data.

The current narrowing slice adds
`FullEnsemble.mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq`
and a load-scoped `OpEnvelope.SelectedEnvelopeMemRowInFullEnsembleMemTableAtEnvelope`
predicate, aiming to reduce selected provider-row coverage to the fact that
the envelope's selected Clean Mem row appears in the FullEnsemble Mem table
with equal evaluated row input. The adapter theorem
`selectedMemProviderReadReplayRowInFullEnsembleMemTableAtEnvelope_of_envelopeMemRow`
is split by load case to avoid monolithic `OpEnvelope` normalization, and the
public `zisk_riscv_compliant_program_bus` theorem now derives the old provider
replay-row evidence internally from the narrower predicate. Focused
`lake build ZiskFv.AirsClean.FullEnsemble.Balance`,
`lake build ZiskFv.Compliance.OpEnvelope`, and `lake build ZiskFv.Compliance`
passed. Full `lake build`, trust regeneration, both trust gates, closure print
with zero project axiom names, targeted retired-memory scans, generated
zero-entry checks, and `nix run .#test` also passed. After trimming proof-binder
noise, focused `lake build ZiskFv.Compliance.OpEnvelope` and
`lake build ZiskFv.Compliance` passed again. The remaining implementation target
is proving the shared trace/table embedding, selected envelope Mem-row table
occurrence, and selected prefix-state equality from accepted full execution
data.

Post-commit audit of the next bridge checked the in-tree FullEnsemble balance
surface and the Clean `Air.Flat` table/witness definitions. A direct table
uniqueness route would require proving duplicate-free component positions for
the concrete full ensemble, including many component disequalities; even if
proved, that only identifies the Mem table and does not derive chronological
trace embedding or Sail/replay prefix-state equality. `Mem.TraceSpec` already
separates pure replay consequences from the semantic obligations:
`GeneratedMemFullTraceConstruction` and
`AcceptedAirMainMemFullTraceConstruction` still require chronological public
rows, row-level read/write replay soundness, and initial Sail/replay memory
agreement as fields. The next aligned implementation target is therefore an
AIR/full-execution extraction theorem for those fields plus selected prefix
cursor coverage, not another local load projection theorem.

The prefix-read surface slice changes `GeneratedMemFullTraceConstruction` and
`AcceptedAirMainMemFullTraceConstruction` to carry
`MemoryBusRowsPrefixReadSound` instead of recursive
`MemoryBusRowsReadWriteSound`; the recursive replay object is now derived
internally when lowering through `AcceptedFullMemoryBusRowsTrace`. This moves
the remaining semantic obligation into the prefix-indexed form expected from
chronological accepted Mem rows. Focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec`, `lake build ZiskFv.Compliance.OpEnvelope`,
and `lake build ZiskFv.Compliance` passed. Full `lake build`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, closure print for
`ZiskFv.Compliance.zisk_riscv_compliant_program_bus`, retired-memory scans,
generated zero-entry baseline checks, and `nix run .#test` also passed. The
remaining implementation target is still the accepted AIR/full-execution
extraction theorem that proves the new prefix-read field and selected cursor
facts from trace data, rather than taking them as top-level trust.

The extraction-target boundary slice adds
`OpEnvelope.AcceptedFullExecutionMemoryExtractionAtEnvelope`, containing the
full-ensemble Mem trace/table object, selected envelope Mem-row table
occurrence, and split-indexed prefix-state equality, and refactors
`zisk_riscv_compliant_program_bus` to consume that named target before deriving
the existing accepted-memory evidence internally. Focused `lake build
ZiskFv.Compliance.OpEnvelope` and `lake build ZiskFv.Compliance`, full
`lake build`, `trust/scripts/regenerate.sh`, both trust gates, closure print,
retired-memory scans, generated zero-entry checks, and `nix run .#test`
passed. The remaining proof is to construct this target from accepted full
execution trace data.

The cursor-boundary slice adds
`OpEnvelope.SelectedPrefixAtFullEnsembleMemTableAtEnvelope` and
`OpEnvelope.AcceptedFullExecutionMemoryCursorExtractionAtEnvelope`, then
changes `zisk_riscv_compliant_program_bus` to consume that cursor-shaped target
directly. This deliberately avoids lowering a selected cursor to the older
universal split-indexed prefix-state predicate, because duplicate equal
memory-bus rows would make that implication too strong. Focused `lake build
ZiskFv.Compliance.OpEnvelope` and `lake build ZiskFv.Compliance` passed. The
remaining proof is now to construct the cursor extraction target from accepted
full execution trace data: shared trace/table embedding, selected envelope
Mem-row occurrence, selected prefix cursor coverage, and prefix-read soundness.

The selected-row cleanup slice removes the obsolete split-indexed
`OpEnvelope.AcceptedFullExecutionMemoryExtractionAtEnvelope` and its lowering
helper. The public theorem now checks that the cursor extraction target's
selected envelope Mem-row occurrence implies selected accepted-row membership
via the FullEnsemble table projection and accepted trace/table embedding. The
selected prefix cursor is still carried separately; tying that cursor and row
membership together remains part of the unproved cursor-extraction construction
target. Focused `lake build ZiskFv.Compliance`,
focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`,
`trust/scripts/regenerate.sh`, both trust gates, closure print,
retired-memory scans, generated zero-entry checks, and `nix run .#test`
passed.

The FullEnsemble-aligned cursor slice adds
`OpEnvelope.SelectedPrefixStateAtFullEnsembleMemTableAtEnvelope`,
`OpEnvelope.selectedMemReadReplayRowAtAcceptedAirMainMemTraceAtEnvelope_of_traceTable`,
and
`OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_fullEnsemblePrefixState`.
This removes the duplicated accepted-trace package from the next bridge shape:
selected row membership is now derived internally from the selected envelope
Mem-row occurrence plus table embedding, while the upstream full-execution
theorem only needs to supply prefix-state equality for the same FullEnsemble
Mem-table trace. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, both trust gates, targeted retired-name
scans, and `nix run .#test` passed. This slice was committed as `04140c9a`.

The mutable-Mem-table selection slice proves
`ZiskFv.AirsClean.FullEnsemble.exists_mem_table_of_fullRv64im_witness`: every
`fullRv64imEnsemble` witness contains a concrete table whose component is
`Mem.componentWithDualMemBus`. It also adds
`AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness`, which builds
the full-ensemble Mem trace/table bridge from a full witness, an accepted
AIR/Main/Mem trace, and an embedding theorem for the located mutable Mem
table. This removes manual mutable-Mem table selection from the upstream
extraction target, but it deliberately does not prove chronological row
embedding, selected envelope row occurrence, selected prefix cursor coverage,
or prefix-read soundness. Focused `lake build
ZiskFv.AirsClean.FullEnsemble.Balance` and `lake build
ZiskFv.Compliance.OpEnvelope`, full `lake build`, trust regeneration, both
trust gates, closure print, targeted retired-name scan, and `nix run .#test`
passed for this slice.

The embedding-obligation naming slice adds
`ZiskFv.AirsClean.FullEnsemble.MutableMemReadReplayRowsEmbeddedInTrace` and
updates `AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_witness` to
consume that named predicate. This does not discharge the embedding; it gives
the upcoming accepted full-execution extraction theorem a precise witness-level
target: every mutable dual-Mem table in the full-ensemble witness has its
projected read-replay rows embedded in the accepted chronological memory row
trace. Focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance` and
`lake build ZiskFv.Compliance.OpEnvelope` passed. Full `lake build`, both
trust gates, closure print with zero project axiom names, targeted retired-name
scan, and `nix run .#test` also passed.

The witness-selected cursor-constructor slice adds
`OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_witness`
and
`OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_witnessCursor`
and
`OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_witnessPrefixState`.
The future accepted full-execution extraction theorem no longer needs to pass
an arbitrary Mem table bridge: it can call these constructors from an accepted
trace, full-ensemble witness, `MutableMemReadReplayRowsEmbeddedInTrace`, the
selected envelope row occurrence in the witness-selected table, and either the
selected prefix cursor directly or selected prefix-state equality. Focused
`lake build ZiskFv.Compliance.OpEnvelope` passed for this slice. Full
`lake build`, both trust gates, closure print with zero project axiom names,
targeted retired-name scan, and `nix run .#test` also passed for the final
slice.

The accepted-trace-construction cursor slice adds
`OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_construction`,
`OpEnvelope.MutableMemReadReplayRowsEmbeddedAtAcceptedTraceConstruction`,
`OpEnvelope.SelectedEnvelopeMemRowAtAcceptedTraceConstructionWithWitness`, and
`OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_acceptedTraceConstructionWitness`.
The selected prefix cursor is now recovered from
`AcceptedAirMainMemFullTraceConstructionAtEnvelope` instead of being supplied
separately to the witness bridge. The remaining full-execution obligations are
therefore the accepted trace construction itself, witness-level mutable-Mem
read-row embedding, and selected envelope Mem-row occurrence in the
witness-selected table. Focused `lake build ZiskFv.Compliance.OpEnvelope`
passed for this slice. Full `lake build`, both trust gates, closure print with
zero project axiom names, targeted retired-memory scan, and `nix run .#test`
also passed.

The public-boundary construction slice adds
`OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` and
`OpEnvelope.acceptedFullExecutionMemoryCursorExtractionAtEnvelope_of_acceptedTraceConstruction`.
`zisk_riscv_compliant_program_bus` now consumes this load-scoped construction
object instead of the post-built cursor extraction object. Load envelopes expose
the accepted AIR/Main/Mem trace construction, full RV64IM witness,
mutable-Mem read-row embedding, and selected envelope Mem-row occurrence in the
witness-selected table; non-load envelopes remain `ULift Unit`. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed for this
slice. Full `lake build`, both trust gates, closure print with zero project
axiom names, targeted retired-memory scan, and `nix run .#test` also passed.

The split-boundary slice adds shared
`AcceptedFullExecutionMemoryTrace`, per-envelope
`OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageAtEnvelope`, and
`OpEnvelope.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_fullExecutionMemoryTrace`.
The public compliance theorem now consumes the shared trace and selected
coverage separately, then derives the older load-scoped construction object
internally. Focused `lake build ZiskFv.Compliance.OpEnvelope`, focused
`lake build ZiskFv.Compliance`, full `lake build`, both trust check scripts,
global compliance closure print, targeted retired-memory scan, and
`nix run .#test` passed. The remaining open theorem is proving the shared
trace plus coverage from accepted full execution rather than taking them as
public inputs.

The current inverse-packaging slice adds
`OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope` and
`OpEnvelope.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_traceConstruction`.
This proves that, on load envelopes, the older load-scoped construction object
decomposes into the new shared trace plus selected envelope coverage package;
non-load envelopes remain trivial because they do not contain memory trace
data. Focused `lake build ZiskFv.Compliance.OpEnvelope`, focused
`lake build ZiskFv.Compliance`, full `lake build`, both trust check scripts,
global compliance closure print, targeted retired-memory scan, and
`nix run .#test` passed. This is a migration helper, not the final upstream
construction theorem.

Post-commit source inspection did not find a broader accepted full-execution
witness object that already proves the memory trace. `FullEnsemble` exposes
the RV64IM ensemble, table selection, and balanced-channel projections, while
`Main` exposes row-local/ROM/memory-bus Clean component surfaces. The missing
source theorem still has to connect those accepted witness tables to
chronological memory rows, prefix replay/state coverage, and selected envelope
row occurrence; it is not currently available as a global execution object.
