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
- [ ] Prove `OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope` and `OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope` from the accepted full execution trace.

## Current Notes

The active load path no longer carries `LoadTraceContext` inside `LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over the selected load event. The public theorem now takes `OpEnvelope.AcceptedAirMainMemFullTraceAtEnvelope` and `OpEnvelope.SelectedPrefixAtAcceptedAirMainMemTraceAtEnvelope`, both `Unit` for non-load envelopes and, for load envelopes, split into shared accepted AIR/Main/Mem full-trace data plus a selected prefix cursor pinned to the envelope's concrete read row. The shared accepted construction names generated Mem row constraints, chronological raw memory-bus rows, row-level read/write replay soundness, and initial memory agreement; the packed accepted-at-envelope construction, generated Mem burden, packed row construction, recursive `MemoryBusRowsReadWriteSound`, projected `TraceReplaySound`, and selected memory cursor are derived internally. Raw row replay has an explicit equivalence to projected Mem-event replay, and selected row cursors can be built from row splits plus ordinary memory-read tags. The remaining gap is still global: there is no theorem that proves this shared accepted Mem trace and selected prefix cursor from the full execution trace.

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
