# Close Load Memory Trust Gap

## Goal

Close the load-memory soundness gap left by
`row_models_sail_state_load`: selected load bytes must come from a proved
agreement between the Sail memory state and the accepted Mem trace replay, not
from caller-supplied semantic memory facts.

## Current Assessment

The long implementation phase was useful but inefficient. It removed the
visible source axiom, added byte-addressed trace/replay machinery, made the
current theorem boundary more honest, and kept the trust ledger at zero project
axioms. It did not fully close the memory trust gap: the hard memory-state
agreement proof is still represented by strong construction, embedding,
selected-row, and prefix-state hypotheses.

The closeout strategy is to refine, not scrap. Keep the trace/replay/load
infrastructure, stop adding equivalent public wrappers, prove the missing
accepted-execution memory extraction theorem directly, and then prune adapter
clutter.

## Closeout Plan

- Final target: `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` should not
  take memory-specific semantic hypotheses such as selected prefix-state
  equality, replay embeddings, `prefixReadSound`, row chronology/nodup facts, or
  `AcceptedAirMainMemFullTraceConstructionAtEnvelope`. Existing non-memory
  `env.completenessBurden` may remain; closing the broader OpEnvelope
  completeness gap is a separate stream.
- Introduce one canonical raw accepted-execution memory evidence object, or use
  an existing accepted-execution object if it already has the needed fields. It
  may carry concrete program/witness data, the selected mutable Mem table,
  accepted Mem trace tables, initial Sail state, and full-ensemble structural
  links. It must not carry semantic replay facts as assumptions.
- Prove a program-level memory extraction theorem from that raw data:
  construct the chronological memory-bus rows, prove generated-row legality,
  nodup/order facts, all-event mutable-Mem replay embedding, initial agreement,
  and `prefixReadSound` by replay induction over accepted Mem rows.
- Prove per-load envelope coverage from raw accepted execution plus the existing
  envelope burden: selected provider-row occurrence in the concrete Mem table,
  selected accepted-row membership, and selected prefix cursor construction.
- Treat selected prefix-state equality as the critical proof. For a selected
  load, prove that the Sail memory before the load equals replay after all
  earlier accepted Mem events. If the current repo lacks a usable execution
  timeline, add the minimum memory-only timeline theorem connecting Main-row
  order, Mem timestamps, stores, loads, and replay state; do not expose this as
  a public compliance hypothesis.
- Retarget the compliance proof through this canonical extraction path, then
  demote or delete compatibility wrappers whose only purpose is translating
  between equivalent memory-evidence packages.

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
- [x] Verify and commit load-scoped public memory trace theorem boundary.
- [x] Verify and commit source-shaped public memory trace theorem boundary.
- [x] Split cursor-to-source promotion through explicit selected-row occurrence uniqueness.
- [x] Move public memory boundary to cursor-shaped source evidence plus uniqueness.
- [x] Add construction-plus-uniqueness bridge to the cursor-shaped source boundary.
- [x] Add a `rows.Nodup` helper that proves selected-prefix occurrence uniqueness.
- [x] Add `rows.Nodup` to accepted Mem row-trace construction and derive uniqueness from it.
- [x] Move the public compliance theorem memory premise to full-execution trace construction.
- [x] Move the public compliance theorem memory premise to shared full-execution trace plus per-envelope coverage.
- [x] Split the public compliance theorem memory premise into load-scoped shared trace plus indexed coverage.
- [x] Add direct projections from full-execution memory construction to the split public trace and coverage binders.
- [x] Add a shared-trace theorem wrapper for the split public compliance theorem.
- [x] Add an accepted AIR/Main/Mem trace wrapper for the shared-trace theorem.
- [x] Decompose accepted AIR/Main/Mem coverage into selected prefix plus selected witness Mem-row evidence.
- [x] Prove non-boundary same-address value carry facts from generated Mem segment constraints.
- [x] Prove segment-boundary carry-in/carry-out facts from generated Mem segment constraints.
- [x] Prove previous-step and increment/delta facts from generated Mem segment constraints.
- [x] Split generated/accepted Mem trace construction into row-order and replay-agreement obligations.
- [x] Add Nat interpretations and no-wrap bounds for Mem increment and distance chunks.
- [x] Verify and commit no-wrap field/Nat bridges for packed Mem increment and distance expressions.
- [x] Verify and commit Nat-facing generated delta consequences for Mem step/address increments.
- [x] Verify and commit dual-step range/no-wrap facts for Mem chronology.
- [x] Verify and commit previous-step same-address chronology facts for Mem replay.
- [x] Verify and commit effective previous-row primary/dual chronology facts.
- [x] Expose all-event mutable-Mem replay embedding alongside selected-read embedding.
- [x] Thread all-event replay embedding through the selected FullEnsemble Mem-table bridge.
- [x] Add selected accepted-row membership from all-event replay embedding.
- [x] Add a global wrapper that consumes packed full-execution memory construction.
- [x] Add direct accepted AIR/Main/Mem selection to packed memory construction bridge.
- [x] Expose top-level compliance wrappers for source and cursor-source memory evidence.
- [x] Expose a top-level wrapper for unpacked accepted AIR/Main/Mem trace construction plus witness facts.
- [x] Name the shared accepted full-execution Mem row extraction target and add compliance wrappers for it.
- [x] Index selected-load extraction evidence by the named shared Mem row extraction package.
- [x] Split selected-load extraction evidence into cursor-shaped row selection.
- [x] Package row extraction plus cursor selection as a load-scoped source target.
- [x] Move the primary compliance theorem boundary to the row-cursor source target.
- [x] Name balanced active-Main memory provider row coverage from FullEnsemble.
- [x] Split balanced provider coverage into mutable-Mem and non-mutable route branches.
- [x] Add table-parametric FullEnsemble Mem-table construction and provider-row cursor extraction path.
- [x] Move the primary compliance theorem boundary to provider-row cursor-source evidence.
- [x] Add direct-`LD` mutable-provider route bridge to table-parametric provider replay coverage.
- [x] Split direct-`LD` active-Main provider routing into named mutable promotion and four visible non-mutable branch-exclusion obligations.
- [x] Add direct-`LD` row provenance and Main `b` source-fact bridge for branch exclusions.
- [x] Prove direct-`LD` MemAlignReadByte and MemAlignByte branch exclusions from raw width equality.
- [x] Split the direct-`LD` residual route burden after the proved byte-width exclusions.
- [x] Name Main memory-bus multiplicity invariant and use it to eliminate the direct-`LD` Main self-provider residual branch.
- [x] Add table-parametric provider cursor source evidence for the concrete Mem table found by route balance.
- [x] Split direct-`LD` table-parametric provider cursor construction into same-table provider-row replay plus prefix-state replay.
- [x] Compose direct-`LD` active route coverage, replay embeddings, and table-indexed prefix replay into direct source evidence.
- [x] Reduce direct-`LD` same-table prefix-state replay to selected prefix cursor replay plus accepted-row uniqueness.
- [x] Replace the over-broad direct-`LD` generic MemAlign exclusion target with aligned direct-Mem selected-provider coverage or provider uniqueness.
- [x] Construct table-parametric provider cursor source for direct `LD` from aligned route coverage plus selected prefix replay.
- [x] Split `MainMemBusMultiplicitySound` through row-local Main source-multiplicity legality.
- [x] Project unified-Main ROM lookup constraints to program-ROM membership.
- [x] Discharge `MainMemBusSourceMultiplicitySound` from witness constraints plus program-ROM source legality.
- [x] Split `MainProgramRomSourceMultiplicitySound` through row-indexed program ROM source legality.
- [x] Prove selected-row source multiplicity from `MainRowProvenance`.
- [x] Remove direct-`LD` program-ROM source wrappers in favor of positive aligned mutable-route evidence.
- [x] Add provider-shaped source construction from shared trace plus selected provider row and prefix cursor.
- [x] Add a public provider-prefix source boundary that derives uniqueness internally.
- [x] Move the primary compliance theorem to the provider-prefix source boundary.
- [x] Add unpacked accepted AIR/Main/Mem provider-selection boundary.
- [x] Add direct global theorem for shared row extraction plus provider-row cursor selection.
- [x] Add provider-shaped accepted trace construction boundary.
- [x] Expose split accepted AIR/Main/Mem construction at the provider compliance boundary.
- [x] Add direct-`LD` split-construction route bridge for positive aligned mutable-Mem coverage.
- [x] Add split generated-Mem envelope lowering from split accepted AIR/Main/Mem construction.
- [x] Add split shared row-extraction boundary for accepted AIR/Main/Mem trace construction.
- [x] Add split row-cursor source boundaries and compliance wrappers.
- [x] Factor top-level compliance through direct accepted AIR/Main/Mem trace construction.
- [x] Move the named public compliance theorem to the direct accepted AIR/Main/Mem trace construction boundary.
- [x] Factor split accepted AIR/Main/Mem trace construction into shared split trace plus selected prefix cursor.
- [x] Expose provider-selection evidence over split accepted AIR/Main/Mem traces.
- [x] Add extraction-indexed provider selection over split accepted AIR/Main/Mem traces.
- [x] Add load-scoped split-trace provider selection source and compliance wrapper.
- [x] Add split provider construction package and lower it to split-trace source evidence.
- [x] Expose unpacked split-indexed provider construction theorem.
- [x] Bridge shared row extraction plus provider selection into split provider construction.
- [x] Add constructor for shared row-split extraction from split trace plus embeddings.
- [x] Add generated-to-accepted split Mem trace construction constructor.
- [x] Add program-level generated split trace and row-split extraction constructors.
- [x] Expose generated split Mem construction at the top-level compliance theorem boundary.
- [x] Expose generated Mem construction as the direct sufficient top-level replay boundary.
- [x] Add selected replay-row coverage target to avoid relying on all-row read embedding for primary writes.
- [x] Add provider-row replay coverage with primary read evidence.
- [x] Add full-ensemble replay-provider bridge to selected-row membership.
- [x] Add replay-provider cursor extraction target.
- [x] Add replay-provider split-trace source boundary and compliance wrapper.
- [x] Add generated split Mem replay-provider selection boundary.
- [x] Add replay-only split Mem replay-provider boundary without read-only embedding.
- [x] Add replay-only provider plus prefix-state boundary that derives selected prefix cursor.
- [x] Add replay-only cursor-to-state adapter using accepted trace `rowsNodup`.
- [x] Add accepted-split replay-only extraction and compliance boundary.
- [x] Add direct split generated/accepted Mem construction replay projections.
- [x] Add replay-only split construction boundary without read-only Mem embedding.
- [x] Add replay-only state-selection source boundary for shared split extraction.
- [x] Add replay-provider envelope-row adapter for FullEnsemble Mem table coverage.
- [x] Add replay-only table-local envelope-row state-selection boundary.
- [x] Add accepted/generated split wrappers for replay-only envelope-row state selection.
- [x] Add construction-level replay-only envelope-row bridge and public wrapper.
- [x] Add generated-split replay-envelope construction wrapper.
- [x] Add shared generated split trace plus per-envelope replay-envelope selection wrapper.
- [x] Add shared accepted split trace plus per-envelope replay-envelope selection wrapper.
- [x] Add shared accepted split trace plus envelope-row prefix-state replay wrapper.
- [x] Stabilize the merged worktree with focused build verification.
- [x] Add structural replay-row projection evidence deriving all-event Mem table embedding.
- [x] Identify or define the canonical raw accepted-execution memory evidence object.
- [x] Verify raw accepted split-trace surface.
- [x] Commit raw accepted split-trace surface.
- [x] Add raw replay-row projection lowering from raw accepted trace plus table row equality.
- [x] Verify raw replay-row projection lowering.
- [ ] Commit raw replay-row projection lowering.
- [ ] Prove shared accepted Mem split trace construction from raw accepted execution data.
- [ ] Prove all-event mutable-Mem replay embedding from the concrete Mem table, without assuming read-only embedding for writes.
- [ ] Prove selected load provider-row occurrence from full-ensemble route/balance/provider facts.
- [ ] Prove selected prefix-state equality from accepted execution order and memory replay.
- [ ] Retarget the primary compliance theorem to derive memory construction internally from raw accepted execution data.
- [ ] Prune redundant wrapper/adapters and stale comments after the canonical path builds.
- [ ] Regenerate trust ledgers and rerun the full verification suite.

## Current Notes

Closeout checkpoint: this stream now lives at
`/home/cody/zisk-fv/.worktrees/memory-trust-gap` on branch `memory-trust-gap`.
Merge commit `a058ff0b` incorporates `origin/main`. The branch currently has a
large wrapper/adapter family that exposes progressively more honest memory
evidence shapes, but the next work should not add another equivalent wrapper.
The efficient closeout is to prove the accepted-execution extraction theorem
that supplies the existing replay-envelope construction from raw accepted trace
data, then prune the wrapper family. The merged baseline is stabilized:
`lake build ZiskFv.Compliance.RowProvenance ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance` passes after repairing post-merge `RowProvenance` API drift
and removing stale legacy load-address arguments from the Aeneas bridge audit
helpers.

Replay-row projection checkpoint:
`AcceptedFullExecutionMemoryReplayRowsProjection` now names a concrete
full-ensemble mutable Mem table plus the structural equality
`acceptedTrace.rows = memReplayRowsOfTable table`, and
`AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRowsProjection` derives
`MemReplayRowsEmbeddedInTrace` from that equality via
`memReplayRowsEmbeddedInTrace_of_rows_eq`. This removes one all-event embedding
caller field for this path, but it is not the final raw object: the accepted
split trace still carries chronology, prefix-read soundness, and initial
agreement, which must be proved from concrete accepted execution data.
Focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` and full `lake build` pass for
this slice. `trust/scripts/check-all-semantic.sh` also passes.
`trust/scripts/check-all.sh` is not clean in this worktree because broader
caller-burden/hypothesis ledgers have shrunk versus baseline and Aeneas
production extraction artifacts are missing/untracked; this slice did not
regenerate those broad ledgers.

Raw split-trace checkpoint:
`RawAcceptedAirMainMemFullTraceSplit` now names the canonical upstream accepted
AIR/Main/Mem split-trace data: initial Sail state, public memory-bus row
projection, concrete Mem trace columns, row count, and generated Mem rows. It
does not carry row ordering, prefix-read soundness, or initial Sail/replay
agreement as fields. `RawAcceptedAirMainMemReplayEvidence` isolates the two
remaining nonlocal replay obligations, `GeneratedMemRowOrderFacts` and
`MemoryBusRowsPrefixReadSound`, and
`AcceptedAirMainMemFullTraceSplitConstruction.ofRaw` lowers raw data plus those
proofs into the existing construction while proving initial agreement
internally by reflexivity. Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`,
focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, and full
`lake build`, `git diff --check`, and `trust/scripts/check-all-semantic.sh`
pass for this slice. Commit `a4214da8` records it.

Raw replay-row projection checkpoint:
`RawAcceptedFullExecutionMemoryReplayRowsProjection` now combines the raw
accepted AIR/Main/Mem split trace, the still-needed raw replay evidence, the
concrete full-ensemble Mem table, and the structural equality
`raw.rows = memReplayRowsOfTable table`.
`AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofRawRowsProjection`
lowers that raw package to the existing replay-only shared extraction,
discharging initial Sail/replay agreement through `ofRaw` and all-event table
embedding through `memReplayRowsEmbeddedInTrace_of_rows_eq`. This does not yet
prove `GeneratedMemRowOrderFacts` or `MemoryBusRowsPrefixReadSound`; it makes
them the remaining explicit proof target instead of hiding them behind an
accepted split trace. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, `git diff --check`, and
`trust/scripts/check-all-semantic.sh` pass for this uncommitted slice.

Soundness/completeness wording: this project is closing a soundness/trust gap.
The old axiom asserted memory-state agreement for selected loads. The remaining
work looks "completeness-like" only because we must prove that accepted
full-execution data covers the memory evidence needed by the soundness theorem.

Latest checkpoint: `OpEnvelope.MutableMemReplayRowsEmbeddedAtAcceptedSplitTrace`
and `OpEnvelope.SelectedEnvelopeMemRowAtAcceptedSplitTraceWithWitness` expose
the accepted split trace, all-event mutable-Mem replay embedding, and selected
envelope-row occurrence without requiring a selected prefix cursor. The new
constructor
`acceptedFullExecutionMemoryReplayEnvelopeSplitTraceConstructionAtEnvelope_of_acceptedAirMainMemSplitTraceAndPrefixState`
derives the selected prefix cursor from selected envelope-row coverage plus
`SelectedPrefixStateAtAcceptedAirMainMemTraceAtEnvelope`, and the public wrapper
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSplitTraceReplayEnvelopeStateSelection`
exposes that shape at the compliance theorem boundary. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass. This is still conditional: accepted full execution must
still prove the shared split trace, all-event replay embedding, selected
envelope-row occurrence, and prefix-state equality from actual accepted trace
data.

The active load path no longer carries `LoadTraceContext` inside
`LoadPromises`; `LoadPromises.memoryBurden` is now a standalone proposition over
the selected load event. The public theorem now takes
`OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope` plus
`OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope`: load
envelopes carry a shared accepted full-execution memory trace plus selected
envelope Mem-row occurrence and selected prefix cursor coverage indexed by that
trace; non-load envelopes carry no memory trace data. The split-indexed source
predicate, lower trace/table object, packed
accepted-at-envelope construction, generated Mem burden, packed row
construction, recursive `MemoryBusRowsReadWriteSound`, projected
`TraceReplaySound`, ordinary selected-row membership, and selected memory
cursor are derived internally. Raw row replay has an explicit equivalence to
projected Mem-event replay, and selected row cursors can be built from row
splits plus ordinary memory-read tags. The remaining gap is still global: there
is no theorem that constructs the cursor-shaped load evidence from accepted
full execution trace data.

The source-shaped public boundary exposes the next-more-honest memory evidence:
`OpEnvelope.AcceptedFullExecutionMemoryTraceSourceAtEnvelope` carries the shared
full-execution Mem trace, selected envelope Mem-row occurrence, and split-indexed
prefix-state equality, while deriving the selected prefix cursor internally. The
source coverage is now table-shaped directly, and
`acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_sourceCoverage` lowers it
through explicit load-case constructors to avoid generic `OpEnvelope` recursor
blowups. This slice passed `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, regenerated trust ledgers, both trust
check scripts, global closure print, targeted retired-memory scans, and
`nix run .#test`.

Status checkpoint: this is not currently blocked on a local Lean syntax or build
failure. The remaining risk is the final global proof obligation: accepted full
execution still has to produce one shared `AcceptedFullExecutionMemoryTrace` plus
per-load selected table-row occurrence, selected prefix cursor, and selected-row
occurrence uniqueness.
Historical adapter checkpoint:
`OpEnvelope.selectedMemProviderReplayRowInFullEnsembleMemTableAtEnvelope_of_envelopeMemRow`,
derives replay-provider selected coverage from an envelope Mem-row table
occurrence plus the load-arm `wr = 0` proof; it passed focused
`lake build ZiskFv.Compliance.OpEnvelope`.
The replay-only path now also has table-local envelope-row evidence:
`SelectedEnvelopeMemRowInMemTableAtEnvelope` lowers through
`selectedMemProviderReplayRowInMemTableAtEnvelope_of_envelopeMemRow`, and
`AcceptedFullExecutionMemoryReplayRowSplitTraceEnvelopeStateSelection*`
has been lifted to the construction boundary. Callers can now use
`AcceptedFullExecutionMemoryReplayEnvelopeSplitTraceConstructionAtEnvelope` or
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemReplayEnvelopeSplitTraceConstruction`
with selected envelope-row occurrence; provider replay-row coverage is derived
internally by
`selectedMemReplayProviderRowAtAcceptedSplitTraceConstructionWithWitness_of_envelopeRow`.
The earlier state-selection wrappers expose the same table-local envelope-row
shape at the compliance boundary. This avoids using the
full-ensemble table bridge, and therefore avoids reintroducing the read-only
mutable-Mem embedding just to derive selected provider-row replay coverage.
Generated split Mem construction now lowers through
`acceptedAirMainMemFullTraceSplitConstructionAtEnvelope_of_generatedMemFullTraceSplit`
and
`acceptedFullExecutionMemoryReplayEnvelopeSplitTraceConstructionAtEnvelope_of_generatedMemFullTraceSplit`.
The public wrapper
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayEnvelopeSplitTraceConstruction`
keeps generated Mem construction, all-event replay embedding, and selected
envelope-row occurrence visible.
The next wrapper,
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitReplayEnvelopeSelection`,
factors that generated evidence into one shared
`GeneratedMemFullTraceSplit` trace plus per-envelope selected-prefix,
all-event replay embedding, and selected envelope-row occurrence. This is still
conditional, but it matches the eventual accepted full-execution proof shape
more closely: shared Mem trace once, selected load coverage separately.
The shared-generated wrapper passed focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test`.
The accepted-trace counterpart,
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSplitTraceReplayEnvelopeSelection`,
now takes one shared `AcceptedAirMainMemFullTraceSplitAtEnvelope`, the
load-local selected prefix, all-event replay embedding, and selected envelope
Mem-row occurrence. This removes another packed per-envelope construction
boundary on the accepted route; it passed focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test`.
The follow-on wrapper slice exposes the same envelope-row state-selection shape
at the accepted split AIR/Main/Mem and generated split Mem construction theorem
levels; it passed focused `lake build ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test`.
No ZisK semantic bug has been identified so far; the issue is whether the
accepted-execution surface already exposes enough coverage/state facts to prove
that theorem, or whether the global construction layer must be strengthened.

Current generated-to-accepted checkpoint: `AcceptedAirMainMemFullTraceSplitConstruction.ofGenerated`
attaches Main-trace provenance to a generated split Mem trace construction.
This is record packaging only; the generated construction still contains the
local Mem rows, row-order facts, and replay facts that accepted full execution
must prove from the actual trace. This slice passed focused
`lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused
`lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Current generated-construction checkpoint:
`AcceptedAirMainMemFullTraceSplit.ofGenerated` packages generated split Mem
construction as the program-level accepted split trace, and
`AcceptedFullExecutionMemoryRowSplitExtraction.ofGeneratedMemTrace` packages
that trace with the witness-level mutable-Mem read/replay embedding predicates.
This is still record packaging: accepted full execution must still prove the
generated split construction and both embedding predicates from actual trace
data, while per-load provider-row and prefix selection remains a separate
obligation. Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`, focused
`lake build ZiskFv.Compliance.OpEnvelope`, focused
`lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

Current replay-provider source checkpoint:
`AcceptedFullExecutionMemoryReplayProviderSplitTraceSelectionAtEnvelope` and
`AcceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionSourceAtEnvelope`
state selected provider-row coverage in the all-event mutable-Mem replay shape
over split accepted AIR/Main/Mem traces, and
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionSource`
exposes that source directly at the compliance boundary. A heavier
construction-level replay-provider wrapper was attempted but removed from this
slice after dependent-type elaboration timeouts; the source boundary keeps the
selected replay-provider obligation visible without adding that expensive
adapter. Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`,
full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

Current generated replay-provider selection checkpoint:
`acceptedFullExecutionMemoryReplayProviderRowSplitTraceSelectionSourceAtEnvelope_of_selection`
packages extraction-indexed replay-provider split selection into the
load-scoped source shape, and
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayProviderSelection`
exposes generated split Mem construction plus replay-provider selected-row
coverage directly in the compliance theorem family. This is still conditional:
the generated split construction, mutable-Mem embeddings, selected prefix, and
selected replay-provider row remain caller obligations. Focused
`lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

Current replay-only boundary checkpoint:
`AcceptedFullExecutionMemoryReplayRowSplitExtraction` carries split accepted
AIR/Main/Mem trace data, one concrete mutable Mem table, and the all-event
`MemReplayRowsEmbeddedInTrace` proof for that table, without requiring the
older read-only mutable-Mem embedding. The new
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayRowSelection`
wrapper exposes generated split Mem construction plus witness-level all-event
replay embedding and selected provider/prefix coverage as the sufficient
top-level replay-provider boundary. This reduces a stale obligation but is
still conditional: accepted full execution must still prove generated split
construction, all-event replay embedding, selected provider-row coverage, and
selected prefix cursor from actual trace data. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

Current split replay-projection checkpoint:
`GeneratedMemFullTraceSplitConstruction.toAcceptedFullMemoryBusRowsTrace` and
`AcceptedAirMainMemFullTraceSplitConstruction.toAcceptedFullMemoryBusRowsTrace`
now lower split order/replay facts directly to the global raw-row replay trace.
`OpEnvelope.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_generatedSplitTraceAtEnvelope`
and
`OpEnvelope.acceptedFullMemoryBusRowsTraceConstructionAtEnvelope_of_acceptedAirMainMemSplitTraceAtEnvelope`
consume those split traces directly for load-scoped replay construction,
without first repacking through the older packed generated construction shape.
This is a real projection from existing split evidence, not final closure:
accepted full execution still has to produce the split trace and selected
prefix/provider facts. Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice.

Current replay-only construction checkpoint:
`AcceptedFullExecutionMemoryReplaySplitTraceConstructionWithWitness` and
`AcceptedFullExecutionMemoryReplaySplitTraceConstructionAtEnvelope` now carry
split accepted AIR/Main/Mem construction, all-event mutable-Mem replay
embedding, and selected provider replay-row coverage over the internally chosen
mutable Mem table without requiring the older read-only mutable-Mem embedding.
`acceptedFullExecutionMemoryReplayRowSplitTraceSelectionSourceAtEnvelope_of_replaySplitTraceConstruction`
lowers this construction package to the existing replay-only split trace
selection source. The new compliance wrappers
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayRowSplitTraceSelectionSource`,
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplaySplitTraceConstruction`,
and
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemReplaySplitTraceConstruction`
route it to the public compliance theorem. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice.

Current replay-only state-selection checkpoint:
`AcceptedFullExecutionMemoryReplayRowSplitTraceStateSelectionSourceAtEnvelope`
now packages a shared replay-only split extraction with per-load selected
provider-row coverage and prefix-state equality, and
`acceptedFullExecutionMemoryReplayRowSplitTraceSelectionSourceAtEnvelope_of_stateSelectionSource`
lowers it to the existing cursor-shaped replay-only source by deriving the
selected prefix cursor internally. The new compliance wrappers
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayRowSplitTraceStateSelection`
and
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryReplayRowSplitTraceStateSelectionSource`
make this proof shape available at the top level. This narrows the future
accepted-execution obligation to provider replay-row coverage plus prefix-state
agreement for a shared replay extraction, but it does not yet prove those facts
from the full execution trace.

Current replay-only prefix-state checkpoint:
`selectedMemReplayRowAtAcceptedAirMainMemTraceAtEnvelope_of_replayRowSplitExtractionProvider`
derives accepted chronological-row coverage from replay-only provider-row
coverage and the concrete table's all-event replay embedding.
`AcceptedFullExecutionMemoryReplayRowSplitTraceStateSelectionAtEnvelope` then
uses that row membership plus selected prefix-state equality to construct the
selected prefix cursor internally, and
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionReplayRowStateSelection`
exposes this closer-to-accepted-execution boundary at the compliance theorem
level. This still leaves generated split construction, all-event replay
embedding, provider-row coverage, and prefix-state equality as upstream
obligations. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

Current replay-only cursor-to-state adapter checkpoint:
`acceptedFullExecutionMemoryReplayRowSplitTraceStateSelectionAtEnvelope_of_selection`
converts the older replay-only cursor-shaped selected-load evidence into the
new prefix-state shape, deriving occurrence uniqueness from the accepted split
trace's `orderFacts.rowsNodup`. This is a compatibility bridge, not final
closure: accepted full execution still has to prove the selected provider row
and the prefix-state/cursor facts from the actual trace. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this adapter.

Current accepted-split replay-only checkpoint:
`AcceptedFullExecutionMemoryReplayRowSplitExtraction.ofAcceptedAirMainMemTrace`
selects the concrete mutable Mem table from the full RV64IM witness for an
accepted split AIR/Main/Mem trace, using only the witness-level all-event
mutable-Mem replay embedding. The top-level wrappers
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTraceSplitReplayRowSelection`
and
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTraceSplitReplayRowStateSelection`
expose this accepted-trace replay-only boundary directly. This removes the
generated-only detour for this route but remains conditional: accepted full
execution still has to construct the accepted split trace, all-event replay
embedding, selected provider-row coverage, and prefix-state equality. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

Historical top-level boundary checkpoint:
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionProviderSelection`
exposes the generated split Mem construction, mutable-Mem read/replay
embeddings, and extraction-indexed provider/prefix selection directly in the
top-level compliance theorem family. This is still conditional: it does not
prove those memory facts from accepted execution, but it prevents the current
boundary from being hidden behind manual row-split extraction packaging.
Focused `lake build ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this wrapper.

Current direct generated-boundary checkpoint:
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceConstructionAtEnvelope`
and
`zisk_riscv_compliant_program_bus_of_generatedMemFullTraceSplitConstructionAtEnvelope`
expose the generated Mem replay construction that the current load replay proof
actually consumes. This is boundary clarification, not trust closure: accepted
AIR/Main/Mem provenance wrappers remain integration targets, but accepted full
execution still has to prove generated Mem construction, mutable-Mem
read/replay embeddings, and selected provider/prefix coverage from actual trace
data. Focused `lake build ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for committed slice `a47f641f`.

Current selected replay-row checkpoint:
`OpEnvelope.SelectedMemReplayRowAtAcceptedAirMainMemTraceAtEnvelope` and
`selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_memReplayRow`
provide the semantically correct selected-row membership path from actual
read/write Mem replay rows. This avoids making future accepted-execution
integration prove the overbroad all-row read embedding for primary writes;
selected loads should instead prove their provider row is a read, then use
the existing replay-row embedding. Focused
`lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for committed slice `e0fe4794`.

Current provider replay-row checkpoint:
`OpEnvelope.SelectedMemReplayRowInTraceTableAtEnvelope`,
`OpEnvelope.SelectedMemProviderReplayRowInTraceTableAtEnvelope`, and
`selectedMemReplayRowInTraceTableAtEnvelope_of_providerReplayRow` add the
table-local selected replay-row path. The primary branch carries the concrete
Mem row `wr = 0` proof needed to use the actual read/write replay embedding;
dual rows remain read events by construction. Focused
`lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for committed slice `006f6179`.

Current replay-provider bridge checkpoint:
`OpEnvelope.SelectedMemReplayRowInFullEnsembleMemTableAtEnvelope`,
`OpEnvelope.SelectedMemProviderReplayRowInFullEnsembleMemTableAtEnvelope`,
`selectedMemReplayRowAtAcceptedAirMainMemTraceAtEnvelope_of_traceTable`, and
`selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_providerReplayRows`
connect the replay-provider row target to accepted selected-row membership via
the actual `replayEmbedded` path. This gives accepted full-execution integration
a semantically correct bridge for selected loads without requiring primary
writes to appear in the read-only replay projection. Focused
`lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for committed slice `ca4c40a0`.

Current replay-provider cursor checkpoint:
`OpEnvelope.AcceptedFullExecutionMemoryReplayProviderCursorExtractionAtEnvelope`,
`OpEnvelope.AcceptedFullExecutionMemoryReplayProviderTableCursorSourceAtEnvelope`,
and
`acceptedFullExecutionMemoryReplayProviderCursorExtractionAtEnvelope_of_fullEnsemblePrefixState`
make the table-parametric cursor extraction target available for actual
read/write replay-provider rows. The constructor derives selected chronological
membership through `selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_providerReplayRows`.
Focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for committed slice `c1287b25`.

Current checkpoint after committed slice `f256fd0d`: the ROM/source-legality
split is verified and committed, and the next row-indexed source-legality bridge
is focused-build verified. `ZiskFv/AirsClean/Main/Constraints.lean` now exposes
generic ROM-message and source-sum eval lemmas, and
`ZiskFv/AirsClean/FullEnsemble/Balance.lean` uses those lemmas to prove that
`MainProgramRomRowsSourceMultiplicitySound` implies the env-shaped
`MainProgramRomSourceMultiplicitySound`. The next source-legality task is
proving the row-indexed predicate from actual row provenance/source facts.

Current checkpoint after committed slice `e89d100d`: selected-row source
multiplicity is now proved from `MainRowProvenance`, and `OpEnvelope` has an
adapter to the AIR-level `MainRomRowSourceMultiplicitySound` for that concrete
row. This slice passed focused `RowProvenance`/`OpEnvelope` builds, full `lake
build`, both trust scripts, and `nix run .#test`. It does not discharge
`MainProgramRomRowsSourceMultiplicitySound` yet: that predicate quantifies over
any arbitrary row matching opaque `program i`, so provenance for one selected
Main row is insufficient. The honest remaining choice is either to add a
program-wide ROM provenance/well-formedness bridge for every `program i`, or to
refactor the direct-`LD` route so it consumes selected row provenance instead of
the program-wide source-legality predicate.

Current checkpoint after the direct-route cleanup: selected-row provenance also
cannot rule out the Main self-provider branch by itself, because that branch can
select an arbitrary Main provider row from the witness. `OpEnvelope` therefore
no longer provides direct-`LD` active-route wrappers that silently derive
provider cursor evidence from `MainProgramRomSourceMultiplicitySound`; the
route-friendly path is the positive `DirectLoadAlignedMutableMemProviderRouteAtEnvelope`
boundary plus same-table prefix cursor evidence. The focused
`lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, both trust
scripts, and `nix run .#test` gates pass for this cleanup.

Current provider-prefix checkpoint: `OpEnvelope` now has
`acceptedFullExecutionMemoryProviderTraceCursorCoverageAtEnvelope_of_prefixCursor`
and
`acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_prefixCursor`.
These constructors build the provider-shaped public memory boundary from the
natural accepted-execution facts: a shared `AcceptedFullExecutionMemoryTrace`,
selected provider-row replay coverage in the witness-selected Mem table, and
the selected chronological prefix cursor. The selected occurrence uniqueness
field is derived internally from `fullTrace.acceptedTrace.construction.rowsNodup`.
Focused `lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`,
both trust scripts, and `nix run .#test` passed for the committed provider-prefix
source slices.

Current checkpoint after provider-trace-construction wrapper: the wrapper slice adds a provider-shaped accepted
trace construction package that replaces the older selected envelope-row
equality obligation with concrete primary/dual provider-row replay coverage in
the witness-selected mutable Mem table. The lowering now reuses the existing
provider-selection constructor instead of normalizing provider-row coverage
directly, and focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass. The larger
remaining gap is still the global accepted-execution theorem that constructs the
shared Mem trace and per-envelope selected provider-row/prefix coverage.

Current checkpoint after split provider construction boundary: the split boundary exposes
`AcceptedAirMainMemFullTraceSplitConstructionAtEnvelope` at the provider
compliance theorem surface. This keeps generated Mem row facts, row-order facts,
and replay facts separated until the final lowering to the packed construction.
Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass.

Current provider-prefix source checkpoint: `OpEnvelope` now exposes
`AcceptedFullExecutionMemoryProviderPrefixSourceAtEnvelope`, with load cases
carrying a shared `AcceptedFullExecutionMemoryTrace`, selected provider-row
replay coverage, and selected chronological prefix cursor, but no caller
supplied uniqueness proof. The lowering theorem
`acceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope_of_providerPrefixSource`
derives uniqueness from `rowsNodup`, and
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderPrefixSource`
exposes that boundary at the global compliance layer. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice.

Current primary-boundary checkpoint: `zisk_riscv_compliant_program_bus` now
consumes `AcceptedFullExecutionMemoryProviderPrefixSourceAtEnvelope` directly.
The older provider cursor source wrapper remains as compatibility evidence and
forgets uniqueness before calling the primary theorem. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice.

Current accepted-provider-selection checkpoint: `OpEnvelope` now names
`AcceptedFullExecutionMemoryProviderTraceSelectionAtEnvelope`, and
`Compliance.lean` exposes
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSelection`.
This lets callers provide accepted AIR/Main/Mem trace data, read/replay
embeddings, and selected provider-row/prefix evidence directly; the wrapper
lowers those facts to the primary provider-prefix source boundary. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice.

Current row-extraction provider-selection checkpoint: `Compliance.lean` now
exposes
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryProviderRowCursorSelection`,
the direct shared-extraction theorem for provider-row cursor-shaped selected
load evidence. Focused `lake build ZiskFv.Compliance` passes; full gates are
also complete: full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

The latest theorem split records the exact promotion needed when full execution
naturally produces a selected prefix cursor rather than the stronger
split-indexed state predicate. `SelectedLoadMemoryBusRowPrefixCursor.prefixUnique`
and `state_eq_of_prefixUnique` prove that cursor state equality plus selected
occurrence uniqueness implies all-splits prefix-state equality; the envelope
constructors `selectedPrefixStateAtFullEnsembleMemTableAtEnvelope_of_prefixUnique`
and `acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_prefixUnique` package
that bridge for the public source boundary. The direct-`LD` variant
`directLoadMutableMemProviderPrefixStateAtEnvelope_of_prefixCursor` now consumes
same-table selected prefix cursors, derives occurrence uniqueness from
`fullTraceTable.acceptedTrace.construction.rowsNodup`, and feeds the
route-plus-prefix source composition through a replay-shaped prefix-cursor
wrapper. Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed for this slice, and later full-gate runs also passed.

The current public-boundary slice adds
`OpEnvelope.AcceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope` and
`OpEnvelope.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope`, then changes
`zisk_riscv_compliant_program_bus` to consume that cursor-shaped package. The
theorem derives `AcceptedFullExecutionMemoryTraceSourceAtEnvelope` internally
with `acceptedFullExecutionMemoryTraceSourceAtEnvelope_of_cursorSource`. This
makes the accepted-execution obligation visible as shared trace + selected row
+ selected cursor + selected occurrence uniqueness, instead of asking callers
for the already-promoted split-indexed source predicate. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, closure print with zero project axiom names,
targeted retired-memory scan, and `nix run .#test` passed for this slice.

The latest construction bridge adds
`OpEnvelope.SelectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope`
and
`OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_traceConstructionAndPrefixUnique`.
It proves that the older load-scoped full-execution construction object already
contains the shared trace, selected envelope row, and selected prefix cursor
needed by the current public memory boundary; the extra fact is exactly
selected-prefix occurrence uniqueness. Focused `lake build
ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, closure print with zero
project axiom names, targeted retired-memory scan, and `nix run .#test` passed
for this slice.

The helper slice adds
`List.prefix_eq_of_nodup_splits` and
`SelectedLoadMemoryBusRowPrefixCursor.prefixUnique_of_nodup`, proving that a
duplicate-free accepted row list is enough to discharge the selected-prefix
uniqueness side condition. This passed focused `lake build
ZiskFv.Compliance.OpEnvelope`. It does not by itself close the gap: accepted
full execution still has to provide `rows.Nodup` or another real uniqueness
invariant, plus the shared trace/coverage/cursor evidence.

The construction-boundary slice makes that uniqueness invariant part
of the accepted Mem trace object: `AcceptedFullMemoryBusRowsTrace`,
`GeneratedMemFullTraceConstruction`, and
`AcceptedAirMainMemFullTraceConstruction` now carry `rowsNodup`. The envelope
bridge
`selectedPrefixUniqueAtAcceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_nodup`
derives selected occurrence uniqueness from that field, and
`acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_traceConstruction`
uses it to lower the construction package to the current cursor-source package.
`zisk_riscv_compliant_program_bus` now consumes
`OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` and derives
cursor-source evidence internally. Focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec`, focused `lake build
ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, and full
`lake build` passed for this slice. `trust/scripts/regenerate.sh`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, closure
print with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` also passed.

The accepted-trace packaging slice adds
`AcceptedFullExecutionMemoryTrace.ofAcceptedAirMainMemTrace` and
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemFullTrace`. This exposes
the next upstream integration target as accepted AIR/Main/Mem trace data plus
the full RV64IM witness, mutable-Mem embedding, and selected per-envelope
coverage; it does not prove the remaining semantic Mem fields. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
trust regeneration, both trust gates, closure print with no project axiom names,
targeted retired-memory scan, and `nix run .#test` passed.

The latest FullEnsemble balance slice adds
`ActiveMainMemProviderRowMatchSpec` and
`activeMainMemProviderRowMatchSpec_of_active_main_eval`, a named form of the
balanced active-Main memory-bus provider-row coverage theorem. This is a
verified proof-surface improvement, not the final extraction theorem: the
provider result still exposes MemAlignReadByte, MemAlignByte, MemAlign,
mutable-Mem primary/dual, and unified-Main branches. The next proof needs to
split by route rather than assume one blanket exclusion: LD/direct full-width
loads should refine the provider result to the mutable-Mem branch, while
subword loads already carry `MemAlignWitness` and likely need a chained
Main-to-MemAlign-to-mutable-Mem selected-row proof.

The current route-split slice adds
`ActiveMainMutableMemProviderRowMatchSpec`,
`ActiveMainNonMutableMemProviderRowMatchSpec`,
`activeMainMemProviderRowMatchSpec_mutable_or_nonmutable`, and
`activeMainMutableMemProviderRowMatchSpec_of_no_nonmutable`. These lemmas do
not prove the route facts themselves; they make the next direct-load proof
target exact: derive the mutable-Mem provider row by ruling out the named
non-mutable branch family. Focused `lake build
ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

The current provider-row extraction slice adds
`AcceptedAirMainMemFullTraceWithFullEnsembleMemTable.of_table`,
`OpEnvelope.acceptedAirMainMemFullTraceWithFullEnsembleMemTableAtEnvelope_of_table`,
`OpEnvelope.selectedRowMembershipAtAcceptedAirMainMemTraceAtEnvelope_of_providerReplay`,
`OpEnvelope.AcceptedFullExecutionMemoryProviderCursorExtractionAtEnvelope`, and
`OpEnvelope.acceptedFullExecutionMemoryProviderCursorExtractionAtEnvelope_of_fullEnsemblePrefixState`.
This avoids the table-choice/equality mismatch found after the route split:
balanced full execution naturally identifies a concrete provider table and row
whose replay projection matches the selected load bus entry, not necessarily
the older envelope-carried Clean Mem row. Focused `lake build
ZiskFv.Compliance.OpEnvelope`, full `lake build`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass.

The current construction-wrapper slice adds
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceConstruction`.
It lets upstream callers provide the packed
`OpEnvelope.AcceptedFullExecutionMemoryTraceConstructionAtEnvelope` directly,
while the theorem projects the split shared-trace and per-envelope coverage
inputs required by `zisk_riscv_compliant_program_bus` internally. This is not
the final global discharge theorem; it makes the next source-shaped boundary
explicit and reusable. Focused `lake build ZiskFv.Compliance` passes; full
`lake build`, trust regeneration, both trust gates, and `nix run .#test` pass.

The selected-coverage slice adds
`OpEnvelope.AcceptedFullExecutionMemoryTraceSelectionAtEnvelope`,
`acceptedFullExecutionMemoryTraceCoverageAtEnvelope_of_selection`, and
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSelection`. It unpacks
the per-envelope memory coverage obligation into the selected chronological
prefix and selected witness Mem-row occurrence that accepted full execution
must actually produce. This still does not prove the semantic
`AcceptedAirMainMemFullTrace` fields. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, closure print with no project axiom names,
targeted retired-memory scan, and `nix run .#test` passed.

The current working edit adds no-wrap bridge lemmas for the packed Mem
increment and segment-distance expressions:
`field_increment_val_eq_incrementNat` and
`field_distance_val_eq_distanceChunksNat`. These are local arithmetic bridges
needed by chronology proofs that move from generated field equalities to Nat
order facts. Focused `lake build ZiskFv.Airs.Mem`, dependent focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
closure print with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` passed for this slice.

The next working edit adds generated-delta consequences:
`delta_step_val_eq_incrementNat_of_same_addr_segment_every_row`,
`delta_step_val_pos_of_same_addr_segment_every_row`,
`delta_addr_val_eq_incrementNat_of_addr_change_segment_every_row`, and
`delta_addr_val_pos_of_addr_change_segment_every_row`. These combine the
generated Mem segment equations with the no-wrap increment bridge so chronology
proofs can use positive Nat representatives instead of raw field equalities.
Focused `lake build ZiskFv.Airs.Mem` passes. The dependent focused build `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance` also passes. Full `lake build`, trust regeneration, both
trust gates, closure print with zero project axiom names, targeted retired-memory
scan, and `nix run .#test` passed for this slice.

The dual-step chronology slice adds range/no-wrap facts:
`step_columns_in_range`, `dual_step_delta_in_range`,
`step_dual_ge_step_add_wr_of_dual_step_delta_range`,
`dual_step_delta_val_eq_nat_sub_of_range`,
`step_le_step_dual_of_dual_step_delta_range`, and
`step_lt_step_dual_of_wr_one_dual_step_delta_range`. These model the PIL
`range_check(step_dual - step - wr, 0, 2^24 - 1, sel_dual)` no-wrap consequence
needed to order primary and dual Mem events inside one row. Focused `lake build
ZiskFv.Airs.Mem`, dependent focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
closure print with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` passed for this slice.

The current working edit adds
`previous_step_le_step_of_same_addr_segment_every_row`, a no-wrap bridge from
the generated same-address increment equation to Nat chronology between the
row's carried `previous_step` and current `step`. This is the row-to-row
chronology counterpart to the dual-step in-row ordering fact. Focused
`lake build ZiskFv.Airs.Mem` and dependent focused `lake build
ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
closure print with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` passed for this slice.

The current working edit adds direct projections for `previous_row_step`: when
the previous row has no dual event it is the previous primary `step`, and when
`sel_dual = 1` it is `step_dual`. It also combines those projections with the
same-address previous-step chronology theorem to prove non-boundary chronology
from the previous primary or dual emitted timestamp into the current row's
primary timestamp. Focused `lake build ZiskFv.Airs.Mem` and dependent focused
`lake build ZiskFv.AirsClean.Mem.TraceSpec ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
closure print with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` passed for this slice.

The Mem segment-continuity slice adds named consequences of
`ZiskFv.Airs.Mem.segment_every_row`: at non-boundary rows
(`segment_l1 row = 0`), the previous-address/value expressions reduce to the
previous row, same-address rows carry the previous address, and same-address
reads carry the previous `value_0`/`value_1` chunks. These lemmas are a real
piece of the future `prefixReadSound` proof; segment-boundary carry-in and
chronological replay remain separate obligations. Focused `lake build
ZiskFv.Airs.Mem`, full `lake build`, trust regeneration, both trust gates,
closure print with no project axiom names, targeted retired-memory scan, and
`nix run .#test` passed.

The split-construction slice adds `GeneratedMemRowOrderFacts`,
`GeneratedMemReplayFacts`,
`GeneratedMemFullTraceSplitConstruction`, and
`AcceptedAirMainMemFullTraceSplitConstruction`. These do not discharge the
remaining semantic Mem obligations; they split the upstream theorem target so
generated row constraints, chronological uniqueness/order, and Sail/replay
agreement can be proved independently and then repacked into the existing
construction object. Focused `lake build ZiskFv.AirsClean.Mem.TraceSpec`
passed, as did focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates,
closure print with no project axiom names, the retired-memory declaration scan,
and `nix run .#test`.

The increment/distance arithmetic slice adds `incrementNat`,
`increment_chunks_in_range`, `distanceChunksNat`, and
`distance_chunks_in_range` in `ZiskFv.Airs.Mem`, plus positivity and
Goldilocks-modulus no-wrap bounds for those Nat interpretations. These facts
mirror the PIL `bits(22)`, `bits(16)`, and two-`bits(16)` range checks and are
intended as the arithmetic input for the next chronology proof; they do not yet
prove chronological row ordering. Focused `lake build ZiskFv.Airs.Mem`,
focused `lake build ZiskFv.AirsClean.Mem.TraceSpec
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust gates, closure print with no project axiom names, the
retired-memory declaration scan, and `nix run .#test` passed.

The Mem segment-boundary slice adds the complementary boundary facts from
`ZiskFv.Airs.Mem.segment_every_row`: at rows with `segment_l1 row = 1`,
the previous-address/value expressions reduce to `previous_segment_*`; at rows
where `segment_l1 (row + 1) = 1`, the current value chunks, address, and
effective step are recorded as `segment_last_*`. These are still local
algebraic consequences; the cross-segment chronological replay proof remains
open. Focused `lake build ZiskFv.Airs.Mem`, full `lake build`, trust
regeneration, both trust gates, closure print with no project axiom names,
targeted retired-memory scan, and `nix run .#test` passed.

The Mem step/delta slice adds generated-order consequences from
`ZiskFv.Airs.Mem.segment_every_row`: the `previous_step` witness reduces to
the previous row's effective step at non-boundary rows and to
`previous_segment_step` at segment boundaries; the generated increment equation
reduces to `delta_step` for same-address rows and `delta_addr` for address
changes. These facts are prerequisites for chronological replay, but they do
not yet prove Nat-level timestamp monotonicity or accepted full-trace
construction. Focused `lake build ZiskFv.Airs.Mem`, full `lake build`, trust
regeneration, both trust gates, closure print with no project axiom names,
targeted retired-memory scan, and `nix run .#test` passed.

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

The cursor-construction slice adds
`OpEnvelope.acceptedAirMainMemFullTraceAtEnvelope_of_construction`, recovering
the shared accepted AIR/Main/Mem trace object from the load-scoped accepted
trace construction. Focused `lake build ZiskFv.Compliance.OpEnvelope` passed.
This is a small verified reduction: it removes one separately supplied selected
prefix cursor from the planned next constructor, but it does not yet prove the
remaining full-execution embedding or selected Mem-row occurrence obligations.

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

The construction-payload cleanup replaces the anonymous nested Sigma/PLift
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

The active load-scoped public-boundary slice changes
`zisk_riscv_compliant_program_bus` to consume
`OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope` rather than
a shared trace plus a separate per-envelope coverage argument. Load envelopes
still expose the accepted full-execution memory trace and selected coverage,
while non-load envelopes carry only `ULift Unit`; the older construction object
is derived internally by
`OpEnvelope.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_traceWithCoverage`.
Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed;
full `lake build`, both trust check scripts, global compliance closure print
with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` also passed.

The current theorem-surface split exposes the shared trace and selected
coverage as separate public binders:
`OpEnvelope.AcceptedFullExecutionMemoryTraceAtEnvelope` and
`OpEnvelope.AcceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope`.
The compatibility package
`OpEnvelope.AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope` is rebuilt
internally by
`OpEnvelope.acceptedFullExecutionMemoryTraceWithCoverageAtEnvelope_of_split`.
Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance` passed;
full `lake build`, trust regeneration, both trust gates, closure print with
zero project axiom names, targeted retired-memory scan, and `nix run .#test`
also passed.

The current construction-projection slice adds
`OpEnvelope.acceptedFullExecutionMemoryTraceAtEnvelope_of_traceConstruction`
and
`OpEnvelope.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_traceConstruction`.
These directly project the split public trace and coverage binders from the
older `AcceptedFullExecutionMemoryTraceConstructionAtEnvelope`, avoiding the
packed `AcceptedFullExecutionMemoryTraceWithCoverageAtEnvelope` compatibility
route for callers that already have construction evidence. Focused
`lake build ZiskFv.Compliance.OpEnvelope`, full `lake build`, both trust gates,
closure print with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` passed.

Current inspection found no local Lean blocker in the split/projection layer.
The remaining trust gap is upstream: `AcceptedAirMainMemFullTrace` and
`AcceptedFullExecutionMemoryTrace` still contain semantic fields that must be
constructed from accepted full execution, especially `rowsNodup`,
`chronologicalRows`, `prefixReadSound`, `initialAgreement`, mutable Mem-table
embedding, selected envelope-row occurrence, and selected prefix cursor
coverage. These fields are visible rather than hidden, but they are still the
proof work left to close.

The shared-trace wrapper slice adds
`OpEnvelope.acceptedFullExecutionMemoryTraceAtEnvelope_of_fullTrace`,
`OpEnvelope.acceptedFullExecutionMemoryTraceCoverageForTraceAtEnvelope_of_fullTraceCoverage`,
and
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTrace`. This variant
consumes one shared `AcceptedFullExecutionMemoryTrace` plus ordinary
per-envelope coverage, then lowers to the current split public theorem
internally. Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`
passed; full `lake build`, trust regeneration, both trust gates, closure print
with zero project axiom names, targeted retired-memory scan, and
`nix run .#test` also passed.

The current replay-embedding slice adds polarity-preserving mutable-Mem replay
row projections in `ZiskFv.AirsClean.FullEnsemble.Balance` and exposes
`MutableMemReplayRowsEmbeddedInTrace` beside the existing selected-read
embedding. `AcceptedFullExecutionMemoryTrace`,
`AcceptedFullExecutionMemoryTraceConstructionWithWitness`, and the public
accepted AIR/Main/Mem wrapper theorems now carry both obligations: read-only
embedding for selected load coverage and all-event replay embedding for future
store/update replay construction. Focused
`lake build ZiskFv.AirsClean.FullEnsemble.Balance` and
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, closure print with zero
project axiom names, targeted retired-memory scan, and `nix run .#test` passed
for this slice.

Status checkpoint: this is not a current local Lean proof loop. The last two
slices were verified and committed. The remaining work is the upstream global
construction theorem: deriving the accepted Mem trace, replay agreement, and
selected load coverage from accepted full-execution data instead of taking those
semantic fields as top-level evidence. No ZisK semantic bug has been identified
so far; the issue is still a proof-surface/trust-boundary gap.

The accepted-selection bridge slice adds
`OpEnvelope.acceptedFullExecutionMemoryTraceConstructionAtEnvelope_of_acceptedAirMainMemSelection`
and routes
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSelection` through
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceConstruction`.
This aligns the source-shaped accepted AIR/Main/Mem selection boundary with the
packed construction theorem used by replay, without claiming the upstream
accepted-execution construction has been proved. Focused
`lake build ZiskFv.Compliance.OpEnvelope` and
`lake build ZiskFv.Compliance` passed. Full `lake build`, trust regeneration,
both trust gates, and `nix run .#test` also passed.

The source-wrapper slice exposes
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceSource` and
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryTraceCursorSource`.
These wrappers lower the already-defined source and cursor-source memory
evidence through selected coverage and the packed construction path internally.
The visible upstream target is now
`OpEnvelope.AcceptedFullExecutionMemoryTraceCursorSourceAtEnvelope`: construct
the shared accepted Mem trace, selected envelope row, selected chronological
prefix cursor, and selected occurrence uniqueness from accepted full-execution
data. Focused `lake build ZiskFv.Compliance` passed.

The current accepted-selection bridge slice adds
`OpEnvelope.acceptedFullExecutionMemoryTraceCursorCoverageAtEnvelope_of_selection`
and
`OpEnvelope.acceptedFullExecutionMemoryTraceCursorSourceAtEnvelope_of_selection`.
This derives selected-prefix occurrence uniqueness from
`acceptedTrace.construction.rowsNodup` instead of requiring a separate
uniqueness input, and routes
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemSelection` through the
cursor-source public wrapper. Focused
`lake build ZiskFv.Compliance.OpEnvelope` and focused
`lake build ZiskFv.Compliance` pass; full `lake build`, trust regeneration,
both trust gates, and `nix run .#test` also pass. This still does not construct
the accepted Mem trace, selected row occurrence, or selected prefix cursor from
accepted full execution; those remain the upstream theorem target.

The unpacked construction-wrapper slice adds
`OpEnvelope.acceptedFullExecutionMemoryTraceConstructionWithWitness_of_fields`
and
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemTraceConstruction`.
This exposes the current upstream construction target as separate accepted
AIR/Main/Mem construction, full RV64IM witness, mutable-Mem read/replay
embeddings, and selected envelope Mem-row occurrence fields, then routes them
through the cursor-source theorem. Focused
`lake build ZiskFv.Compliance.OpEnvelope` and focused
`lake build ZiskFv.Compliance` pass. This is still a boundary-sharpening step:
it does not prove the accepted Mem trace construction, embeddings, selected row
occurrence, or selected cursor from full execution.

Post-commit inspection of `ZiskFv.AirsClean.FullEnsemble.Balance` confirms the
next missing object is not another table-selection projection. The existing
`exists_mem_table_of_fullRv64im_witness` theorem explicitly selects the
dual-aware mutable Mem table but does not assert chronological embedding of
that table's projected rows into an accepted memory trace. The balance module
has selected-provider and message-match lemmas from `witness.BalancedChannels`
and `witness.Spec`, but no theorem that constructs the accepted chronological
row list, `rowsNodup`, chronological order, prefix read soundness, initial
agreement, or mutable-Mem replay embeddings from those channel facts. The next
real proof target must therefore introduce/prove the accepted memory-bus row
extraction from balanced full-execution interactions before the current
cursor-source obligations can be discharged globally.

The current boundary-naming slice adds
`AcceptedFullExecutionMemoryRowExtraction` as the shared accepted-execution Mem
row extraction result: accepted AIR/Main/Mem trace plus witness-level mutable-Mem
read and read/write replay embeddings. `Compliance.lean` now has wrappers that
consume this shared package with either ordinary per-envelope coverage or the
unpacked selected-prefix/selected-row evidence. This is not the missing global
row-extraction proof; it gives that proof a named result shape. Focused
`lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, and `nix run .#test` pass
for this slice.

The current selected-load boundary slice adds
`OpEnvelope.AcceptedFullExecutionMemoryRowSelectionAtEnvelope`, the
extraction-indexed view of selected prefix plus selected envelope Mem-row
evidence. It also adds lowering helpers from row extraction/selection to
ordinary coverage and cursor-source evidence, and changes the top-level
row-extraction selection wrapper to consume this named selection package.
Focused `lake build ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full
`lake build`, trust regeneration, both trust gates, and `nix run .#test` pass
for this slice.

The current cursor-selection split adds
`OpEnvelope.AcceptedFullExecutionMemoryRowCursorSelectionAtEnvelope`, which
indexes the selected mutable-Mem provider-row occurrence and selected
chronological prefix cursor by the shared `AcceptedFullExecutionMemoryRowExtraction`.
It also adds a bridge to the older row-selection shape and a new compliance
wrapper
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelection`.
This is the sharper upstream target for accepted full-execution replay: prove
shared row extraction once, then prove selected row plus selected cursor per
load; selected occurrence uniqueness is still derived internally from
`rowsNodup`. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice. It still does not construct the accepted
chronological Mem row trace, witness mutable-Mem embeddings, selected row
occurrence, or selected cursor from balanced full-execution interactions.

The unpacked split-indexed provider-construction wrapper slice adds
`zisk_riscv_compliant_program_bus_of_acceptedAirMainMemProviderSplitTraceConstruction`.
It keeps the split construction, split-indexed mutable-Mem read/replay
embeddings, and split-indexed selected provider-row coverage visible at the
top-level wrapper instead of forcing callers through the non-split
`acceptedAirMainMemFullTraceConstructionAtEnvelope_of_split` detour. Focused
`lake build ZiskFv.Compliance` passes after moving the wrapper below the lower
split provider-construction theorem it calls. This is still boundary plumbing;
the accepted full-execution trace still has to prove the shared split trace and
selected coverage rather than supply them.

The current row-cursor source slice adds
`OpEnvelope.AcceptedFullExecutionMemoryRowCursorSelectionSourceAtEnvelope`, a
load-scoped `Σ extraction, cursorSelection` package. It bridges this package to
the existing cursor-source replay path, adds a constructor from the older
load-scoped accepted-trace construction object, and exposes
`zisk_riscv_compliant_program_bus_of_acceptedFullExecutionMemoryRowCursorSelectionSource`.
This unifies the final per-envelope target: accepted full execution should
produce one shared row extraction plus selected mutable-Mem row and selected
prefix cursor for each load. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

The current primary-boundary slice changes
`zisk_riscv_compliant_program_bus` itself to consume
`OpEnvelope.AcceptedFullExecutionMemoryRowCursorSelectionSourceAtEnvelope`.
The older split full-trace, packed construction, source-shaped, cursor-source,
row-extraction, and accepted AIR/Main/Mem theorem variants remain as wrappers
that lower into this sharper public theorem boundary. This makes the
top-level compliant theorem expose the real remaining accepted-execution
memory obligation directly: for load envelopes, accepted full execution must
produce shared row extraction plus selected mutable-Mem row and selected prefix
cursor evidence; non-load envelopes carry no memory data. Focused `lake build
ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice.

The provider-boundary slice adds provider-row versions of the shared trace
cursor coverage, trace cursor source, extraction-indexed cursor selection, and
load-scoped row-cursor source package. `zisk_riscv_compliant_program_bus` now
consumes
`OpEnvelope.AcceptedFullExecutionMemoryProviderTraceCursorSourceAtEnvelope`
directly, and the replay chain lowers from the selected prefix cursor without
reconstructing the older envelope-row extraction object. Older envelope-row
theorem variants remain as compatibility wrappers via
`selectedMemProviderReadReplayRowInFullEnsembleMemTableAtEnvelope_of_envelopeMemRow`.
Focused `lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust gates, and
`nix run .#test` pass for this slice. The remaining global target is still to
derive the shared accepted Mem row extraction plus per-load provider replay
coverage and selected prefix cursor from balanced accepted full execution.

The current direct-load route slice adds
`OpEnvelope.DirectLoadMutableMemProviderRouteAtEnvelope` and
`OpEnvelope.DirectLoadMutableMemProviderReplayAtEnvelope`, plus
`directLoadMutableMemProviderReplayAtEnvelope_of_route`. For `LD`, the bridge
uses the mutable branch of balanced active-Main provider coverage to construct
a table-parametric FullEnsemble Mem-table object for the exact provider table
found by balance, then composes the envelope's selected Main `bMem` entry match
with the primary/dual provider entry match. This deliberately remains
Prop-valued because the balance provider table is obtained from Prop-level
existential coverage. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice. The next route obligations are proving
direct `LD` excludes the non-mutable branch family, and following legitimate
subword MemAlign branches to mutable Mem.

The current branch-exclusion split adds named FullEnsemble branch predicates
for MemAlignReadByte, MemAlignByte, MemAlign, and Main self-provider cases
inside `ActiveMainNonMutableMemProviderRowMatchSpec`, plus a proof that ruling
out all four rules out the aggregate non-mutable family. At the envelope level,
`OpEnvelope.DirectLoadActiveMainMemProviderRouteAtEnvelope` exposes balanced
active-Main provider coverage before branch selection, and
`OpEnvelope.DirectLoadNoNonMutableMemProviderRouteAtEnvelope` exposes the four
direct-`LD` exclusions needed by
`directLoadMutableMemProviderRouteAtEnvelope_of_active_route`. This slice is
honest about the remaining gap: it does not prove those exclusions; it gives
the Main/ROM provenance integration a precise target. Focused
`lake build ZiskFv.AirsClean.FullEnsemble.Balance`, focused `lake build
ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full
`lake build`, `trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice.

The latest provenance/source-fact slice adds
`MainRowProvenance.LdRowMode`,
`OpEnvelope.DirectLoadMainRowProvenanceAtEnvelope`,
`OpEnvelope.DirectLoadMainBSourceFactsAtEnvelope`, and
`directLoadMainBSourceFactsAtEnvelope_of_rowProvenance`. This records the real
production direct-`LD` row shape (`CopyB`, `b_src_ind`, `ind_width = 8`,
`store_reg`) for the exact evaluated Clean Main row, which is stronger than the
existing envelope `h_main_row` core-row equality and is needed for ROM selector
facts. Focused `lake build ZiskFv.Compliance.RowProvenance`, focused
`lake build ZiskFv.Compliance.OpEnvelope`, focused `lake build
ZiskFv.Compliance`, full `lake build`, `trust/scripts/regenerate.sh`,
`trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and
`nix run .#test` pass for this slice. The immediate remaining local route work
is to combine these source facts with raw memory-channel provider-route facts
to prove the four direct-`LD` non-mutable exclusions.

The byte-width exclusion slice proves the first two direct-`LD` non-mutable
provider exclusions. `OpEnvelope.directLoadMainBMessageWidthAtEnvelope` derives
that direct `LD` Main `bMem` has raw memory-bus width 8, while
`directLoadNoMemAlignReadByteProviderRouteAtEnvelope_of_sourceFacts` and
`directLoadNoMemAlignByteProviderRouteAtEnvelope_of_sourceFacts` rule out the
MemAlignReadByte and MemAlignByte provider branches because their raw pushed
messages have width 1 and balance equates the full raw message. The package
predicate `DirectLoadNoByteMemAlignProviderRouteAtEnvelope` deliberately covers
only those two branches; generic MemAlign and Main self-provider remain visible
open obligations. Focused `lake build ZiskFv.Compliance.OpEnvelope` passes for
this slice, as do focused `lake build ZiskFv.Compliance`, full `lake build`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

The residual route-boundary split adds
`OpEnvelope.DirectLoadNoResidualNonMutableMemProviderRouteAtEnvelope` for the
two still-open direct-`LD` branches: generic MemAlign and Main self-provider.
`directLoadNoNonMutableMemProviderRouteAtEnvelope_of_byte_and_residual`
combines the already-proved byte-width exclusions with that residual predicate,
and `directLoadMutableMemProviderRouteAtEnvelope_of_active_route_and_residual`
promotes active route coverage to the mutable-Mem route using source facts plus
only the residual obligations. Focused `lake build
ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full
`lake build`, `trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
split.

The Main self-provider split adds
`ZiskFv.AirsClean.FullEnsemble.MainMemBusMultiplicitySound`, a witness-level
invariant saying unified Main memory-bus interactions in the full ensemble have
multiplicity `-1` or `0`. Under that named invariant,
`no_activeMainSelfMemProviderRowMatchSpec_of_mainMemBusMultiplicitySound` rules
out the direct-`LD` Main self-provider residual branch, and
`directLoadMutableMemProviderRouteAtEnvelope_of_active_route_and_genericMemAlign`
now needs only the generic MemAlign exclusion plus this explicit
source-legality invariant. This is intentionally not hidden trust removal yet:
`MainMemBusMultiplicitySound` still has to be proved from ROM/source legality
and accepted full-execution facts. Focused and full gates passed for this split
before commit.

Follow-up route audit: the remaining generic MemAlign exclusion cannot be
proved as a blanket direct-`LD` fact. ZisK's emulator/counter path sends
unaligned width-8 reads through generic MemAlign, while `PureSpec.ld`'s Sail
equivalence is the aligned-success case. The sound route target is therefore
not “no generic MemAlign for LD”; it is either an aligned direct-Mem provider
coverage theorem that uses the Sail alignment assumption, or a provider
uniqueness theorem showing the balanced provider is the concrete Mem provider
row already carried by the `OpEnvelope.ld` constructor. The existing
provider-row public memory boundary is compatible with that second path and
already lowers selected envelope Mem rows to provider-row coverage.

The latest table-parametric provider-cursor split adds
`OpEnvelope.AcceptedFullExecutionMemoryProviderTableCursorSourceAtEnvelope` and
`acceptedAirMainMemFullTraceConstructionAtEnvelope_of_providerTableCursorSource`.
This keeps the concrete FullEnsemble Mem table found by channel balance instead
of coercing selected provider coverage through the witness-selected Mem table.
The compliance wrapper
`zisk_riscv_compliant_program_bus_of_fullExecutionMemoryProviderTableCursorSource`
then lowers that route-friendly cursor source directly to the accepted
AIR/Main/Mem trace construction consumed by replay. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`,
`trust/scripts/regenerate.sh`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
slice. The next step is to construct this table-parametric cursor source for
aligned direct `LD`: route balance supplies selected provider-row coverage in
the concrete Mem table, while accepted replay still has to supply the selected
prefix cursor for the same table.

The current direct-`LD` join-point slice narrows that construction target before
trying to solve it globally. `DirectLoadMutableMemProviderCursorAtEnvelope`
packages selected provider-row replay and selected prefix-state equality for
the same concrete FullEnsemble Mem provider table; `directLoadMutableMemProviderCursorAtEnvelope_of_replay`
adds a table-indexed prefix-state obligation to existing provider-row replay
coverage; and
`directLoadAcceptedFullExecutionMemoryProviderTableCursorSourceAtEnvelope_of_mutableProviderCursor`
lowers that Prop-valued cursor predicate into direct-`LD` cursor source
evidence. This deliberately does not claim all-load source construction:
subword loads still need their MemAlign-to-Mem route chain, and the current
slice passes focused `lake build ZiskFv.Compliance.OpEnvelope`,
`lake build ZiskFv.Compliance`, full `lake build`, trust regeneration,
both trust check scripts, and `nix run .#test`.

The route-plus-prefix composition slice adds
`directLoadMutableMemProviderCursorAtEnvelope_of_active_route_and_prefix` and
`directLoadAcceptedFullExecutionMemoryProviderTableCursorSourceAtEnvelope_of_active_route_and_prefix`.
These theorems compose active direct-`LD` route coverage, Main `b` source
facts, generic-MemAlign exclusion, `MainMemBusMultiplicitySound`, all-table Mem
read/replay embeddings, and a table-indexed selected prefix-state theorem into
the direct-only table-parametric source boundary. The important remaining
obligation is still visible rather than laundered: accepted replay must prove
the prefix-state predicate for the exact concrete Mem provider table selected
by route balance. Focused `lake build ZiskFv.Compliance.OpEnvelope
ZiskFv.Compliance`, full `lake build`, trust regeneration, both trust check
scripts, and `nix run .#test` pass for this slice.

The aligned-route split adds
`OpEnvelope.DirectLoadAlignedMutableMemProviderRouteAtEnvelope` as the positive
direct-Mem boundary for direct `LD`, rather than requiring callers to prove that
generic MemAlign is impossible for every width-8 load. The wrapper
`directLoadAcceptedFullExecutionMemoryProviderTableCursorSourceAtEnvelope_of_alignedRoute_and_prefixCursor`
derives table-parametric provider cursor source evidence from that positive
route plus same-table selected prefix cursors, so aligned direct-Mem coverage
can bypass the over-broad generic-MemAlign exclusion target. Focused `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust check scripts, and `nix run .#test` pass for this
slice.

The current source-multiplicity split adds
`ZiskFv.AirsClean.FullEnsemble.MainMemBusSourceMultiplicitySound`, a row-local
full-ensemble predicate saying each unified-Main `a`, `b`, and `store`
memory-source selector sum evaluates to `1` or `0`. The theorem
`mainMemBusMultiplicitySound_of_sourceMultiplicitySound` derives the coarser
`MainMemBusMultiplicitySound` from that row-local source predicate, and the
direct-`LD` generic-MemAlign route helpers now expose the source-multiplicity
predicate instead of the coarser pull-or-zero invariant. This is a real split,
not final closure: accepted full execution still has to prove the source sums
from ROM/source legality for every unified-Main row. Focused `lake build
ZiskFv.AirsClean.FullEnsemble.Balance` and `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, both trust check scripts, and `nix run .#test` pass for this
slice.

The ROM/source-legality split projects the ROM lookup carried by unified-Main
row constraints to exact program-ROM membership using Clean table soundness, via
`ZiskFv.AirsClean.Main.romSpec_of_mainWithRomAndMemBus_constraints`,
`romSpec_of_mainWithRomMemAndOpBus_constraints`, and
`romSpec_of_componentWithRomMemAndOpBus_constraints`. `Balance.lean` now exposes
`MainProgramRomSourceMultiplicitySound`, then proves
`mainMemBusSourceMultiplicitySound_of_constraints_and_programRomSourceMultiplicitySound`
from `witness.Constraints` plus that program-ROM source-legality predicate.
`OpEnvelope` has direct-`LD` compatibility adapters that consume this lower
burden for the generic-MemAlign route, mutable-route, mutable cursor, and
table-parametric provider cursor-source constructions. Focused `lake build
ZiskFv.AirsClean.Main.Circuit`, `lake build
ZiskFv.AirsClean.FullEnsemble.Balance`, and `lake build
ZiskFv.Compliance.OpEnvelope ZiskFv.Compliance`, full `lake build`, trust
regeneration, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this slice.

Historical checkpoint after the split provider construction bridge:
`OpEnvelope.acceptedFullExecutionMemoryProviderSplitTraceConstructionAtEnvelope_of_rowSplitExtractionSelection`
turns the named shared split row extraction plus extraction-indexed provider
selection into the split provider construction package. This is a boundary
alignment step only: the selected prefix and selected provider row still come
from the per-envelope selection, and the shared accepted split trace still comes
from the shared extraction object. Focused `lake build
ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`, full
`lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
bridge.

Historical constructor checkpoint:
`AcceptedFullExecutionMemoryRowSplitExtraction.ofAcceptedAirMainMemTrace`
packages a split accepted AIR/Main/Mem trace plus the mutable-Mem read/replay
embedding predicates into the named shared row-split extraction target. This
does not discharge the global obligations; it isolates the next proof target
into three ingredients accepted full execution must provide. Focused `lake
build ZiskFv.Compliance.OpEnvelope`, focused `lake build ZiskFv.Compliance`,
full `lake build`, `trust/scripts/check-all.sh`,
`trust/scripts/check-all-semantic.sh`, and `nix run .#test` pass for this
constructor.
