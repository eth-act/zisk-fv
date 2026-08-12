# Trusted Base

This is the narrative source of truth for zisk-fv's current trust boundary.
The generated machine ledgers live under [`generated/`](generated/).

## Claim

The intended soundness claim is:

> Assuming the Sail-to-Lean extraction and ZisK RV64IM circuit-to-Lean
> extraction are trusted, every state transition accepted by the modeled ZisK
> RV64IM circuits is a valid RISC-V state transition.

The advertised Lean endpoint is:

```text
ZiskFv.Compliance.root_soundness
```

`ZiskFv.Compliance.zisk_riscv_compliant_program_bus` is the **internal**
per-arm channel-balance lemma that `root_soundness` consumes; it is audited
alongside the endpoint but is not the claim. The statement and full axiom
closure of `root_soundness`, and of the two completeness endpoints, are
additionally frozen *in-build* by `ZiskFv/Audit.lean`: the script gates below
need oleans and a separate run, whereas those golden tests fail during
`lake build` itself. `zisk_riscv_compliant_program_bus` is not pinned there —
it is covered by the script gates only.

Current generated counts:

| Surface                                                                | Count | Ledger                                                                                             |
| ---                                                                    | ---:  | ---                                                                                                |
| Source Lean trust declarations                                         | 0     | [`generated/baseline-axioms.txt`](generated/baseline-axioms.txt)                                   |
| Transitive project-axiom closure of `root_soundness`                   | 0     | [`generated/baseline-strong-export-closure.txt`](generated/baseline-strong-export-closure.txt)     |
| Transitive project-axiom closure of `zisk_riscv_compliant_program_bus` | 0     | [`generated/baseline-zisk-riscv-compliant.txt`](generated/baseline-zisk-riscv-compliant.txt)       |

The source trust ledger currently contains no project axioms. Neither the
endpoint nor the internal global theorem has a transitive project-axiom closure.
The former Aeneas row-lowering and memory-state load bridge axioms are now
visible conditional inputs: `env.aeneasBridgeTrust` and
`env.memoryTimelineEvidence` on the internal global theorem.

The extraction assumptions are part of the project premise but outside the
Lean axiom ledger:

- Sail-to-Lean extraction for the official `riscv/sail-riscv` semantics.
- ZisK RV64IM circuit-to-Lean extraction from flake-pinned ZisK/PIL inputs.

## Current Classes

| Class                         | Declarations | In global closure | Removability                                                                                             |
| ---                           | ---:         | ---:              | ---                                                                                                      |
| Aeneas row-lowering condition | 0            | 0                 | Discharge `env.aeneasBridgeTrust` by importing generated Aeneas Lean into main Lake.                      |
| Sail memory timeline          | 0            | 0                 | Reduced to the memory-only `RowTraceCoherence` floor (#76 Fold-B; see below), unified on `root_soundness` into one named `BootSegmentMemorySeed` premise (#185), then restated **concretely** (#115) as `memInit`+`boot` (boot/cross-segment seed) + `step` (per-step execution-successor) + guarded direct-Mem read-soundness inputs. The direct-Mem path derives the order certificate from accepted Mem replay evidence when `MutableMemPresent witness` holds, scoped placement/classification, source/target chronology, the derived Main fixed-schema timestamp facts, and `ScopedDirectMemReplayLengthCertificate`; the no-memory path proves read-soundness over an empty execution-row list without a Mem bridge. The opaque cursor `stateAt`/`RowTraceCoherence` is derived by the execution-order fold (`Spike.rowTraceCoherence_of_uniformReplayMem`). The raw `readSound : MemoryBusRowsPrefixReadSound ...` seed field is gone; remaining carried content is boot/initial-memory plus named constructor/cardinality certificates, with MemAlign routed to #242. See below. |
| Clean completeness            | 0            | 0                 | Retired from source trust; false/circular fields are visible non-claims.                                  |


## Retired Row-Shape Bridge

The former RV64-to-ZisK hand-written row-shape axiom surface has been removed from the
active Lean trust ledger. The live opcode literals, lane helpers,
register-pointer decoding helper, and row/state helper structures live in
`ZiskFv/RowShape/Contract.lean`.

Canonical per-opcode theorem closures no longer mention any retired
row-shape bridge names. The route obligations that used to be hidden behind
that contract are now explicit caller/envelope facts or are derived from row
provenance and provider rows: static mode/control pins from provenance,
runtime source/data lanes from caller facts, and jump/PC facts from explicit
route obligations.

## Aeneas Row-Lowering Bridge

The production-backed Aeneas extraction is checked by the repository test path.
As of eth-act/zisk-fv#111 (PR #160), the generated Aeneas Lean **is** imported
into the main Lake proof (`ZiskFv.lean` → `ZiskFv/Compliance/AeneasBridgeTrust/Extraction/`),
and the per-opcode **static** decode/row-mode pins (`op` / `is_external_op` /
`m32` / `set_pc` / `store_pc`) are proven in-build, kernel-soundly (axioms
`{propext, Classical.choice, Quot.sound}`, no `native_decide`), from the real
lowerer (`trust/aeneas/ProductionM2.lean`). Those proven pins are **standalone**:
they are not yet wired to discharge `h_bridge`. Doing so requires binding the
committed circuit row to the lowering of the committed program word
(RomImageBinding, eth-act/zisk-fv#159) plus the dynamic per-arm conjuncts
(immediates / lanes / byte-chains). The generated Aeneas Lean still does not yet
derive every row-provenance, source-lane, immediate, PC, and link bridge fact
consumed by the compliance wrappers, so until that wiring lands the gap is still
represented by a visible global theorem hypothesis:

```text
h_bridge : env.aeneasBridgeTrust
```

The existing wrapper and `OpEnvelope` signatures still expose those fields
because the dispatch proofs pass them to the current wrapper layer. The wrapper
and canonical theorem signatures themselves are the inventory for the later
refactor that removes those parameters after generated Aeneas Lean supplies
proofs inside Lake (the generated caller-burden ledgers that previously tracked
this were retired with the anti-laundering metric — see "Active Caller Burden").

First proof-slice progress: the staged Aeneas harness now checks that
`extract_lui_from_inst` computes the LUI row-shape constants needed for
`MainRowProvenance.LuiRowMode`, and main Lake contains
`MainRowProvenance.luiRowMode_of_extracted_shape`, which states that those
constants discharge the `OpEnvelope.lui` row-mode field. Main Lake also
contains `OpEnvelope.luiOfExtractedShape` and
`OpEnvelope.aeneasBridgeTrust_luiOfExtractedShape`, which construct the LUI
envelope with the derived row-mode field and prove the LUI branch of this
bridge predicate. Generated Aeneas Lean remains staged under `build/`, so this
does not eliminate the remaining caller-burden bridge fields.

Second proof-slice progress: the same row-mode pattern now covers AUIPC. The
staged Aeneas harness checks the `extract_auipc_from_inst` row-shape constants,
and main Lake contains `MainRowProvenance.auipcRowMode_of_extracted_shape`,
`OpEnvelope.auipcOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_auipcOfExtractedShape`.

Third proof-slice progress: the same row-mode pattern now covers the JAL
rd-write route. The staged Aeneas harness checks the `extract_jal_from_inst`
row-shape constants, and main Lake contains
`MainRowProvenance.jalRowMode_of_extracted_shape`,
`OpEnvelope.jalOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_jalOfExtractedShape`.

Fourth proof-slice progress: JALR now has the matching final-row control-pin
slice. The staged Aeneas harness checks the `extract_jalr_from_inst` external
`OP_AND` and control-pin constants, and main Lake contains
`MainRowProvenance.jalrPins_of_extracted_shape`,
`MainRowProvenance.jalrControl_of_extracted_shape`,
`OpEnvelope.jalrOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_jalrOfExtractedShape`.

Fifth proof-slice progress: FENCE now has the matching activation/opcode pin
slice. The staged Aeneas harness checks the `extract_fence_from_inst` internal
`OP_FLAG` constants, and main Lake contains
`MainRowProvenance.fencePins_of_extracted_shape`,
`OpEnvelope.fenceOfExtractedShape`, and
`OpEnvelope.aeneasBridgeTrust_fenceOfExtractedShape`.

Sixth proof-slice progress: ADD, ADDI, and ADDW now cover the first Binary
provider-route pins. The staged Aeneas harness checks that regular ADD and ADDI
lower to external `OP_ADD` rows and ADDW lowers to an external `OP_ADD_W` row,
and main Lake contains `MainRowProvenance.addPins_of_extracted_shape`,
`MainRowProvenance.addwPins_of_extracted_shape`,
`OpEnvelope.addViaBinaryOfExtractedShape`,
`OpEnvelope.addiViaBinaryOfExtractedShape`,
`OpEnvelope.addwOfExtractedShape`, and the matching
`OpEnvelope.aeneasBridgeTrust_*OfExtractedShape` theorems. The provider-row
source-lane equalities are still explicit envelope fields.

Seventh proof-slice progress: SUB, SUBW, and ADDIW now cover the remaining
initial BinaryAdd/BinaryAddW provider-route shape. The staged Aeneas harness
checks the external `OP_SUB`, `OP_SUB_W`, and `OP_ADD_W` row-shape constants,
and main Lake contains `MainRowProvenance.subPins_of_extracted_shape`,
`MainRowProvenance.subwPins_of_extracted_shape`,
`OpEnvelope.subOfExtractedShape`, `OpEnvelope.subwOfExtractedShape`,
`OpEnvelope.addiwOfExtractedShape`, and the matching
`OpEnvelope.aeneasBridgeTrust_*OfExtractedShape` theorems.

Generated extraction and bridge manifest: the canonical production-backed
Aeneas extraction is tracked at
[`aeneas/ProductionM2.lean`](aeneas/ProductionM2.lean), and CI regenerates it
from the pinned inputs and fails on any non-zero diff. The maintained trust-gate
artifact [`aeneas-generated-bridge-manifest.txt`](aeneas-generated-bridge-manifest.txt)
is checked by `trust/scripts/check-aeneas-generated-bridge-manifest.sh` and by
`trust/scripts/check-all.sh`; it keeps the generated row-shape predicates and
Lean examples aligned with the generator template. Temporary generated LLBC and
harness modules such as `GeneratedChecks.lean` remain reproducible output under
`build/aeneas-production-extraction`.

Remaining path: export provider-row values, selected memory rows, and
full-ensemble same-message facts into the main proof boundary. Those artifacts
are needed to remove the remaining caller-burden bridge, row-shape, and
promise fields from wrapper and `OpEnvelope` boundaries. The `bus_shape`
category is already zero after the W-shift structural cleanup.

## Sail Memory Timeline

The former per-load byte-agreement promise has been replaced by a visible global
timeline-evidence hypothesis:

```text
h_memory_timeline : env.memoryTimelineEvidence
```

For load `OpEnvelope` arms, `env.memoryTimelineEvidence` requires
`Nonempty (MemoryTimelineEvidence state bus.e1)`; non-load arms require no
memory evidence. Generated full-witness sidecar artifacts can construct that
timeline evidence through `FullWitnessGeneratedTimelineEvidence`, while
dispatch consumes only the public `MemoryTimelineEvidence state e1` API before
reconstructing canonical `LoadPromises`. The `OpEnvelope` load constructors
themselves carry only `LoadStructuralPromises`, so they no longer accept a
per-load byte oracle.

`FullWitnessGeneratedTimelineEvidence` wraps `FullWitnessMemoryTimelineEvidence`
as a checked generated producer and makes the generated ProverData sidecar
source explicit: it carries
`FullWitnessMemAirSourceProverDataWitnessFacts` and records that the stored
sidecars are exactly the sidecars packaged from those witness facts. The inner
`FullWitnessMemoryTimelineEvidence` contains the concrete full-ensemble witness,
the `FullWitnessMemAirSourceRawSidecars` callback for the witness-selected
mutable Mem table, and only the residual Sail-memory timeline fact. A derived
Mem AIR source accessor selects the `FullWitnessMemReplayBridge`, which derives
the `AcceptedMemoryReplayEvidence` sub-object used by
`MemoryTimelineEvidence`, including prefix-read soundness for the accepted Mem
rows.

The accepted Mem table is sorted by address and step, not by execution time
(`zisk/state-machines/mem/pil/mem.pil` line 9: "Memory is sorted by address and
step"). The residual timeline boundary therefore does **not** claim whole Sail
state equality after replaying the accepted Mem-table prefix. It states only:
the accepted rows split around the selected read, the selected row is a read,
and the selected Sail state agrees with
`replayMemoryAfterBusRows acceptedReplay.initialMemory priorRows` on the
selected entry's eight byte lanes (`ReplayMemoryAgreementOnBytes ... entry.ptr.toNat`).
The canonical load proofs derive `LoadByteAgreement` from that byte-local
timeline evidence plus the circuit-side prefix-read agreement.

Generated/full-ensemble Mem facts target
`FullWitnessMemAirSourceProverDataWitnessFacts`: Clean assertion/lookup
witnesses plus named `witness.data` sidecar keys for raw split generated
constraints, row range facts, segment range facts, and the stage-2 source
columns for each mutable Mem table. The reproducible generated wrapper
`Extraction.MemGeneratedArtifact` exposes `buildWitnessFacts`, which assembles
that target from the three per-table callback families, plus
`buildRawFacts` and `buildWitnessFactsFromRawParts`, which assemble/adapt raw
ProverData fact callbacks to the same witness target. It also exposes
`buildTimelineEvidence`, which passes the assembled facts to
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`. The top-level
`nix run .#test` gate compiles the generated `Extraction.Circuit` shim,
`Extraction.Mem` constraint source, and
`Extraction.MemGeneratedArtifact` wrapper directly under the generated
`build/extraction` root. It also compiles
`Extraction.MemGeneratedConstraintBridge`, which binds those extracted Mem
constraints to the ProverData-backed source view used by the wrapper, so this
surface stays synchronized with the checked Lean API.
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts` packages that
target into a checked generated producer of the public timeline boundary. Lean
packages the resulting sidecar callback into the witness-selected
`FullWitnessMemAirSource` via
`fullWitnessMemAirSourceOfRawSidecars`, and
`fullWitnessMemoryTimelineEvidence_of_rawSidecars` combines it with only the
byte-local residual Sail timeline field above. `FullWitnessMemAirSourceRawFacts` and
`fullWitnessMemoryTimelineEvidence_of_rawFacts` remain compatibility adapters
for lower-level generated modules that still produce the raw sigma callback;
`fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts` is the checked
adapter for raw ProverData facts.

Retirement path: emit/prove the extractor/full-ensemble
`FullWitnessMemAirSourceProverDataWitnessFacts`, then prove the whole-execution
induction showing that, for each selected load, Sail memory at the selected
entry's eight bytes equals the last same-address accepted write in step order
(including the preload/first-read base case). The table/list-position part of
the bridge is named as `MemTableGeneratedRowsBridge`, which connects Clean
`table.table` positions to `rowAt mem idx` and the row-indexed
`generated_every_row` constraints. `FullWitnessMemReplayBridge` packages the
concrete full-ensemble Mem table, generated-row/range facts, active-row equality,
and nonempty segment evidence; its actual segment carries a derived
component-owned fixed-column fact (legacy compatibility constructors still use
`segmentWithFixedL1`). Its constructor derives the accepted replay
subobject, so `AcceptedMemoryReplayEvidence.prefixReadSound` is no longer a bare
global-boundary assumption. The semantic trust gate includes a
two-address witness with an addr-sorted/time-reversed prefix (write at byte
address 0 with later timestamp, selected read at byte address 8 with earlier
timestamp) so the old whole-state boundary shape cannot return silently.
Current #115 surface note: `AcceptedZiskTrace.mem_replay_table` is guarded by
`MutableMemPresent witness`, the objective fact that the concrete witness has a
mutable-Mem table with at least one row. Under that guard it separately selects
the concrete mutable-Mem table, witness membership, component identity, and
nonempty-table proof. Memory-less traces prove the guard impossible; they do not
fabricate an empty replay bridge. No generated Mem sidecar remains an
accepted-trace field: the S3 lifecycle audit found the former segment,
permutation, `gsum`, `im0`, and `im1` fields unconsumed outside their vacuous
constructor populations and deleted them. `mem_replay_constraints` is deleted:
its segment/permutation package is derived from the selected table's live constraints plus its
right-indexed transition, using canonical table `ProverData` and
component-owned fixed data. Row range facts are likewise derived from live Mem
`Table.fromStatic` lookups. `memReplayRows`/`memReplayBridge` construct the
canonical replay bridge directly, rather than rebuilding a raw sidecar or
`FullWitnessMemAirSource`. The former segment range field is deleted: its
canonical `MemSegmentGeneratedRangeFacts` are derived for the selected table
by `memReplaySegmentRanges`, from `constraints_hold`, `channels_balanced`, and
`transitions_hold` only. The chain is the generated `ValidatedLink` entries
for Mem range hints 884/886, `mem.pil:267-268` (with the companion source
bridge coverage at `mem.pil:285-286`), their linked c24–33 constraints at
`std_sum.pil:590/599/656/696`, the indexed transition's materialized
`ProverData` source cells, finished bus-103 balance, and the
`SpecifiedRangesSlice` static provider. `ProverAssumptions` is
completeness-only and is not consumed by this derivation.
`mem_replay_source_covers` remains the
matching structural source-correlation certificate: every mutable-Mem table in
the witness is the selected source table.

MemAlign provider route (#242): the former provider-side carve-out is closed.
`MemAlignLoadProviderRomValueFacts` and `MemAlignCoreLookupFacts` are retired:
a selected MemAlignByte/ReadByte provider carries its exact in-circuit
static-lookup byte range directly in the structural witness, while the
trace-local narrow-load boundary supplies the general provider's complete
selected-width value shape. The trace-local #1142 exclusion derives the
selected prove pins. Existing `MemAlignWitness` parameters remain consumer
interfaces, not detached whole-table lookup facts or new caller promises. The
remaining direct-Mem branch exclusions are
`LoadBDirectMutableMemResidues.no_marb`, `no_mab`, and `no_memAlign`.
The component-fidelity route is intrinsic: generated c29 plus c1/c3/.../c15
are MemAlign's D1 predicate, and c0/c2/.../c14 plus h998 are its D3 predicate;
the existing accepted-trace transition certificates check those
component-owned relations. The final provider bridge consumes those accepted
component facts and the two proof-triggered defect boundaries; it does not add
a parallel timeline assumption.

### Trace-coherence floor (`RowTraceCoherence`) — #76 Fold-B load reduction

> **#115 update (concrete seed form).** On `root_soundness` the whole-segment
> memory premise `BootSegmentMemorySeed`
> (`ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean`) no longer
> carries the opaque free cursor `stateAt` + whole-sequence
> `coherence : RowTraceCoherence stateAt [] rows` described below.  It now carries
> the **concrete** `memInit` + `boot` (boot/cross-segment seed) + `step` (per-step
> execution-successor) + guarded `readSoundInputs` (initial-memory equality and,
> on the direct-Mem closeout path, a derived `BootSegmentReplaySafeOrderCertificate`
> from scoped placement/classification, source/target chronology, and the named
> `ScopedDirectMemReplayLengthCertificate`) + a structural `placement` (each memory
> op's real bus row). The guarded path is keyed by `MutableMemPresent witness`,
> not instruction-count positivity; a separate no-memory theorem proves
> read-soundness over an empty execution-row list without `initialMemory_eq`.
> `memEvidence_of_bootSeed` *derives* the opaque `stateAt`/`RowTraceCoherence` per op via the execution-order fold
> (`Spike.exec_order_fold_fin` + `Spike.rowTraceCoherence_of_uniformReplayMem`).
> This is now a partial **trust reduction** for the old read-soundness half:
> table-order replay soundness comes from accepted Mem AIR replay evidence, and
> the seed carries only the explicit boot/initial-memory bridge, direct-Mem scoped
> placement/classification, and named row-count/order certificates. It is not free
> on the accepted-trace side: every memory-present `AcceptedZiskTrace` constructor must now supply the guarded
> Mem AIR source from which the replay bridge is derived, plus the structural
> certificate that every mutable-Mem table in the witness is that selected
> source table. The remaining direct-Mem carried content is constructor/cardinality
> class (`ScopedDirectMemReplayLengthCertificate`, owned for future derivation by
> #219), not read-value agreement. MemAlign-routed accesses are explicitly outside
> this closeout and are tracked by #242.
> It remains a constructibility
> restatement for the Sail execution-memory cursor itself:
> `rowTraceCoherence_of_uniformReplayMem` mechanizes only the reconstruction
> direction (`step`+`boot` ⟹ the uniform-replay cursor satisfies
> `RowTraceCoherence`; no converse), and the concrete `step` pins `binding.mem` at
> every index the opaque chain tied only at memory-op indices, so it is
> net-zero-to-marginally-*stronger* on trust (satisfied trivially by real traces).
> Its value is that the memory premise is now concrete, with no opaque `stateAt`
> existential, which is the seam the non-degenerate load instantiation (#221 → #74)
> needs. The `LoadMemoryTimelineCoherenceEvidence` *evidence type* below is
> unchanged — only how the seed supplies it changed.

The load-arm memory residual of the global theorem
`zisk_riscv_compliant_program_bus` has been reduced from a **whole-`SailState`**
identity to a **memory-map-only** trace-coherence floor.

* **Before (retired):** `LoadMemoryTimelineConstructionEvidence` carried
  `MemoryPrefixStateAlignment initialState state priorRows`, i.e.
  `state = stateAfterMemoryBusRows initialState priorRows` — a closed-form
  identity that pins **every** field of the load Sail `state` (regs,
  choiceState, mem, tags, cycleCount, sailOutput) to a replay of the prefix.
  This def is kept in `ZiskFv/Compliance/OpEnvelope.lean` marked **RETIRED**
  for the audit diff only; nothing in the live closure references it.
* **After (live):** `LoadMemoryTimelineCoherenceEvidence` carries an opaque
  cursor-indexed state assignment `stateAt`, the segment seed
  `stateAt [] = initialState`, the load-state pin `stateAt priorRows = state`,
  and the chain
  `RowTraceCoherence stateAt [] priorRows`
  (`ZiskFv/ZiskCircuit/MemTimeline/Spike.lean`). Each `RowTraceCoherence`
  conjunct constrains **only the `.mem` field** at one consumed prefix row:
  the row's memory transition takes any replay map agreeing with the current
  cursor's Sail memory to one agreeing with the next cursor's Sail memory
  (stores via `writeMemoryOfEntry`; reads / inactive / non-memory rows leave
  it unchanged). `regs` / PC / `cycleCount` / `tags` / `sailOutput` are
  **free**.

**Trust class.** `RowTraceCoherence` is the *trace-coherence* premise — at each
consumed prefix row the Sail state at the next execution cursor is the memory
transition of the Sail state at the current cursor. `ProgramBinding.stateAt`
carries no field for it, so it stands as **external trust, the same class as
channel-balance**: a per-step chaining fact about the execution timeline that
the row-local equivalence layer does not establish. It is dischargeable in
principle by the #100 whole-trace / execution-bus induction (which proves the
Sail successor relation across the trace). It is **not** an axiom — it is a
named binder carried on the load `OpEnvelope` residual and the load
`RowData_<op>` of the strong export; the global theorem's closure contains **no
new `ZiskFv.*` axiom** (kernel axioms only).

**What is DERIVED, not assumed.** The byte-local agreement the load consumer
actually needs — `stateBytesAtPrefix` of `MemoryTimelineEvidence`, i.e.
`ReplayMemoryAgreementOnBytes state (replayMemoryAfterBusRows … priorRows)
entry.ptr.toNat` — is **folded out** of the per-store steps via the store-driven
Fold-B (`replayAgreement_of_rowTraceCoherence` →
`stateBytesAtPrefix_of_rowTraceCoherence`), combined with the circuit-side
`prefixReadSound` (`memoryTraceAgreement_of_rowTraceCoherence`). The replay
engine only *transports* the seed agreement through the memory transitions; it
never manufactures agreement. See `loadMemoryTimelineEvidence_of_coherenceEvidence`
in `OpEnvelope.lean` for the live discharge bridge from the coherence residual
to the legacy `MemoryTimelineEvidence` API.

**Strict shrink (non-degeneracy proof).** The reduction is real, not a rename:
`RowTraceCoherence` never constrains `regs` / `cycleCount` / `choiceState` /
`sailOutput`, so it admits load states the old whole-state identity forbids.
`ZiskFv.ZiskCircuit.MemTimeline.Spike.witness_nondegenerate` exhibits a
store-then-read model whose load state's `regs` **and** `cycleCount` differ from
the initial state's, with the full selected-load `MemoryTraceAgreement` still
derived end-to-end (`witness_memoryTraceAgreement`) — impossible under the
frozen `MemoryPrefixStateAlignment` route. Both witnesses depend on kernel
axioms only.

**Scope note (stores).** The sub-doubleword store RMW byte residuals
(`h_m1..h_m7` of `RowData_sb/sh/sw`) are byte-local facts of the *same* class
and reduce by the *same* `memoryTraceAgreement_of_rowTraceCoherence` +
`byte_facts_of_event_agreement` machinery, but they are positional fields of the
`OpEnvelope.sb/sh/sw` **constructors** (not a keyed `@[reducible] def` consumed
only inside dispatchers, as the load residual is). Reducing them requires an
`OpEnvelope` inductive refactor of the store arms and re-derivation inside the
store cores, which touches the caller-burden / hypothesis-count baselines for
the store opcodes. They are therefore **deferred** to a follow-up; only the load
residual is reduced here.

### One named seed premise (`BootSegmentMemorySeed`) — #185 legibility MVP

The headline theorem `ZiskFv.Compliance.root_soundness` no longer carries the
memory-coherence residual as **ten scattered per-op fields**. Previously each of
the ten memory ops (seven loads carrying
`LoadMemoryTimelineCoherenceEvidence`, and `sb`/`sh`/`sw` carrying
`StoreRmwMemoryCoherenceEvidence`, after #119) was an `Inputs_<op>` field, each an
independent existential re-positing its *own* `initialState` / `rows` / `stateAt`
/ `RowTraceCoherence` chain — nothing forced the ten copies to describe the same
execution.

* **After (live, #115 concrete form):** `root_soundness` takes **one** binder
  `bootSeed : BootSegmentMemorySeed ziskTrace sailTrace ziskStep`
  (`ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean`). It bundles the
  **concrete** fields `memInit` + `boot` (boot / cross-segment seed memory),
  `step` (the per-step execution-successor: each Sail step's memory is the replay
  of that step's memory rows), guarded `readSoundInputs` (generic initial-memory
  bridge plus `BootSegmentReplaySafeOrderCertificate`; the direct-Mem closeout
  derives that order certificate from scoped source/target chronology and
  `ScopedDirectMemReplayLengthCertificate`), and a *structural* `placement`
  (each memory op's real bus row — a load's read `busLd .. .e1`, a narrow
  store's write `busSt .. .e2` + preserved bytes). `memEvidence_of_bootSeed` **derives** every
  op's per-op residual by the execution-order fold (`Spike.exec_order_fold_fin`
  gives the per-op state pin from `boot` + `step`;
  `Spike.exists_flatMap_range_split_of_singleton` locates the op's row;
  `loadEvidence_of_loadMemReplay` / `storeEvidence_of_loadMemReplay` build the
  evidence, re-choosing the opaque cursor `stateAt` as the uniform replay via
  `Spike.rowTraceCoherence_of_uniformReplayMem`). The ten `Inputs_<op>` memory
  fields are **removed**; the dispatcher threads the seed-derived
  `MemoryOpEvidenceFor` into each `stepStrong_<op>`. #115 replaced the earlier
  opaque `stateAt` / `RowTraceCoherence` seed fields with these concrete ones — a
  **constructibility restatement** (`rowTraceCoherence_of_uniformReplayMem`
  mechanizes only `step`+`boot` ⟹ coherence; the concrete `step` is
  net-zero-to-marginally-stronger, satisfied trivially by real traces), not a
  reduction for the Sail cursor part (see the #115 note under the floor section).

**Trust class.** Identical to the `RowTraceCoherence` trace-coherence floor
above — a named external-trust premise (the class of channel-balance), **not** an
axiom and **not** a defect. `root_soundness`'s `ZiskFv.*` axiom closure is
unchanged (empty — see `baseline-strong-export-closure.txt`); the public binder
still carries `bootSeed` (`baseline-strong-export-binders.txt`). The seed is
genuinely irreducible at the single-segment level (a segment does not contain its
own initial state — it is carried in from the previous segment / boot). The old
raw `readSound` field has been replaced by accepted Mem replay evidence plus
explicit initial-memory, scoped direct-Mem placement/classification, source/target
chronology, and named row-count/order certificates. This reduces the seed-side
read-value assumption, but it also adds a nonempty accepted-trace constructor
burden: `mem_replay_table` must select the concrete mutable Mem AIR table and
nonempty proof. The canonical segment range factor is derived from the
accepted constraint/balance/transition chain, never supplied by the accepted
trace. Generated constraints and row ranges are derived from the live Mem component rather than
supplied by the accepted trace; `mem_replay_source_covers` must certify
structural coverage of mutable-Mem tables by that selected table.
The direct-Mem row-count equality is visible as `ScopedDirectMemReplayLengthCertificate`
and belongs to the #219 whole-channel balance route for future derivation.
**#119** reduced the store byte facts to the
coherence shape.

**Memory, not memory+PC.** The coherence chain constrains only `.mem`; the seed's
`initialState` snapshot pins PC / registers only incidentally, and per-step
next-PC is discharged separately (the `AcceptedZiskTrace` PC-handshake
certificate, #100/#163). Naming it a *memory* seed keeps the premise from
promising more than the proof delivers.

**Non-vacuity (both halves).** The premise is inhabitable non-degenerately. The
load half is `ZiskFv.ZiskCircuit.MemTimeline.Spike.witness_memoryTraceAgreement`
(over empty seed memory). The store half — which the empty-memory Spike witness
cannot supply, since a narrow store's `StoreRmwPreservedBytesAtPrefix` floor is
false over empty memory — is `witnessStore_evidence`: a concrete
`StoreRmwMemoryCoherenceEvidence` whose preserved bytes come from a **non-empty**
seed memory. This is the store-side anti-laundering crux (the empty-memory floor
is genuinely false). Both depend on kernel axioms only. (The "not a frozen
whole-state floor" property is a property of the `LoadMemoryTimelineCoherenceEvidence`
*type* — it constrains only `.mem`, leaving regs / PC free — established under the
#76 floor section above; #115's concrete-seed evidence uses the uniform-replay
cursor, so the earlier `witnessStore_nondegenerate` regs/cycleCount side-claim was
dropped as describing a cursor the evidence no longer uses.)

### The PC premises (`SegmentPcChain` + `StepRowsAligned`) — #330

**Before (pre-#330).** `h_pc_bridge` was a field of **all 63** `Inputs_<op>`
structures: at every executed row, the caller asserted that the Main `pc` column
equals the Sail PC at that step. `root_soundness` took the whole family as
`inputsAgree : ∀ i, InputsAgree …`.

**Intermediate (Phase 5/6).** `inputsAgree` dropped to `InputsAgreeCore` (the same
63 structures minus that field) plus one `pcSeed : SegmentPcSeed` with `boot` and
`succ`. That was a restructuring only: `pcSeed_of_inputsAgree` proved the converse,
and `succ` still named `nextPcMux` — a committed ZisK column.

**After (live, Phase 7).** `root_soundness` takes
`inputsAgree : ∀ i, InputsAgreeCore …` plus **two** binders
(`ZiskFv/Compliance/TraceLevelExport/SailRetireChain.lean`):

* `pcChain : SegmentPcChain ziskTrace sailTrace ziskStep` — `boot` (the Sail PC
  agrees with the Main `pc` column at step `0`) and `retire` (the Sail state at
  `j + 1` takes its `PC` from what step `j` retired into `nextPC`);
* `rowsAligned : StepRowsAligned ziskTrace ziskStep …` — at every step with a
  successor, the step's execution-bus producer entry is its own Main row's
  successor `pc`.

`stepSound_of_programDecodes` is now a **strong induction on the step index**
rather than a per-`i` map. Row `0`'s PC agreement is `boot`; each later row comes
from the previous row's own `StepSound` via `pcBridge_succ_of_stepSound`. Three
facts make that step work, all proved, none assumed:

* `mainOfTable_pc_succ_eq_nextPcMux` — the circuit's own PC recurrence, from the
  `AcceptedZiskTrace.transitions_hold` certificate. Two side conditions are derived
  rather than assumed: `segment_l1 ≠ 1` away from row `0` (from the component-owned
  fixed `SEGMENT_L1 = [1,0,0,…]` schema) and the fixed-column capacity bound (from
  the table's own `fixed_domain` field).
* `nextPC_of_busEffect_ok` — if the channel effect succeeds, its post-state's
  `nextPC` **is** the producer entry's `pc`. Needs only the execution bus's shape.
* `stepChannelOutput_busEffect_ok` — the channel effect never faults.
  `MemBusMessage.toEntry` takes multiplicity and address space as explicit
  arguments and every bus passes numerals, so `bus_effect`'s "impossible under
  assumptions" error exits are unreachable.

**Trust class, stated precisely.** Named external-trust premises, the same class as
`bootSeed` and channel-balance — not axioms, not defects. `root_soundness`'s axiom
closure is unchanged; the new ZisK-side declarations close over
`[propext, Classical.choice, Quot.sound]`, and the ones that mention `StepSound`
close over the pre-existing Sail LHS set the endpoint already carried.

**This is still not a logical-strength reduction — say so plainly.**
`sailRetireChain_of_inputsAgree` proves the converse direction: the old per-row
bundle, plus `rowsAligned`, yields `retire`. Together with
`pcBridge_succ_of_stepSound` that makes the old bundle and `boot` + `retire`
**inter-derivable given `rowsAligned`**, the same situation Phase 5/6 was in. Do
not read this entry as a trust reduction.

What it does change, and why the change is worth having:

* **The per-step cross-machine burden is gone.** `boot` is now the only premise
  relating a committed ZisK column to a Sail register. `retire` mentions no
  `mainOfTable`, no `nextPcMux`, no `pc` column — it relates two Sail states
  through Sail's own step function. `rowsAligned` mentions no Sail state at all.
  A caller can discharge each by reasoning on one side only.
* **A hidden condition became visible.** `JalrLoweringRows` permits a two-row
  unaligned JALR lowering with `finish = start + 1`, and `StepSound`'s JALR arm is
  indexed by `finish`, so such a step writes `pc (j + 2)` into Sail's `nextPC`
  while step `j + 1`'s bridge is stated at `pc (j + 1)`. Assuming `succ` let a
  trace satisfy the PC equation while its Sail step had in fact retired elsewhere;
  nothing checked the two agreed. `rowsAligned` is that check, now on the record.
  It binds only at steps that have a successor, so a trailing unaligned JALR — the
  shape `jalrSpinRootSoundness` uses — discharges it vacuously.

**What would be a real strength reduction, and is not done.** `SailTrace` is a bare
`Fin n → SailState` (`ZiskFv/Compliance/SailTrace.lean`) with no chaining, so
*something* must say the Sail states form an execution — exactly the reason
`bootSeed` is irreducible at the single-segment level. Defining `SailTrace` as the
sequence Sail's own semantics generates from an initial state would make `retire`
definitional and leave `boot` alone. That is a change to a protected interface used
by all 63 arms, and it remains the open #330 follow-on.

**Non-vacuity.** All seven accepted-trace witnesses supply both binders and still
instantiate `root_soundness` / `stepSound_of_programDecodes`. They build `retire`
through `sailRetireChain_of_inputsAgree` from the per-row `InputsAgree` family they
already prove — no witness evaluates a Sail execution by hand. The
empty-execution memory witness and the degenerate probe get vacuous ones, as their
`bootSeed`s already are.

**Scope.** The PC arm only. The register fields (`h_a_*_t` / `h_b_*_t`, 116
occurrences) stay assumed; they go through the MemBus and are the separate
register-partition axis (`main.pil:277-279`, #169/#19).

### Register MemBus balance (`MEMORY_REG_OP`) — #225

The full RV64IM Clean ensemble now **emits** the complete register-consistency
MemBus traffic, so the register (`mem_op = 3`) partition balances for a real
instruction. All of it is derived composed-table emissions — **no** new trust
premise, `axiom`, or `opaque`:

- **Interior** (per Main row): for `a`, `b`, and `store` register accesses Main
  emits both the previous-access push-prev (`MEMORY_REG_OP`) and the current
  pull (`Main/Constraints.lean`; PIL `main.pil:277…328`).
- **Boundary** (chain-closing): a new single-purpose provider component
  `ZiskFv.AirsClean.RegisterBoundary.component` emits, per tracked register, the
  boot pull (`global_init_mem`, `mem.pil:507-508` + per-register call site
  `main.pil:535-537`; `mem_op=3`, ts 0, value 0, mult `-1`) and the reload push
  (`reg_pre_load` "Proves the last access.", `main.pil:450`; ts = last access,
  mult `+1`). It is a real `addTable`-composed provider in
  `fullRv64imSoundEnsemble` (`AirsClean/FullEnsemble.lean`) with
  `Assumptions := True` and no algebraic constraints — a deliberately
  under-constrained boundary provider, which is sound in the soundness direction
  (an under-constrained provider never makes `root_soundness` vacuous; the
  anti-laundering hazard, an overstrong validator, runs the other way).

The checked artifact
`ZiskFv.Compliance.RegisterMemBusBalance.addX1X1X1_registerMemBus_balanced`
proves `BalancedInteractions` of the register (`mem_op=3`) partition for the
minimal no-prelude real-register witness `add x1,x1,x1`, built from the **real
component emission definitions** (`aRegPreMessage`/`aMemMessage`/… and
`bootMessage`/`reloadMessage`) instantiated at a concrete `add x1,x1,x1`
`MainRowWithRom` — not hand-authored literals. The telescoping content is the
four consistency equalities (`aRegPre = boot`, `aMem = bRegPre`, `bMem = cRegPre`,
`cMem = reload`) plus the idle registers' self-balancing boot/reload pairs. The
semantic trust gate discovers the wrapper
`trust/consistency/register_mem_bus_add_x1_x1_x1.lean`; its axiom closure is
kernel-only (`propext`, `Classical.choice`, `Quot.sound`) and adds no project
axioms.

The messages are the real emission *definitions*, but the interaction
multiplicities are the emissions' `±1` selector values pinned at this row
(`pushedValue` / `pulledValue`), **not yet evaluated from the components'
`interactionsWith` lists** — so this artifact would not track a change to an
emission's multiplicity in `Main/Constraints.lean`. Deriving the interaction list
(messages and multiplicities) via a `mainSingleRowTable_interactionsWith_memBus`
reduction — the memBus analogue of #234's `mainSingleRowTable_interactionsWith_opBus`,
which #234 explicitly deferred — is the #219 follow-up.

**Scope / residuals (register-partition close).** This delivers the `mem_op=3`
partition `BalancedInteractions` — the object #219 consumes — not the whole-channel
`witness.BalancedChannels` or a constraint-satisfying accepted trace, which stay
**#219**. The balance is conditional on the previous-step timestamp chain
(`a_reg_prev_mem_step = 0`, `b_reg_prev_mem_step = 1`, `store_reg_prev_mem_step = 2`,
reload at `3`), pinned in the concrete row here; deriving it from ZisK's
ordering/range checks is the **#169/#19** range-fidelity axis.

**Update (#342, bus 102).** Half of that axis is now delivered. `main.pil:333-335`'s
three 24-bit register-step range checks are modelled as the `RegisterStepRangeChannel`
(bus 102) with a real `Guarantees`, provided by `RegisterStepRangeSlice` and consumed by
Main; balance turns a Main register pull into the provider's `rangeTable24.Spec` on
`<slot>_mem_step - <slot>_reg_prev_mem_step - 1`. So `a_reg_prev_mem_step` is no longer a
free witness column. `main.pil:447`'s reload-timestamp check remains **unmodelled**: the
`RegisterBoundary` reload timestamp is still free, and
`registerBoundary_table_interactionsWith_registerStepRange_nil` currently *proves* that
component silent on bus 102 — so modelling 447 later will require revisiting that lemma
and the provider case split in `exists_registerStepRange_provider_of_pull`.

**Update (#342, the walk).** The descent is now *consumed*, in
`ZiskFv/Compliance/RegisterWalk.lean`.
`registerRead_supplied_by_boundary_or_strictly_later_row` says a Main register read on an
accepted trace is supplied either by the `RegisterBoundary` or by a Main row whose own
register access sits at a **strictly later** memory-bus timestamp. Every premise is
discharged from `AcceptedZiskTrace`: the branch split from `channels_balanced`, the
supplying row's slot activity from its counterpart multiplicity plus Main's selector
booleanity, the descent from the bus-102 slice, and the no-wrap bound from the Main
table's own fixed-column capacity (`mainFixedCapacity = 2^22`) rather than from a
segment-length assumption. Consequently the supply relation is acyclic
(`regSupplies_chain_timestamps_nodup_of_trace`), which is what excludes the disjoint
register cycle #342 exhibits. The relation is slot-indexed on both sides, so mixed-slot
cycles are excluded too. The chain result is stated over `IsActiveWitnessMainRow` — every Main
row of the witness, not just the executed prefix — because a provider may be a padding row past
that prefix, and its no-wrap bound comes from the same fixed-column capacity. V2 check 19 keeps
the axiom closure visible
(`trust/consistency/register_walk_acyclic.lean`); it is kernel-only and adds no project
axioms.

The relation is **not vacuous**: `addX1Row_walk_isChain` exhibits it on the `add x1,x1,x1`
witness row, whose three slots read at timestamps `1`, `2`, `3` and whose bus-102
distances are the `[0, 0, 0]` that `singleAddWitness`'s provider list records. Every
result in `RegisterWalk.lean` is an implication out of `RegSupplies`, so an empty relation
would make them hold without saying anything about ZisK.

**What this still does not give.** Acyclicity bounds the walk from below, not above. Nothing yet
forces a register chain to *reach* `RegisterBoundary.bootMessage`, for two separate reasons.
First, the `main.pil:447` gap above is unchanged, so the boundary can still self-pair at
timestamp `0`. Second, iterating the supply step needs the supplying row's own access to be a
`mem_op = 3` **pull**, i.e. `a_src_mem + a_src_reg = 1`, because `exists_push_of_pull` fires only
at multiplicity exactly `-1`. Main's constraints give **booleanity only**
(`Main/Constraints.lean:252,259`); no exclusivity constraint exists in the component, so `(1, 1)`
is admissible in the model and the pull would ride at `-2` with `mem_op = 4`. Ruling that out means
pinning `rom_flags` to a decoded instruction — the committed-program decode bridge (#172, on top of
#164's proven decoder), a different axis from this range slice.
This slice does **not** claim register/memory access-ordering soundness. The
cross-segment continuation terms (`MAIN_CONTINUATION_ID` block and
`main.pil:454`'s `sel:(1-main_last_segment)` continuation pull) are out of scope
(#103/#76).

## Platform Profile

There are no project axioms for the current platform profile. PMP, PMA,
CLINT, and Zicfilp branches are discharged by ordinary Lean theorems in
`ZiskFv/SailSpec/Auxiliaries.lean`, using the global RISC-V profile
hypotheses carried by opcode proofs: machine mode, PMP disabled by the Sail
configuration, one ZisK physical-memory PMA region, aligned accesses, no HTIF,
C disabled in `misa`, and `mseccfg` readability.

These facts still define the verification target, but they are no longer in
the trusted axiom ledger.

## Clean Completeness

Clean component completeness placeholders have been retired from the source
trust ledger. The false or circular Clean completeness fields now set
`ProverAssumptions := False` and prove the field by ex falso, making the
mandatory Clean field a visible non-claim rather than trusted constructibility.
The push-only BinaryExtension base circuit remains honestly trivial and
axiom-free.

The Clean integration gate still keeps this boundary explicit: any future
`ZiskFv.AirsClean.*circuit_completeness` axiom must not enter the global
compliance theorem's project-axiom closure.

## ArithTable And DIV/REM Audit Conclusions

The opcode-shaped ArithTable axiom family has been retired from the active
trust shape. `generated/baseline-arith-table-op-axioms.txt` remains as a
guardrail so new `arith_table_op_*` trust facts cannot be added silently.

Active conclusions:

- True finite-table projections are now derived from row-native
  `ArithTableSpec` witnesses rather than trusted as opcode-shaped facts.
- False static claims such as unconditional W-mode `sext = 0` or static
  `np_xor` cannot be reintroduced; they must be replaced by dynamic proofs or
  explicit defect gates.
- `DIVU`, `REMU`, `DIVUW`, and `REMUW` are retired from the broad dynamic
  witness defect by deriving unsigned range, W high-chunk, nonzero-divisor,
  quotient high-zero, and remainder-bound facts from Clean ArithDiv/Binary
  evidence plus the unsigned Euclidean identity.
- Signed full-64 `DIV` and `REM` are now **narrowed and non-vacuously proved**:
  the `Defects.ArithDivDynamicWitnessShape` `.div`/`.rem` exclusion is the EXACT
  `op2 ≠ 0 ∧ |r| = |op2|` false-positive shape (`op2.toInt ≠ 0 ∧
  (signedRemainderInt v r_a).natAbs = op2.toInt.natAbs`), not the opcode-wide
  `True` — narrowed to the nonzero-divisor path so the divisor-zero branch is
  discharged separately (see the #114 bullet below). The canonical `equiv_DIV` /
  `equiv_REM` are real (no `False.elim`). For `DIV`, the accepted-trace route
  selects the completed physical Arith row and derives its constraints, ranges,
  sign classification, and conditional WEAK signed remainder bound internally;
  `h_r_le`, `h_nr_pin`, and `h_r_sign` are no longer caller residuals. The
  genuine Sail-to-row operand bridges remain. The narrowed-defect exclusion
  upgrades the derived weak bound to the STRICT `|r| < |op2|` fact used by the
  quotient proof. The existing `REM` caller surface is unchanged by this work.
  Anti-vacuity is gate-checked by
  `Defects.honest_{div,rem}_witness_not_forge`. 0 `ZiskFv.*` axioms (the
  per-theorem `collectAxioms` closure is unchanged).
- Signed W-mode `DIVW` and `REMW` are now **narrowed and non-vacuously proved**
  (2026-06-20): the `Defects.ArithDivDynamicWitnessShape` `.divw`/`.remw`
  exclusion is the EXACT W false-positive shape on the nonzero-divisor path
  (`extractLsb op2 31 0 ≠ 0#32 ∧ (signedRemainderIntW v r_a).natAbs =
  (extractLsb op2 31 0).toInt.natAbs`), not the opcode-wide `True`. The missing mid-level W discharge infrastructure
  was built: `div_w_chain_witnesses` (the m32=1 W carry chain) +
  `h_rd_val_mdrs_{divw,remw}_chunked` (composing it with the existing low-level
  W bridges `abs_euclidean_to_signed_euclidean_div_rem_w`,
  `fgl_{div,rem}_w_signed_to_bv64`, `signed_t{div,mod}_unique`). The canonical
  `equiv_DIVW` / `equiv_REMW` are real (no `False.elim`); they carry the WEAK W
  bound `h_r_le : |r₃₂| ≤ |op2₃₂|` plus the W operand pins
  (`a_2=a_3=b_2=b_3=d_2=d_3=0`, `c_2=c_3=0`) / `h_nr_pin` / `h_r_sign` as caller
  residuals and DERIVE the STRICT `|r₃₂| < |op2₃₂|` from the narrowed-defect
  exclusion (`lt_of_le_of_ne`). Anti-vacuity is gate-checked by
  `Defects.honest_{divw,remw}_witness_not_forge`. 0 `ZiskFv.*` axioms (the
  per-theorem `collectAxioms` closure is unchanged).
- **Signed remainder-bound residual.** For full-64 `DIV`, the WEAK bound
  `|r| ≤ |op2|` is now derived from the completed Arith/Binary provider ensemble
  and the quotient proof is independent of the physical remainder-sign bit;
  neither `h_r_le` nor `h_r_sign` remains a caller hypothesis. `REM` and the
  W-mode arms retain their existing residual surfaces. The operand sign bridges are no longer blocked on
  indexed range-table extraction: #169 composes `RangeTables.arithRangeTable`
  into ArithDiv `IndexedRangeSpec` and adds row-local
  `ArithTableProjections.Div.na/nb_eq_msb{64,32}_of_{pos,neg}_indexed` lemmas.
  The public signed DIV/REM surfaces may still carry genuine cross-world bridge hypotheses
  until #151 wires those row-local indexed facts through provider accessors. The
  real ZisK ArithDiv circuit enforces the weak bound via the
  `LT_ABS_NP`/`LT_ABS_PN` byte-chain comparison (`arith.pil:274`), but the FV
  model's completed provider now exposes the weak comparison consequence for
  DIV; the `LT_ABS_NP` false positive
  (`ltAbsNpByteChain_falsePositive_eqAbs256`) remains exactly the narrowed
  `|r| = |op2|` defect exclusion that upgrades it to the strict bound Sail requires.
  Visible in the canonical/wrapper caller-burden ledgers; details in
  [`defects.md`](defects.md) (`ZISK-DEFECT-ARITH-DIV-DYNAMIC-WITNESS-SOUNDNESS`).
- **Divisor-zero / signed-overflow boundary discharge (DIV/DIVW/REM/REMW,
  #114, 2026-06-22).** The canonical theorems previously carried caller
  promises `h_op2_ne` (`op2 ≠ 0`) and `h_no_overflow` (¬`INT_MIN`/−1); both are
  now removed. The divisor-zero and signed-overflow branches are discharged
  in-model: `DIV`/`DIVW` consume the exposed ArithDiv boundary constraints
  `Airs.ArithDiv.div_boundary_constraints` — row-local div-by-zero/overflow
  flag machinery (forces divisor chunks `b = 0` / quotient `a = 0xffff` on
  div-by-zero, `b = −1` / dividend `c = INT_MIN` on overflow, plus the
  inverse-sum detector), faithful named-column mirrors of `arith.pil`
  constraints 0–30 now rendered by the uncurated `--skip-unsupported`
  extraction (65 defs, 0 stubs) — while `REM`/`REMW` derive the divisor-zero
  remainder from the carry-chain identity (`b = 0 ⟹ d = c`) plus chunk ranges.
  `ArithDivDynamicWitnessShape` is narrowed to the nonzero-divisor path
  accordingly. Net anti-laundering metric shrinks (8 `[bridge]` caller binders
  removed, 2 `[row]` `h_boundary` added; hypothesis-count 356 → 350);
  per-theorem `collectAxioms` closure still 0 `ZiskFv.*` axioms.
- Signed `MUL`, `MULH`, and `MULHSU` have their malicious-witness defect
  **narrowed** to the exact exceptional product-sign forge shape (`(na=1,nb=0,
  np=0)` / `(na=0,nb=1,np=0)`); the honest cases are proved non-vacuously
  (`equiv_MUL` / `equiv_MULH` / `equiv_MULHSU`, gate-checked by the
  `Defects.honest_{mul,mulh,mulhsu}_witness_not_malicious` anti-vacuity guards).
- **Signed-M sign public binders retired.** `equiv_MULH` and `equiv_MULHSU`
  no longer expose `h_sign_a` / `h_sign_b` caller hypotheses. The compliance
  wrappers derive the high-half operand sign facts from #169's indexed Arith
  range-table evidence (`RangeTables.arithRangeTable`, ArithMul/ArithDiv
  `IndexedRangeSpec`, and
  `ArithTableProjections.Mul.na/nb_eq_msb{64,32}_of_{pos,neg}_indexed`). The
  signed-M forge exclusion itself remains active; details in
  [`defects.md`](defects.md)
  (`ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS`).
- **MULH/MULHSU shared lookup route (S3 PR 3).** The balance-selected Arith
  provider is `componentWithArithTable`; its `FullSpec` supplies the carry
  chain, Arith-table membership, c46, 16-bit chunk facts, signed-carry facts,
  and indexed range facts to the additive `equiv_MULH_of_fullSpec` and
  `equiv_MULHSU_of_fullSpec` bridges. This is the permitted S1a in-component
  `Table.fromStatic` route because every looked-up value is a plain Arith row
  cell: `arithTable`, `arithRangeTable`, `rangeTable16`, and
  `signedCarryRangeTable` occur in `ArithMul/Constraints.lean`'s
  `mainWithArithTable`. The extracted Arith c49–c64 survey independently binds
  range hints on bus 330 and the table hint on bus 331; its generated
  `ValidatedLink`s cover c49–c60/c63. The provider selection itself is from
  finished operation-bus balance. c46 remains a separate F-only assertion cited to
  `arith.pil:262`, not a lookup or a challenge-mixed range route. No
  `ProverAssumptions` or per-opcode lookup/range caller premise is added; the
  legacy canonical `equiv_MULH`/`equiv_MULHSU` binders remain compatibility
  surfaces while the new constructions consume their shared facts from
  balance/provider soundness.
- **Binary c10 mixed lookup route (#268).** This is a cited application of
  the existing lookup/permutation protocol-soundness class, not a new trust
  kind. The final BinaryTable assumes tuple is the source lookup at
  `binary.pil:121-124`; its coupled Binary operation tuple occurs in the same
  accumulator constraint at `std_sum.pil:590`. The generated
  `Extraction.LookupWiring.link_Binary_10` records those two
  constraint-derived tuples under `derivedMixed2`, with `hints := []` to make
  the absent c10 hint provenance explicit; its exact structural identity is
  kernel-checked by `constraint_Binary_10 = template_Binary_10 := by rfl`.
  `AirsClean.Binary.c10Wiring.sourceBinding` separately checks that the
  bus-125 tuple is the live `lookupMessage7` model. Binary and
  BinaryExtension consumers emit negative messages only; their exact
  `BinaryTableSlice`/`BinaryExtensionTableSlice` providers and local finished
  bus-125/bus-124 ensembles carry table membership through balance. No
  consumer promise or soundness-side `ProverAssumptions` is introduced;
  provider `ProverAssumptions` is completeness-only.
- **MemAlign byte-assembly exact lookup wiring (#242).** This is a cited
  application of the existing lookup/permutation protocol-soundness class,
  not a new trust kind. The shared MemAlignByte PIL template emits the live
  byte-memory permutation at `mem_align_byte.pil:66-100`, the 16-bit/byte
  range and lookup facts at `:103-104`, and the direct padding updates at
  `:106-118`; MemAlignReadByte instantiates that same template through its
  Rust witness builder. The generated `ValidatedLink` entries kernel-check
  the normal byte links plus the exact zero-tail routes
  `MemAlignByte c9/c13` and `MemAlignReadByte c6/c7` at std_sum
  `:590/:656/:599/:656`, and their composed exact assumes-neg/zero-tail
  routes `MemAlignByte c14` and `MemAlignReadByte c8` at `:656`, each by
  `constraint = template := by rfl` with the real hints #1025/#1027,
  #1031/#1032, #1050, and #1054/#1055. The terminal std_sum constraints
  c15/c9 (`:696`) remain explicitly global finalizers, not lookup links.
  The selected byte-provider bridge consumes that exact component `Spec` to
  carry only its needed `< 256` fact into the structural load witness; no
  universal validator residue, caller promise, or soundness-side
  `ProverAssumptions` is introduced.
- **MemAlign virtual-ROM bus-133 route (#242).** This is a cited application
  of the existing lookup/permutation protocol-soundness class, not a new trust
  kind. `mem_align.pil:139-143` defines the unmasked h998 assumes tuple
  `[pc, pc' - pc, delta_addr, offset, width, flags]`; generated
  `link_MemAlign_36` kernel-checks its cluster-2 constraint/template identity
  with the real h996/h998 tuples, and `MemAlign.h998Wiring.sourceBinding`
  kernel-checks h998's actual slots against the live current/successor tuple
  (including the rotated witness slot). `MemAlign.Circuit` reads `pc'` from
  D3's intrinsic cyclic successor environment, including the
  final-row-to-row-zero instance. The consumer emits that exact negative tuple
  on finished bus 133. Balance selects a `MemAlignRomSlice` positive row, and
  the exact provider specification comes from the extracted fixed virtual table
  (`mem_align_rom.pil:6-313`, mirrored by `mem_align_sm.rs`). Thus membership
  is derived from constraints and balance, never promised by the consumer or a
  caller. The D3 premise is the separately documented verifier-checked
  accepted-trace certificate below; no soundness-side `ProverAssumptions` is
  used.
- **MemAlign register-byte bus-107 route (#242).** This is the same cited
  lookup/permutation protocol-soundness application, not a new trust kind.
  `mem_align.pil:113-118` emits one Range Check for each `reg[i]`; the real
  assumes hints #982/#984/#986/#988/#990/#992/#994/#996 are kernel-linked by
  `link_MemAlign_38` and the cluster links `link_MemAlign_33` through
  `link_MemAlign_36` (`constraint = template := by rfl`, at the corresponding
  `std_sum.pil:590/599/656` occurrences). `MemAlign.component` emits those
  exact eight negative one-slot bus-107 tuples. Finished balance selects only
  `MemAlignRangeSlice`, whose static `rangeTable8` lookup supplies exact
  membership. Consumer guarantees are `True`; no caller promise and no
  soundness-side `ProverAssumptions` is used. The provider's identical
  `ProverAssumptions` predicate is completeness-only.
- **MemAlign narrow-load value lanes (#242).** The through-MemAlign route uses
  the exact selected general-provider row reconstructed at
  `mem_align.pil:181-189`. For widths 1, 2, or 4, its reconstructed two-chunk
  value must fit the selected width: `value_1 = 0` plus `value_0 < 2^8` or
  `2^16` for widths 1 or 2. The trace-local
  `Defects.MemAlignNarrowLoadLaneForge` records exactly the negation of that
  complete selected-row shape (including the bridge's selected-width equality);
  `RowOutsideDefectRegion` excludes it only for LBU/LHU/LWU/LB/LH/LW. Its
  negation derives the complete value shape at the bridge point and deletes
  `MemAlignLoadProviderRomValueFacts`. This is a claim boundary, not a new
  trust kind, caller promise, or soundness-side `ProverAssumptions`; the source
  repro checks both a nonzero high chunk and `value_0 = 256` for width one in
  `trust/consistency/memalign_narrow_load_lane_defect.lean`, against the
  physical ROM tuple at `mem_align_rom.pil:6-313`.

The active defect boundaries and retirement criteria are in
[`defects.md`](defects.md).

Trace-level export note (updated 2026-07-28): `RowOutsideDefectRegion` for the strong
trace theorem is now stated over the accepted ZisK trace row, not over
`SailTrace` or `InputsAgree`. The signed-MUL and signed-DIV/REM defect gates
range over matching Arith witness rows from the operation bus, with DIV/REM
divisors reconstructed from witness chunks. Signed DIV now also excludes the
ordinary nonzero-quotient sign-forge predicate
`SignedDivQuotientSignForge`; its `div_overflow = 0` guard preserves the
architectural overflow row. The six narrow-load arms additionally negate the
selected-row `MemAlignNarrowLoadLaneForge`; the forge predicate ranges over
the accepted witness and the exact Main-selected memory-bus entry.

## Active Caller Burden

The live per-canonical-theorem trust footprint is the axiom-closure ledger:

- [`generated/baseline-equiv-axiom-deps.txt`](generated/baseline-equiv-axiom-deps.txt)

> **Retired (2026-06):** the generated anti-laundering ledgers
> (`baseline-hypothesis-count.txt`, `baseline-caller-burden.txt`,
> `baseline-wrapper-caller-burden.txt`) and the DEEP
> construction-binder baseline were removed once the discharge campaign
> concluded at 0 project axioms. They measured per-binder churn that no
> longer tracks a real trust change; the axiom-closure baselines above
> (plus `baseline-zisk-riscv-compliant.txt`) remain the mechanically
> gated audit surface. Promise discharge should still visibly reduce
> caller-supplied promise hypotheses, but this is now authoring/review
> guidance rather than a gated metric.

For historical context, at retirement the canonical ledger held 1100 binder
rows and the wrapper ledger 1135, with `bridge` (122) and `row_shape`
(18 canonical / 22 wrapper) the dominant remaining categories — documented as
generated or full-ensemble integration boundaries, not hidden global axioms.

## Accepted-Trace Certificates (non-axiom obligations on `AcceptedZiskTrace`)

These are **not** Lean axioms (none appears in `generated/baseline-axioms.txt`;
the per-theorem axiom closures are unchanged) and **not** derived from
`constraints_hold` + `channels_balanced` (so they are not folded into
`AcceptedZiskTrace.spec_holds`). They are explicit **structure fields** on
`AcceptedZiskTrace` — verifier-checked facts a real ZisK proof certifies about
the committed trace, but which the single-row Clean `Air.Flat` model cannot
itself express. Each is PIL-faithful and constructible (real ZisK traces satisfy
it). They are documented here precisely because they add to the accepted-trace
trust surface even though they add no axiom.

| Field (`Compliance/AcceptedZiskTrace.lean`) | PIL source | What it certifies |
|---|---|---|
| `main_height` (pre-existing) | — | the physical Main table has a row for every executed-step index; it may also carry padding rows |
| `transitions_hold` (**#100**, extended for **#242** and **#280**) | `main.pil:409-410`, `main.pil:386`; `mem_align.pil:116-117,142` | component-owned D1 predecessor/current relations hold: Main's PC handshake, Main's non-segment source-C copy (a row that sets none of `b_src_mem/imm/ind/reg` reads its `b[0]`/`b[1]` lanes from the predecessor row's `c[0]`/`c[1]`), and MemAlign's gated predecessor `delta_addr` plus eight `down_to_up` register continuities. These are verifier certificates, not caller assumptions. |
| `cyclic_successor_transitions_hold` (**#242**) | `mem_align.pil:113-118,139-143` | MemAlign's D3 cyclic successor/current relations hold on every effective row: h998's unmasked `DELTA_PC = pc' - pc` and eight `up_to_down` register continuities, including final-row-to-row-zero. Its bus-133 ROM membership is derived from finished balance/static provider. |
| `mem_replay_table` (**#115**, guarded by `MutableMemPresent witness`) | Full-ensemble table selection for the mutable Mem component | selects the concrete mutable-Mem table, proves witness membership and component identity, and proves the table is nonempty |
| Derived `memReplaySegmentRanges` (not an `AcceptedZiskTrace` field) | Mem hints 884/886; `mem.pil:267-268` / `285-286`; linked c24–33 at `std_sum.pil:590/599/656/696`; generated `ValidatedLink` entries | derives selected-table `MemSegmentGeneratedRangeFacts` from `constraints_hold`, `channels_balanced`, and `transitions_hold`: the indexed source bridge identifies the canonical `ProverData` chunks, finished bus-103 balance finds the `SpecifiedRangesSlice` provider, and its static table supplies 16-bit membership. `ProverAssumptions` is completeness-only and is not used. |
| `mem_replay_source_covers` (**#115**, guarded by `MutableMemPresent witness`) | Full-ensemble table/source correlation for the mutable Mem component | certifies that every mutable-Mem table in the accepted witness is the selected `mem_replay_table`; this is table identity only, not read-value agreement |

The Main `SEGMENT_L1 = [1,0,...]` (`main.pil:19`) and `main_step = row index`
(`main.pil:90`) facts, including the `2+4*i` / `3+4*i` no-wrap representatives,
are now derived from S2's canonical component-owned indexed fixed schema and its intrinsic
fixed-domain bound. They are not `AcceptedZiskTrace` fields and add no caller-supplied hypothesis.

**#115 constructor-burden note.** Removing the raw seed
`MemoryBusRowsPrefixReadSound` field moved real proof work into checked Mem
replay evidence, but the current branch also strengthens `AcceptedZiskTrace` for
memory-present traces. Constructors whose mutable-Mem table is empty, such as
the degenerate base case and #219/#220's ADD witnesses, prove
`MutableMemPresent` impossible instead of supplying replay fields. A constructor
with mutable-Mem rows must build the guarded `mem_replay_table` and
`mem_replay_source_covers`, in addition to
`constraints_hold`/`channels_balanced`/`transitions_hold`/
`cyclic_successor_transitions_hold`/`main_height`.
Generated constraints, row ranges, canonical segment range facts, and Main
fixed-column facts are derived from the live component. These fields are not
read-value agreement predicates, and they no
longer carry deterministic Mem fixed columns. The paired
`mem_replay_source_covers` field is a structural table-coverage certificate that
removes this residue from seed-layer wrappers. For the #115 direct-Mem closeout,
these fields plus `ScopedDirectMemReplayLengthCertificate` are the named
constructor/cardinality burdens; #219 owns deriving the row-count
certificate from whole-channel balance, and #242 owns the MemAlign-routed tail.

**#100 trust-surface change (honest accounting — a SHIFT, documented as such).**
The next-PC discharge does **not** derive `h_nextPC_matches` from the existing
`constraints_hold`. It **removes** the 63 per-opcode cross-world
`h_nextPC_matches` promises (each asserting *circuit next-PC = Sail next-PC*, the
worst, conclusion-adjacent class) and in their place adds:
- the accepted-trace `transitions_hold` certificate — declared on the Main
  component via `Air.Flat.Component.transition`, carried once for the whole
  trace — while the needed `SEGMENT_L1` fixed fact is derived from the canonical
  component-owned fixed schema; and
- per-opcode **decode pins** (`set_pc`/`jmp_offset…`, the sailTrace-free
  `rowDecode` bucket, dischargeable via #74) and the **PC-provenance bridge**
  (`h_pc_bridge`/`h_pc_bound`, the same class JAL/AUIPC already carried).

So a cross-world output promise is replaced by an in-circuit polynomial
certificate plus dischargeable decode + the existing provenance class, with the
per-op flag/target/cast content **proven** (0 new `ZiskFv.*` axioms). The Clean
`Air.Flat.Component.transition` field is *inert* (no Clean soundness theorem
consumes it — see `docs/clean-fork-divergences.md` D1); the obligation lives
entirely at the `AcceptedZiskTrace` layer, which is why it is in `main_height`'s
class rather than `constraints_hold`'s.

**#280 extension of the same certificate (JALR source-C) — a REDUCTION.**
`transitions_hold` now also carries Main's non-segment source-C copy
(`main.pil:386`, extracted as `constraint_4_every_row` /
`constraint_10_every_row`): `Main.transitionBetween` is
`pcHandshakeBetween ∧ sourceCCopyBetween`, and `sourceCCopyBetween` states
exactly the `(1 - SEGMENT_L1)`-gated *within-segment* equation. Clean's
transition interface has no public-input surface, so the segment-boundary case
(`SEGMENT_L1 = 1`, where the PIL selects the public `segment_previous_c` input)
is deliberately **not** modeled, and neither is the a-lane copy
(`main.pil:385`). The modeled relation is therefore *implied by* the PIL
constraint and never stronger than it.

This extension **reduces** caller trust rather than shifting it. The unaligned
JALR lowering (an `OP_ADD` row followed by the terminal `OP_AND` row) now reads
its ADD result out of the predecessor row through this certificate, which
retires the per-op premise `Inputs_jalr.h_operand_offset` — the cross-world sum
identity `b + offset_bv = rs1_val + signExtend imm`, which in the unaligned case
silently assumed the whole ADD computation — in favour of the narrower register
agreement `h_rs1_start : b = rs1_val`, the same input-agreement class every other
opcode already carries. The remaining lowering facts (`OP_ADD` pins, the
adjacency `start + 1 = finish`, the terminal row's `b_src_*` selectors) are
sailTrace-free decode/placement evidence in `JalrLoweringRows`, not new
cross-world promises.

Consequently `root_soundness`'s conclusion is now indexed by the checked decode
(`StepSound … zs (rowDecode_of_programDecode …)`): for JALR the state effect is
stated at the lowering's terminal row `decode.rows.finish` instead of at the
architectural index `i`. No binder is added — `programDecodes` was already a
`root_soundness` binder — and `JalrLoweringRows.architectural_start` pins
`start.val = i.val`; every other family still reads its effect at `i`.

The `root_soundness` entry point replaces the caller's 63
`ProgramDecode` bundles with a single exact `ProgramRowsBinding` and
per-instruction `RawProgramDecode` evidence. Each arm checks the raw RV64IM
shape, uses the Aeneas-extracted production lowerer, and constructs the same
committed-program decode consumed by `stepSound_of_programDecodes`; unaligned
JALR uses the binding's primary and successor rows. (This endpoint was
introduced as `root_soundness_rawProgram`; it now holds the `root_soundness`
name, and the theorem it calls — formerly `root_soundness` — is
`stepSound_of_programDecodes`. The project keeps exactly one theorem named
`root_soundness`, and it is the outermost node of the audit tree, so the
strong-export binder and closure gates retarget onto it by construction.)
This is a caller-trust reduction and does
not alter `AcceptedZiskTrace`, the semantic conclusion, the known-defect
boundary, or the project axiom closure.

Three boundaries remain explicit. First, the layout functions (`start` and
`addr`) are caller-supplied: their meaning is that architectural word `k` sits
at the binary/ROM location assigned to `k`; the binding proves exact,
gap-free lowered rows relative to that map, not that the map came from a
particular linker image. Second, grounding the same word in Sail's
`ext_decode` is #172 and is not claimed here. Third, identifying `rawProgram`
with the intended compiled binary remains the external compile/commitment
boundary.

**Non-vacuity of this endpoint IS witnessed (#320).** Two theorems in the tree
conclude `ProgramRowsBinding` and feed it to `root_soundness`:

* `addFaithfulProgramRowsBinding`
  (`TraceLevelExport/RawProgramBindingAddFaithfulNonvacuity.lean`), consumed by
  `addFaithfulPaddedRawRootSoundness` on a **one-instruction** execution together
  with real `addFaithfulRawProgramDecodes` — so the conclusion obtained there is
  not vacuous;
* `memoryProgramRowsBinding`, consumed by `memoryRawRootSoundness`, on an empty
  execution (real binding, vacuous `∀ i : Fin 0` conclusion).

The remaining instantiations (`addSpin`, `addAddiSpin`, `divSpin`, `jalrSpin`,
`sdLdSpin`) discharge the premises `root_soundness` shares with
`stepSound_of_programDecodes` — `ziskTrace`, `ziskStep`, `inputsAgree`, `pcSeed`,
`bootSeed`, `hAvoidKnownBugs` — but they satisfy `ProgramDecode` directly, and
`ProgramRowsBinding + RawProgramDecode ⟹ ProgramDecode` does not run in the
direction that would transfer that evidence.
So the clauses carrying the binding's weight (4-alignment, `addr + 1 <
GL_prime`, two-slot separation, and the surjectivity clause) and the two-row
JALR expansion path are currently unexercised, and no gate detects this:
`#print axioms` reports nothing about inhabitation.

Two extraction fidelity qualifications also remain visible. The Aeneas wrapper
passes `rom_address := 0#u64`; this is sound for the exported fields because
that value reaches only `paddr` and a discarded map key, but a production
change that makes it affect another serialized field requires revisiting the
proof. The Rust implementation has a
`#[cfg(feature = "aeneas_extract")]` extraction path, so equivalence of that
feature-selected path with the ordinary production build remains a reviewed
source/configuration boundary and is cross-checked by the focused real
`compute_trace_rom` test.

One extraction-boundary allowlist was widened for this endpoint:
`trust/scripts/check-aeneas-production-boundary.py` exempts
`extract_transpile_rv64im_rows_raw` from the "no public extraction helpers
outside the generated start surface" rule. It is the two-row sibling of the
already-exempt `extract_transpile_rv64im_raw` family and carries the same
reviewed status; it is recorded here because it is a widening of the extraction
surface rather than a proof step. Countervailing, `ZiskFv.Compliance.RawProgramBinding`
was added to `extractionNamespaces` in `bin/TrustGate/Main.lean`, putting the new
module under the raw-closure regression gate.

**Within-segment boundary (explicit).** `mainTransition_to_next_pc`
(`Compliance/MainTransition.lean`) requires `i + 1 < mainTable.table.length` — a
*physical Main-row successor* must exist — surfaced as the per-opcode `h_idx`.
`main_height` only gives a row for each executed step, so the final executed step
needs an additional physical Main row. This condition is separate from committed
ROM length: Main's in-circuit lookup ranges over the full `programLength`, while
the Sail trace and `root_soundness` range over executed steps. The #245 regression
has one executed ADD step, a two-entry committed ADD/JAL ROM, and a faithful JAL
lookup at the physical successor row. When no within-segment successor exists,
the final next-PC is the cross-segment continuation (`main.pil:501-529`), which is
**out of #100 scope = #103**. This is an applicability boundary, not an
unsoundness: where `h_idx` holds the discharge is exact; where it does not, the
final-row next-PC is a named #103 residual.

## Not In This Ledger

The trust ledger does not enumerate the Lean kernel, mathlib,
LeanZKCircuit, the Sail-to-Lean compiler output, or flake-pinned upstream
inputs. Their audit surface is the Lake/Nix configuration and `flake.lock`,
not `generated/baseline-axioms.txt`.

The build pins the immutable
`codygunton/clean@bf5e40ed455613687385e8828cba68b2a438b992` source input
(branch `port-zero-mult-gating`, Lean 4.28.0), rebased onto upstream PR #398.
It provides D1's all-row predecessor/current transition contract, D2's
canonical component-owned indexed fixed-column materialization, and D3's
intrinsic cyclic current/successor transition surface. D1 remains inert to
Clean's existing soundness theorem, so project-side accepted traces explicitly
carry `transitions_hold`; D2 is consumed by canonical table materialization,
constraints, interactions, transitions, and projections. D3 is consumed by
the #242 MemAlign h998/register-continuity/bus-133 derivation: its cyclic relation is carried as
the verifier-checked `cyclic_successor_transitions_hold` accepted-trace
certificate, never by a caller assumption. The structural fixed-domain/no-wrap
bound and cyclic successor indexing belong to `Air.Flat.Table`, not to a
caller-supplied promise hypothesis.

The `bf5e40ed` repoint additionally brings upstream's `Channel.pulledIf` /
`pushedIf` and its `Requirements` obligation gated on `mult ≠ 0`. That closes
the Clean-side limitation recorded as #337: previously `Requirements` fired at
every `mult ≠ -1`, including `0`, so a selector-gated push owed a guarantee
about unconstrained witness values. This is a build-input change, not an
accepted-trace fact; it *weakens* the obligation the project must discharge,
which is upstream's choice and is why the affected proof sites now close with
`intro _; simp [<Channel>]` rather than `intro _; trivial`.

**Be precise about what the weakening costs.** It weakens a stated *obligation*,
not a derivable *conclusion*. Clean transfers a requirement to a guarantee at
`Clean/Air/Balance.lean:206`, and applies that step only to the counterpart
produced by `exists_push_of_pull`, which concludes `b.mult ≠ 0 ∧ b.mult ≠ -1`
(`Balance.lean:155-156`). Both the old and the new definition agree on that
range. The case the new definition drops, `mult = 0`, is therefore never
consumed, so nothing derivable from the stronger form is lost.

The second half of that sentence used to read "every channel we declare sets
`Guarantees := True`, which makes both forms trivial". That was already inaccurate when
written — bus-103 `SpecifiedRangesSliceChannel` carries `rangeTable16.Spec` — and #342
adds a second non-trivial one, `RegisterStepRangeChannel` with
`rangeId = 102 ∧ rangeTable24.Spec value`. The gating argument above does not depend on
`Guarantees` being trivial; it depends only on where Clean consumes `Requirements`.

Two caveats a later reader must not lose:

* **That argument is human-made, not machine-checked.** It comes from reading
  `Balance.lean`, not from a Lean theorem. No gate enforces "our `Requirements`
  are only consumed via `exists_push_of_pull`". Writing one was considered and
  declined: the machinery costs more than the risk, given the `Guarantees :=
  True` situation above.
* **It is contingent on upstream.** If a later Clean revision consumes
  `Requirements` at `mult = 0`, the weaker form starts to matter and this
  paragraph stops being true. Re-read it on the next `clean-src` bump.

The gating first becomes load-bearing in #342, which gives a channel a
non-trivial `Guarantees` for the first time: Main's three bus-102 emissions then
produce obligations of exactly the gated shape
`¬(sel = 1) → ¬(sel = 0) → Guarantees …`, vacuous under selector booleanity.
Without the gating those would be range obligations Main cannot discharge.
