# Memory Argument Obligation Map

This map records how P3 discharges the `env.memoryTimelineEvidence` promise
hypothesis on `ZiskFv.Compliance.zisk_riscv_compliant_program_bus`. The current
global theorem takes `h_bridge : env.aeneasBridgeTrust`,
`h_memory_timeline : env.memoryTimelineEvidence`, and
`h_known_bugs : Defects.NoKnownDefect env`
(`ZiskFv/Compliance.lean:94-98`); the timeline hypothesis is passed only to the
load-bearing dispatchers at `ZiskFv/Compliance.lean:109,111,112`.

`OpEnvelope.memoryTimelineEvidence` is reducible and is nontrivial only for the
seven load routes: `ld`, `lbu`, `lhu`, `lwu`, `lb_via_static_match`,
`lh_via_static_match`, and `lw_via_static_match`
(`ZiskFv/Compliance/OpEnvelope.lean:2234`). Each load route currently requires
`Nonempty (ZiskFv.ZiskCircuit.MemTrace.MemoryTimelineEvidence state bus.e1)`;
non-load routes require only `True`.

## Field Verdict

| `MemoryTimelineEvidence` field | Current provenance | Derivable from | Discharge PR |
| --- | --- | --- | --- |
| `acceptedReplay` | Packed inside the caller-supplied `Nonempty` evidence. `AcceptedMemoryReplayEvidence` stores `rows`, `initialMemory`, and `prefixReadSound` (`ZiskFv/ZiskCircuit/MemTrace.lean:1266-1269`). | Bucket (b): constructible in P3 from `GeneratedMemReplayFacts` (`ZiskFv/AirsClean/Mem/TraceSpec.lean:52-58`), whose `prefixReadSound` already has the exact type required by `AcceptedMemoryReplayEvidence`. | PR3 |
| `priorRows` | Packed inside the caller-supplied evidence as the selected load prefix (`MemTrace.lean:1281`). | Bucket (b): constructible in P3 by locating `bus.e1` in the accepted chronological memory-bus row list using the Main load entry, the selected provider row, and the `MemBusChannel` balance facts already exposed by load structural-unpacking exceptions. | PR3 |
| `laterRows` | Packed inside the caller-supplied evidence as the selected load suffix (`MemTrace.lean:1282`). | Bucket (b): constructible with `priorRows` from the same list split. | PR3 |
| `traceSplit` | Packed inside the caller-supplied evidence (`MemTrace.lean:1283`). | Bucket (b): follows from the selected-row list split once the Main entry is linked to its accepted Mem provider row. `ZiskFv.Airs.OperationBus.matches_entry` names fieldwise entry equality for operation-bus rows (`ZiskFv/Airs/OperationBus/OperationBus.lean:219`), while memory-bus provider matching is exposed through full-ensemble balance hooks such as `activeMainMemProviderRowMatchSpec_of_active_main_eval` (`ZiskFv/AirsClean/FullEnsemble/Balance.lean:9264`). | PR3 |
| `selectedRead` | Packed inside the caller-supplied evidence (`MemTrace.lean:1284-1285`). | Bucket (b): constructible from the load structural promise tags `m1_mult : e1.multiplicity = -1` and `m1_as : e1.as.val = 2` (`ZiskFv/EquivCore/Promises/Load.lean:84-85`) plus `memoryBusTraceEventOfRow`/`memoryBusTraceEventOfRow_read` (`MemTrace.lean:790,1091`). | PR3 |
| `stateBytesAtPrefix` | Packed inside the caller-supplied evidence (`MemTrace.lean:1286-1289`). | Bucket (c) unless PR4 can close the Sail trace-state alignment locally. The circuit side can derive the replay prefix from Mem AIR ordering, row linkage, stores, and `GeneratedMemReplayFacts.initialAgreement`; the missing cross-cutting fact is that the `state` handed to the one-step load theorem is exactly the Sail state after the accepted prior memory events have executed. | PR4, or PR4 reduced to named P4-bound residual |

Once the structure is constructed, downstream byte agreement is already
derived: `MemoryTimelineEvidence.prefixReadAgreement` uses
`acceptedReplay.prefixReadSound` plus `traceSplit` and selected-read tags
(`MemTrace.lean:1293-1306`), `MemoryTimelineEvidence.memoryTraceAgreement`
combines prefix replay with `stateBytesAtPrefix` (`MemTrace.lean:1310-1320`),
and `loadByteAgreement_of_memory_timeline_evidence` feeds that into load
soundness (`ZiskFv/EquivCore/Promises/Load.lean:54-60`).

## Current Mem Groundwork

The Clean Mem surface is already on `origin/main`; P3 must consume it rather
than import the forbidden `memory-trust-gap` wrapper stack.

- `ZiskFv/AirsClean/Mem/Row.lean:23` defines the projected `MemRow`.
- `ZiskFv/AirsClean/Mem/Spec.lean:1-56` names the 9 F-typed per-row Mem AIR
  clauses and maps clauses 1-9 to generated constraints
  `constraint_3_every_row`, `constraint_4_every_row`, `constraint_5_every_row`,
  `constraint_6_every_row`, `constraint_7_every_row`,
  `constraint_8_every_row`, `constraint_18_every_row`,
  `constraint_21_every_row`, and `constraint_23_every_row`.
- `build/extraction/Extraction/Mem.lean:50-162` contains the extracted
  generated constraint definitions for the per-row clauses and the relevant
  segment constraints; `build/extraction/Extraction/Mem.lean:167-222` contains
  the permutation constraints `24..33`.
- `ZiskFv/Airs/Mem.lean:249` names `segment_every_row`,
  `ZiskFv/Airs/Mem.lean:1398` names `permutation_every_row`, and
  `ZiskFv/Airs/Mem.lean:1425` combines them as `generated_every_row`.
- `ZiskFv/AirsClean/Mem/Bridge.lean:411-448` projects the generated
  segment/permutation assertion witnesses, and
  `ZiskFv/AirsClean/Mem/Bridge.lean:476` proves `spec_of_valid`.
- `ZiskFv/AirsClean/Mem/Circuit.lean:217-243` exposes the mutable Mem
  component's memory-bus interactions, including the dual-memory-bus component
  needed by provider-row matching.
- `ZiskFv/AirsClean/Mem/TraceSpec.lean:17-58` names the chronological-row,
  generated-row, row-order, and replay-fact surfaces that PRs 2-4 should fill.

## Inputs Already Exposed By Load Routes

The seven load entries in `trust/structural-unpacking-exceptions.txt` already
carry the inputs P3 consumes rather than growing the public theorem surface:
`Ld@69`, `Lbu@77`, `Lhu@88`, `Lwu@95`, `Lb@102`, `Lh@112`, and `Lw@117`.
Those exceptions expose the mem-family Clean witness, `MemBusChannel` balance
proof, selected Main row equality, selected provider row equality, ROM pins,
width pins, and same-message proof from Clean balance.

The canonical load caller-burden ledger still shows each load binder carrying
`ZiskFv.EquivCore.Promises.LoadPromises`:
`LB@trust/generated/baseline-caller-burden.txt:332`,
`LBU@344`, `LD@354`, `LH@370`, `LHU@382`, `LW@414`, and `LWU@426`.
The wrapper ledger mirrors the same `LoadPromises` burden for the seven load
wrappers (`trust/generated/baseline-wrapper-caller-burden.txt:371,385,397,413,425,457,469`).
PR5 is the metric-moving PR that must replace those with
`LoadStructuralPromises` or a strictly smaller named P4-bound residual.

## `stateBytesAtPrefix` Decomposition

PR4 must not hide `stateBytesAtPrefix` behind another opaque promise. The target
decomposition is:

1. The replayed memory after `priorRows` at `e1.ptr` is the latest prior write
   row to that address, or `acceptedReplay.initialMemory` if there is no prior
   write. The circuit-side ingredients are the `replayMemoryAfterBusRows` fold
   (`MemTrace.lean:840`), same-address read/write replay facts
   (`MemTrace.lean:979-996`), and Mem ordering facts from generated segment
   constraints. Existing low-level lemmas already expose positive same-address
   step deltas (`ZiskFv/Airs/Mem.lean:745-775`) and positive address-change
   deltas (`ZiskFv/Airs/Mem.lean:929-960`).
2. The Sail state's bytes at `e1.ptr` are the latest prior Sail store to that
   address, or the initial memory when there is no prior store.
3. The two latest-write views agree because every accepted Sail store appears as
   a Mem write row with the same address/value and because the Mem
   address-sorted order agrees with chronological order inside an address class.
   The initial case uses `GeneratedMemReplayFacts.initialAgreement`
   (`ZiskFv/AirsClean/Mem/TraceSpec.lean:52-58`).

If step 3 needs a trace-global alignment fact, PR4 should reduce the residual to
one named fact rather than carrying `Nonempty MemoryTimelineEvidence`. The
proposed shape is:

```text
TraceStateAgreesWithReplayPrefix state acceptedReplay.initialMemory priorRows
```

meaning: for the selected Main load row, `state` is the Sail state obtained
after executing exactly the accepted memory-bus events in `priorRows`, starting
from an initial state that agrees with `acceptedReplay.initialMemory`. That fact
belongs to P4's `AcceptedTrace -> OpEnvelope` construction if it cannot be
proved from the row-local load envelope plus Mem AIR and balance facts alone.

## Baseline And Gate Notes

As of the PR1 baseline, the load hypothesis-count lines are:
`LB total=16 hypothesis=2`, `LBU total=12 hypothesis=1`,
`LD total=10 hypothesis=0`, `LH total=16 hypothesis=2`,
`LHU total=12 hypothesis=1`, `LW total=16 hypothesis=2`, and
`LWU total=12 hypothesis=1`
(`trust/generated/baseline-hypothesis-count.txt:34-41`). The seven load entries
in `trust/generated/baseline-equiv-axiom-deps.txt:21-28` remain empty of project
axioms, and the global project-axiom closure remains zero
(`trust/generated/baseline-zisk-riscv-compliant.txt`,
`trust/generated/baseline-axioms.txt`).

The semantic gate currently includes the false probe and the memory timeline
witness (`trust/scripts/check-all-semantic.sh:24-64`). The existing witness
constructs `memory_timeline_witness` and proves
`load_byte_agreement_of_timeline_witness`
(`trust/consistency/load_byte_agreement_witness.lean:97-112`); PR4 should add a
positive constructor witness next to it, without weakening the two-address
regression.
