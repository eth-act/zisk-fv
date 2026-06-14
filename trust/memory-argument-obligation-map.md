# Memory Argument Obligation Map

This map is the P3 close-out hand-off to P4. P3 does not reduce the memory trust
surface: it leaves the global theorem's memory premise visible and auditable,
then names the residual obligations P4 must remove.

## Current Public Boundary

The global theorem now takes
`h_memory_construction : env.memoryTimelineConstructionEvidence`
([ZiskFv/Compliance.lean:98](../ZiskFv/Compliance.lean#L98)) and threads it to
the load and memory-touching dispatchers. This is a reshape to a named
P4-bound residual, not a trust reduction.

`OpEnvelope.memoryTimelineConstructionEvidence` is the visible load-family
promise: each load arm requires `LoadMemoryTimelineConstructionEvidence state
bus.e1`, while non-load arms are `True`
([ZiskFv/Compliance/OpEnvelope.lean:2310](../ZiskFv/Compliance/OpEnvelope.lean#L2310),
[ZiskFv/Compliance/OpEnvelope.lean:2315](../ZiskFv/Compliance/OpEnvelope.lean#L2315),
[ZiskFv/Compliance/OpEnvelope.lean:2330](../ZiskFv/Compliance/OpEnvelope.lean#L2330)).
The older `OpEnvelope.memoryTimelineEvidence` API remains only as internal
adapter glue for existing load dispatchers
([ZiskFv/Compliance/OpEnvelope.lean:2235](../ZiskFv/Compliance/OpEnvelope.lean#L2235),
[ZiskFv/Compliance/OpEnvelope.lean:2333](../ZiskFv/Compliance/OpEnvelope.lean#L2333)).

`MemoryTimelineEvidence` decomposes the load promise into an accepted replay
object, a selected row split, a read-tag fact, and byte agreement between the
load Sail state and the replayed accepted prefix
([ZiskFv/ZiskCircuit/MemTrace.lean:1266](../ZiskFv/ZiskCircuit/MemTrace.lean#L1266),
[ZiskFv/ZiskCircuit/MemTrace.lean:1277](../ZiskFv/ZiskCircuit/MemTrace.lean#L1277),
[ZiskFv/ZiskCircuit/MemTrace.lean:1280](../ZiskFv/ZiskCircuit/MemTrace.lean#L1280),
[ZiskFv/ZiskCircuit/MemTrace.lean:1283](../ZiskFv/ZiskCircuit/MemTrace.lean#L1283),
[ZiskFv/ZiskCircuit/MemTrace.lean:1284](../ZiskFv/ZiskCircuit/MemTrace.lean#L1284),
[ZiskFv/ZiskCircuit/MemTrace.lean:1286](../ZiskFv/ZiskCircuit/MemTrace.lean#L1286)).

## Ledger

| Component | Status after P3 | Who removes it | Asset for the remover |
| --- | --- | --- | --- |
| `selectedRead` | Derived from load structural promises. | Done in P3. | `selectedRead_of_load_structural_promises` packages the `e1` read tag from `LoadStructuralPromises` ([ZiskFv/ZiskCircuit/MemTimeline/Linkage.lean:155](../ZiskFv/ZiskCircuit/MemTimeline/Linkage.lean#L155), [ZiskFv/ZiskCircuit/MemTimeline/Linkage.lean:169](../ZiskFv/ZiskCircuit/MemTimeline/Linkage.lean#L169)); the constructor consumes that derived fact directly ([ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:99](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L99), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:101](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L101)). |
| `stateBytesAtPrefix` | Derived from `MemoryPrefixStateAlignment` plus generated replay `initialAgreement`. | Done in P3 once those residuals are supplied. | `stateBytesAtPrefix_of_memoryPrefixStateAlignment` rewrites the state through the alignment and applies `replayAgreement_after_memoryBusRows` using `facts.initialAgreement` ([ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:36](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L36), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:45](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L45), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:49](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L49)). |
| `prefixReadSound` | Named P4-bound residual. The single-segment circuit-side chain exists, but the whole-trace cross-segment assembly does not. | P4. | `GeneratedMemReplayFacts` currently carries `prefixReadSound` as a field ([ZiskFv/AirsClean/Mem/TraceSpec.lean:52](../ZiskFv/AirsClean/Mem/TraceSpec.lean#L52), [ZiskFv/AirsClean/Mem/TraceSpec.lean:56](../ZiskFv/AirsClean/Mem/TraceSpec.lean#L56)). The concrete single-segment asset derives active-table prefix soundness and packages `AcceptedMemoryReplayEvidence` from generated Mem AIR facts ([ZiskFv/AirsClean/FullEnsemble/Balance.lean:6172](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6172), [ZiskFv/AirsClean/FullEnsemble/Balance.lean:6325](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6325), [ZiskFv/AirsClean/FullEnsemble/Balance.lean:6474](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6474)). P4 must assemble this across the accepted whole trace before it can remove the public memory premise. |
| `initialAgreement` | Named P4/boot residual. | P4 / program binding. | `GeneratedMemReplayFacts` carries `initialAgreement` ([ZiskFv/AirsClean/Mem/TraceSpec.lean:58](../ZiskFv/AirsClean/Mem/TraceSpec.lean#L58)); it is consumed to derive `stateBytesAtPrefix` ([ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:49](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L49), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:50](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L50)). It ties Sail `initialState.mem` to circuit `initialMemory`, so it belongs to the trace/program-binding construction rather than `Valid_Mem`. |
| `MemoryPrefixStateAlignment` | Named P4-bound residual. | P4. | The alignment identifies the selected load Sail state with replaying the accepted memory-bus prefix from the initial state ([ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:21](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L21), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:28](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L28), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:31](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L31)). The nonempty constructors still take this split-indexed alignment as an input ([ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:121](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L121), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:125](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L125), [ZiskFv/ZiskCircuit/MemTimeline/Construction.lean:162](../ZiskFv/ZiskCircuit/MemTimeline/Construction.lean#L162)). |
| store RMW preserved bytes (`sb`/`sh`/`sw` `h_m*`) | Bucket-(c), outside P3's load-only scope. | P4. | The envelope audit identifies the preserved-byte facts and explains that they should move into the memory replay construction or a store-event extension of the memory timeline ([trust/envelope-burden-audit.md:99](envelope-burden-audit.md#L99), [trust/envelope-burden-audit.md:120](envelope-burden-audit.md#L120), [trust/envelope-burden-audit.md:125](envelope-burden-audit.md#L125)). |

## Consistency Witnesses

`trust/consistency/global_theorem_instantiation_ld.lean` is an empty-prefix
satisfiability witness: the selected LD memory read is the first accepted memory
row, so the construction evidence uses `priorRows = []`.
`trust/consistency/memory_prefix_alignment_witness.lean` covers the non-empty
case by proving `MemoryPrefixStateAlignment initialState
(stateAfterMemoryBusRows initialState [storeRow]) [storeRow]` for one concrete
store row. Neither witness removes a P4 residual; they only demonstrate the
reshaped premise is satisfiable in both prefix shapes.

## P4 Assets That Are Not Yet a Discharge

The ordering lemmas in `ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean` are useful
P4 assets for same-address ordering and read-carry reasoning. They expose
same-address read facts, adjacent read-chain facts, and primary/dual timestamp
monotonicity
([ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean:21](../ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean#L21),
[ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean:72](../ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean#L72),
[ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean:121](../ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean#L121),
[ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean:139](../ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean#L139),
[ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean:157](../ZiskFv/ZiskCircuit/MemTimeline/Ordering.lean#L157)).
They are intentionally not wired into the current construction: using them well
requires P4's whole-trace accepted-row assembly.

The full-witness sidecar path likewise remains an asset, not a public-theorem
discharge. It can construct `MemoryTimelineEvidence` from generated Mem facts
only after being given the selected trace split, read tag, and state/prefix byte
agreement
([ZiskFv/AirsClean/FullEnsemble/Balance.lean:6495](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6495),
[ZiskFv/AirsClean/FullEnsemble/Balance.lean:6501](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6501),
[ZiskFv/AirsClean/FullEnsemble/Balance.lean:6503](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6503),
[ZiskFv/AirsClean/FullEnsemble/Balance.lean:6504](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6504),
[ZiskFv/AirsClean/FullEnsemble/Balance.lean:6507](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6507),
[ZiskFv/AirsClean/FullEnsemble/Balance.lean:6514](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6514)).
Generated-artifact wrappers preserve the sidecar provenance
([ZiskFv/AirsClean/FullEnsemble/Balance.lean:6758](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6758),
[ZiskFv/AirsClean/FullEnsemble/Balance.lean:6807](../ZiskFv/AirsClean/FullEnsemble/Balance.lean#L6807)).

## Close-Out Rule

P3 done does not mean memory trust is reduced. P3 done means the memory premise is
auditable and the remaining work is named: whole-trace `prefixReadSound`,
`initialAgreement`, `MemoryPrefixStateAlignment`, and store preserved-byte replay
belong to P4.
