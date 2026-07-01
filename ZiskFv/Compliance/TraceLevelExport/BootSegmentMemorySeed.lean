import ZiskFv.Compliance.TraceLevelExport.Dispatcher

/-!
# The boot / cross-segment memory seed (`BootSegmentMemorySeed`)

`root_soundness`'s loads and stores each consume a memory-coherence fact — "the
value in memory at this address is what the circuit claims" — that no single
instruction can supply, because it depends on the whole history of earlier
writes.  Historically the ten memory ops (seven loads + `sb`/`sh`/`sw`) each
carried their *own* existential copy of that story as an `Inputs_<op>` field
(`h_memory_timeline` / `h_store_rmw`), so nothing forced the ten copies to agree.

This module replaces those ten scattered residuals with ONE named premise, the
`BootSegmentMemorySeed`: the segment's initial memory state plus the single
consistent per-row memory-evolution chain (`RowTraceCoherence` over the *whole*
consumed memory-bus row sequence).  `memEvidence_of_bootSeed` then *derives* each
op's residual from that shared seed, restricting the whole-sequence coherence to
the op's prefix via `rowTraceCoherence_of_append`.

This is the MVP legibility step of issue #185: the seed is legitimately *assumed*
(a segment does not contain its own starting state — it is carried in from the
previous segment / boot).  Driving the seed to zero is the follow-on work in #115
/ #119.  Only the memory field of each cursor state is constrained; PC /
registers are pinned only incidentally through the initial-state snapshot
(per-step next-PC is discharged separately, #163), which is why this is a
*memory* seed rather than a "memory+PC" one. -/

namespace ZiskFv.Compliance

open Interaction

variable {numInstructions : Nat}

/-! ## Restricting the shared whole-sequence coherence to one op's prefix -/

/-- Derive one load's `LoadMemoryTimelineCoherenceEvidence` from the shared seed
    data (replay facts, cursor-indexed state assignment, whole-sequence
    coherence) plus this op's prefix split and cursor tie.  The whole-sequence
    coherence `RowTraceCoherence stateAt [] rows` is restricted to the op's prefix
    by `rowTraceCoherence_of_append`. -/
theorem loadCoherence_of_shared
    {initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (MemoryBusEntry FGL)}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (stateAt : List (MemoryBusEntry FGL) → ZiskFv.ZiskCircuit.MemTrace.SailState)
    (h_seed : stateAt [] = initialState)
    (coherence : ZiskFv.ZiskCircuit.MemTimeline.Spike.RowTraceCoherence stateAt [] rows)
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {entry : MemoryBusEntry FGL}
    {priorRows laterRows : List (MemoryBusEntry FGL)}
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_tie : stateAt priorRows = state) :
    LoadMemoryTimelineCoherenceEvidence state entry := by
  refine ⟨initialState, rows, facts, stateAt, priorRows, laterRows, h_split, h_seed, h_tie, ?_⟩
  rw [h_split] at coherence
  exact ZiskFv.ZiskCircuit.MemTimeline.Spike.rowTraceCoherence_of_append
    stateAt [] priorRows (entry :: laterRows) coherence

/-- The store analogue of `loadCoherence_of_shared`, additionally carrying the
    narrow-store preserved-byte prefix fact into the RMW evidence. -/
theorem storeCoherence_of_shared
    {initialState : ZiskFv.ZiskCircuit.MemTrace.SailState}
    {rows : List (MemoryBusEntry FGL)}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (stateAt : List (MemoryBusEntry FGL) → ZiskFv.ZiskCircuit.MemTrace.SailState)
    (h_seed : stateAt [] = initialState)
    (coherence : ZiskFv.ZiskCircuit.MemTimeline.Spike.RowTraceCoherence stateAt [] rows)
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {entry : MemoryBusEntry FGL} {firstPreserved : Nat}
    {priorRows laterRows : List (MemoryBusEntry FGL)}
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_tie : stateAt priorRows = state)
    (h_bytes : StoreRmwPreservedBytesAtPrefix
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows facts.initialMemory priorRows)
      entry firstPreserved) :
    StoreRmwMemoryCoherenceEvidence state entry firstPreserved := by
  refine ⟨initialState, rows, facts, stateAt, priorRows, laterRows, h_split, h_seed, h_tie, ?_, h_bytes⟩
  rw [h_split] at coherence
  exact ZiskFv.ZiskCircuit.MemTimeline.Spike.rowTraceCoherence_of_append
    stateAt [] priorRows (entry :: laterRows) coherence

/-! ## The seed and its per-op derivation -/

/-- Per-memory-op placement relative to a shared segment memory seed: for each
    load / narrow store row, where its memory-bus entry sits in the shared row
    sequence `rows`, that the op's Sail state `binding i` is the seed's cursor
    state `stateAt priorRows` there, and (for narrow RMW stores) that the
    preserved high bytes are already present in the replay memory at that prefix.
    Non-memory ops and `sd` (a full-doubleword store) impose nothing. -/
def MemoryOpPlacement
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace ziskTrace.numInstructions)
    (rows : List (MemoryBusEntry FGL))
    (stateAt : List (MemoryBusEntry FGL) → ZiskFv.ZiskCircuit.MemTrace.SailState)
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ =>
      ∃ priorRows laterRows,
        rows = priorRows ++ (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 :: laterRows
          ∧ stateAt priorRows = binding i
  | .sb _ =>
      ∃ priorRows laterRows,
        rows = priorRows ++ (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 :: laterRows
          ∧ stateAt priorRows = binding i
          ∧ StoreRmwPreservedBytesAtPrefix
              (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory priorRows)
              (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 1
  | .sh _ =>
      ∃ priorRows laterRows,
        rows = priorRows ++ (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 :: laterRows
          ∧ stateAt priorRows = binding i
          ∧ StoreRmwPreservedBytesAtPrefix
              (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory priorRows)
              (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 2
  | .sw _ =>
      ∃ priorRows laterRows,
        rows = priorRows ++ (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 :: laterRows
          ∧ stateAt priorRows = binding i
          ∧ StoreRmwPreservedBytesAtPrefix
              (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRows initialMemory priorRows)
              (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 4
  | _ => True

/-- **The single named boot / cross-segment memory seed premise of `root_soundness`.**

    One shared assumption for the whole segment, replacing the ten former per-op
    memory residuals.  It supplies:
    * `initialState` — the segment-entry Sail state (its memory is the boot /
      cross-segment seed carried in from the previous segment / boot);
    * `rows` / `facts` — the consumed memory-bus row sequence and its replay facts
      (seed memory agreement + prefix read-soundness);
    * `stateAt` / `coherence` — a cursor-indexed Sail-state assignment whose
      empty-prefix value is `initialState`, coherent (memory only) across the
      *whole* row sequence;
    * `placement` — for each memory op, where its bus entry sits in `rows` and
      that its Sail state is the cursor state there (plus preserved bytes for
      narrow stores).

    `memEvidence_of_bootSeed` derives every op's `MemoryOpEvidenceFor` residual
    from this one seed.  This is a named external-trust premise (the same class as
    channel-balance), NOT an axiom and NOT a defect; driving it to zero is #115 /
    #119. -/
structure BootSegmentMemorySeed
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace ziskTrace.numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) where
  initialState : ZiskFv.ZiskCircuit.MemTrace.SailState
  rows : List (MemoryBusEntry FGL)
  facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows
  stateAt : List (MemoryBusEntry FGL) → ZiskFv.ZiskCircuit.MemTrace.SailState
  h_seed : stateAt [] = initialState
  coherence : ZiskFv.ZiskCircuit.MemTimeline.Spike.RowTraceCoherence stateAt [] rows
  placement : ∀ i : Fin ziskTrace.numInstructions,
    MemoryOpPlacement ziskTrace binding rows stateAt facts.initialMemory i (ziskStep i)

/-- Derive each memory op's residual (`MemoryOpEvidenceFor`) from the one shared
    seed, restricting its whole-sequence coherence to the op's prefix.  Non-memory
    ops and `sd` get the trivial residual. -/
def memEvidence_of_bootSeed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (i : Fin ziskTrace.numInstructions) :
    MemoryOpEvidenceFor ziskTrace binding i (ziskStep i) :=
  match ziskStep i, seed.placement i with
  | .ld _, ⟨_, _, h_split, h_tie⟩
  | .lbu _, ⟨_, _, h_split, h_tie⟩
  | .lhu _, ⟨_, _, h_split, h_tie⟩
  | .lwu _, ⟨_, _, h_split, h_tie⟩
  | .lb _, ⟨_, _, h_split, h_tie⟩
  | .lh _, ⟨_, _, h_split, h_tie⟩
  | .lw _, ⟨_, _, h_split, h_tie⟩ =>
      loadCoherence_of_shared seed.facts seed.stateAt seed.h_seed seed.coherence h_split h_tie
  | .sb _, ⟨_, _, h_split, h_tie, h_bytes⟩ =>
      storeCoherence_of_shared seed.facts seed.stateAt seed.h_seed seed.coherence h_split h_tie h_bytes
  | .sh _, ⟨_, _, h_split, h_tie, h_bytes⟩ =>
      storeCoherence_of_shared seed.facts seed.stateAt seed.h_seed seed.coherence h_split h_tie h_bytes
  | .sw _, ⟨_, _, h_split, h_tie, h_bytes⟩ =>
      storeCoherence_of_shared seed.facts seed.stateAt seed.h_seed seed.coherence h_split h_tie h_bytes
  | .sub _, _ | .and _, _ | .or _, _ | .xor _, _ | .slt _, _ | .sltu _, _
  | .andi _, _ | .ori _, _ | .xori _, _ | .slti _, _ | .sltiu _, _
  | .sll _, _ | .srl _, _ | .sra _, _ | .slli _, _ | .srli _, _ | .srai _, _
  | .add _, _ | .addi _, _ | .subw _, _ | .addw _, _ | .addiw _, _
  | .sllw _, _ | .srlw _, _ | .sraw _, _ | .slliw _, _ | .srliw _, _ | .sraiw _, _
  | .mul _, _ | .mulh _, _ | .mulhsu _, _ | .mulw _, _ | .mulhu _, _
  | .div _, _ | .rem _, _ | .divw _, _ | .remw _, _ | .divu _, _ | .divuw _, _
  | .remu _, _ | .remuw _, _
  | .beq _, _ | .bne _, _ | .blt _, _ | .bge _, _ | .bltu _, _ | .bgeu _, _
  | .lui _, _ | .auipc _, _ | .jal _, _ | .jalr _, _ | .sd _, _ | .fence _, _ =>
      trivial

end ZiskFv.Compliance
