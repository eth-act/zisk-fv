import ZiskFv.Compliance.TraceLevelExport.Dispatcher

/-!
# The boot / cross-segment memory seed (`BootSegmentMemorySeed`)

`root_soundness`'s loads and stores each consume a memory-coherence fact — "the value in memory at
this address is what the circuit claims" — that no single instruction can supply, because it depends
on the whole history of earlier writes.  #185 unified the ten former per-op residuals (seven loads +
`sb`/`sh`/`sw`) into ONE named premise, the `BootSegmentMemorySeed`.

**Issue #115 (this form).** #185's seed stated its memory-evolution assumption as an *opaque* free
cursor function `stateAt : List rows → SailState` plus a whole-sequence
`coherence : RowTraceCoherence stateAt [] rows`.  This form states it *concretely* instead:

* `memInit` + `boot` — the segment's boot / cross-segment seed memory (irreducible at the single-
  segment level: a segment does not contain its own starting state, it is carried in from boot);
* `step` — the per-step **execution-successor**: each Sail step's memory is the replay of that step's
  memory-bus rows onto the previous step's memory (cross-row memory coherence);
* `readSound` — memory-bus **read-soundness** over the whole execution-order row list.  This is the
  out-of-scope ExtF memory-bus **permutation** trust (see `trust/trusted-base.md`;
  `Airs/MemoryBus/MemBridge.lean`), carried as a named premise of that existing class;
* `placement` — the *structural* tie pinning `rowsOf i` to each op's real memory-bus row (a load's
  read `busLd .. .e1`, a narrow store's write `busSt .. .e2` plus its preserved-byte prefix fact).

`memEvidence_of_bootSeed` derives each op's `MemoryOpEvidenceFor` residual by the execution-order fold
(`Spike.exec_order_fold_fin` gives the per-op state pin from `boot` + `step`;
`Spike.exists_flatMap_range_split_of_singleton` locates the op's row; `loadEvidence_of_loadMemReplay` /
`storeEvidence_of_loadMemReplay` build the evidence).

This is a **constructibility restatement, net-zero-to-marginally-stronger on trust** versus #185's
opaque form — NOT a reduction.  `Spike.rowTraceCoherence_of_uniformReplayMem` mechanizes only the
reconstruction direction (`step + boot` ⟹ the uniform-replay cursor satisfies `RowTraceCoherence`;
there is no converse), and the concrete `step` pins `binding.mem` at *every* index where the opaque
chain tied it only at memory-op indices — a difference real traces satisfy trivially (no vacuity).
`readSound` is the same read-soundness `facts` already carried.  The value is *constructibility*: the
memory premise is now concrete, with NO opaque `stateAt` existential and NO whole-sequence
`RowTraceCoherence` on the assumed surface (#115 acceptance "named premises, not an opaque whole-Sail-
state equality"), which is the seam the non-degenerate load instantiation (#221 → #74) needs.  It is a
named external-trust premise (same class as channel-balance), NOT an axiom and NOT a defect; the
read-soundness half remains the memory-bus permutation trust, whose full derivation from
`constraints_hold`/`channels_balanced` is a separate epic. -/

namespace ZiskFv.Compliance

open Interaction
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.ZiskCircuit.MemTimeline.Spike

variable {numInstructions : Nat}

/-! ## The concrete reductions: a clean mem-replay equation implies the op residual. -/

/-- Discharge a load's `LoadMemoryTimelineCoherenceEvidence` from
`state.mem = replayMemoryAfterBusRows facts.initialMemory priorRows`, re-choosing the state-side
existentials as the uniform replay assignment `stateAt X := { state with mem := replay im X }`
(`rowTraceCoherence_of_uniformReplayMem` makes its coherence chain hold, the seed pin is `rfl`, the
state pin is the equation).  The read content (`prefixReadSound`) is inherited from `facts`. -/
theorem loadEvidence_of_loadMemReplay
    {state initialState : SailState}
    {rows priorRows laterRows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_load_mem : state.mem = replayMemoryAfterBusRows facts.initialMemory priorRows) :
    LoadMemoryTimelineCoherenceEvidence state entry := by
  set im := facts.initialMemory with him
  refine ⟨{ state with mem := im }, rows,
    { initialMemory := im
      prefixReadSound := facts.prefixReadSound
      initialAgreement := fun _ => rfl },
    fun X => { state with mem := replayMemoryAfterBusRows im X },
    priorRows, laterRows, h_split, ?_, ?_,
    rowTraceCoherence_of_uniformReplayMem state im [] priorRows⟩
  · show ({ state with mem := replayMemoryAfterBusRows im [] } : SailState)
        = { state with mem := im }
    rfl
  · show ({ state with mem := replayMemoryAfterBusRows im priorRows } : SailState) = state
    rw [← h_load_mem]

/-- The store analogue, additionally carrying the narrow-store preserved-byte prefix fact. -/
theorem storeEvidence_of_loadMemReplay
    {state initialState : SailState}
    {rows priorRows laterRows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL} {firstPreserved : Nat}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_load_mem : state.mem = replayMemoryAfterBusRows facts.initialMemory priorRows)
    (h_preserved :
      StoreRmwPreservedBytesAtPrefix
        (replayMemoryAfterBusRows facts.initialMemory priorRows) entry firstPreserved) :
    StoreRmwMemoryCoherenceEvidence state entry firstPreserved := by
  set im := facts.initialMemory with him
  refine ⟨{ state with mem := im }, rows,
    { initialMemory := im
      prefixReadSound := facts.prefixReadSound
      initialAgreement := fun _ => rfl },
    fun X => { state with mem := replayMemoryAfterBusRows im X },
    priorRows, laterRows, h_split, ?_, ?_,
    rowTraceCoherence_of_uniformReplayMem state im [] priorRows, h_preserved⟩
  · show ({ state with mem := replayMemoryAfterBusRows im [] } : SailState)
        = { state with mem := im }
    rfl
  · show ({ state with mem := replayMemoryAfterBusRows im priorRows } : SailState) = state
    rw [← h_load_mem]

/-! ## The seed and its per-op derivation -/

/-- Per-memory-op placement relative to the concrete seed: the *structural* tie pinning `rowsOf i` to
    this op's real memory-bus row — a load's read `busLd .. .e1`, a narrow store's write `busSt .. .e2`
    (plus the preserved high bytes already present in the replay memory at that op's execution-order
    prefix `(List.range i).flatMap rowsOf`).  Non-narrow-store / non-load ops impose nothing here:
    their `rowsOf` is pinned by `step`'s satisfiability (a store must change memory, a non-memory op
    must not).  The split, cursor tie, and coherence chain #185 carried are now *derived*, not
    assumed. -/
def MemoryOpPlacement
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ =>
      rowsOf i.val = [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1]
  | .sb _ =>
      rowsOf i.val = [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]
        ∧ StoreRmwPreservedBytesAtPrefix
            (replayMemoryAfterBusRows memInit ((List.range i.val).flatMap rowsOf))
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 1
  | .sh _ =>
      rowsOf i.val = [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]
        ∧ StoreRmwPreservedBytesAtPrefix
            (replayMemoryAfterBusRows memInit ((List.range i.val).flatMap rowsOf))
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 2
  | .sw _ =>
      rowsOf i.val = [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]
        ∧ StoreRmwPreservedBytesAtPrefix
            (replayMemoryAfterBusRows memInit ((List.range i.val).flatMap rowsOf))
            (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 4
  | _ => True

/-- **The single named boot / cross-segment memory seed premise of `root_soundness`.**

    One shared assumption for the whole segment, replacing the ten former per-op memory residuals,
    stated concretely (see the module header): `memInit`/`boot` (boot seed), `step` (execution-
    successor), `readSound` (memory-bus read-soundness), and the structural `placement`.
    `memEvidence_of_bootSeed` derives every op's `MemoryOpEvidenceFor` residual from it by the
    execution-order fold.  Named external-trust premise (same class as channel-balance), NOT an axiom;
    driving the residual read-soundness half to zero is the memory-bus permutation epic. -/
structure BootSegmentMemorySeed
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace ziskTrace.numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) where
  /-- The segment boot / cross-segment seed memory. -/
  memInit : Std.ExtHashMap Nat (BitVec 8)
  /-- The per-instruction memory-bus rows (as = 2), pinned to the trace by `placement` / `step`. -/
  rowsOf : ℕ → List (MemoryBusEntry FGL)
  /-- Boot seed: the initial Sail memory is the boot memory. Guarded so the empty segment is trivial. -/
  boot : ∀ (h : 0 < ziskTrace.numInstructions), (binding ⟨0, h⟩).mem = memInit
  /-- Execution-successor: each Sail step's memory is the replay of that step's memory rows onto the
      previous step's memory. -/
  step : ∀ (j : ℕ) (h : j + 1 < ziskTrace.numInstructions),
      (binding ⟨j + 1, h⟩).mem
        = replayMemoryAfterBusRows (binding ⟨j, Nat.lt_of_succ_lt h⟩).mem (rowsOf j)
  /-- Memory-bus read-soundness over the whole execution-order row list. -/
  readSound :
    MemoryBusRowsPrefixReadSound memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf)
  /-- Structural placement pinning `rowsOf` to each memory op's real bus row (+ narrow-store bytes). -/
  placement : ∀ i : Fin ziskTrace.numInstructions,
    MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i)

/-! ## Per-op discharge via the execution-order fold. -/

/-- Discharge one load's residual from the seed and its structural row tie, via the fold. -/
theorem loadEvidence_of_seed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (i : Fin ziskTrace.numInstructions)
    (h_rows : seed.rowsOf i.val = [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1]) :
    LoadMemoryTimelineCoherenceEvidence (binding i)
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 := by
  have hpos : 0 < ziskTrace.numInstructions := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨laterRows, h_split⟩ :=
    exists_flatMap_range_split_of_singleton seed.rowsOf i.val i.isLt _ h_rows
  exact loadEvidence_of_loadMemReplay
    (initialState := binding ⟨0, hpos⟩)
    { initialMemory := seed.memInit
      prefixReadSound := seed.readSound
      initialAgreement := fun _ => by rw [seed.boot hpos] }
    h_split
    (exec_order_fold_fin binding seed.memInit seed.rowsOf hpos (seed.boot hpos) seed.step i)

/-- Discharge one narrow store's RMW residual from the seed and its structural row + preserved-byte
    ties, via the fold. -/
theorem storeEvidence_of_seed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (i : Fin ziskTrace.numInstructions) (firstPreserved : Nat)
    (h_rows : seed.rowsOf i.val = [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2])
    (h_bytes : StoreRmwPreservedBytesAtPrefix
      (replayMemoryAfterBusRows seed.memInit ((List.range i.val).flatMap seed.rowsOf))
      (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 firstPreserved) :
    StoreRmwMemoryCoherenceEvidence (binding i)
      (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 firstPreserved := by
  have hpos : 0 < ziskTrace.numInstructions := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  obtain ⟨laterRows, h_split⟩ :=
    exists_flatMap_range_split_of_singleton seed.rowsOf i.val i.isLt _ h_rows
  exact storeEvidence_of_loadMemReplay
    (initialState := binding ⟨0, hpos⟩)
    { initialMemory := seed.memInit
      prefixReadSound := seed.readSound
      initialAgreement := fun _ => by rw [seed.boot hpos] }
    h_split
    (exec_order_fold_fin binding seed.memInit seed.rowsOf hpos (seed.boot hpos) seed.step i)
    h_bytes

/-- Derive each memory op's residual (`MemoryOpEvidenceFor`) from the one shared seed, via the
    execution-order fold.  Non-memory ops and `sd` get the trivial residual. -/
def memEvidence_of_bootSeed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (i : Fin ziskTrace.numInstructions) :
    MemoryOpEvidenceFor ziskTrace binding i (ziskStep i) :=
  match ziskStep i, seed.placement i with
  | .ld _, h_rows
  | .lbu _, h_rows
  | .lhu _, h_rows
  | .lwu _, h_rows
  | .lb _, h_rows
  | .lh _, h_rows
  | .lw _, h_rows =>
      loadEvidence_of_seed seed i h_rows
  | .sb _, ⟨h_rows, h_bytes⟩ =>
      storeEvidence_of_seed seed i 1 h_rows h_bytes
  | .sh _, ⟨h_rows, h_bytes⟩ =>
      storeEvidence_of_seed seed i 2 h_rows h_bytes
  | .sw _, ⟨h_rows, h_bytes⟩ =>
      storeEvidence_of_seed seed i 4 h_rows h_bytes
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
