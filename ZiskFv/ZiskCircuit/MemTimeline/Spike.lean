import ZiskFv.ZiskCircuit.MemTimeline.Construction

/-!
# Memory timeline — store-driven Fold-B reduction (PR-76.0)

This module is the make-or-break PR-76.0 reduction for issue #76 (`PLAN_ENDGAME_P4_MEMORY.md`
§3/§5). It demonstrates that the **byte-local** memory agreement that the load arms
actually consume (`ReplayMemoryAgreementOnBytes … entry.ptr`, i.e. the
`stateBytesAtPrefix` field of `MemoryTimelineEvidence`) is **derived** from:

* the store-driven replay fold (per-store `EventReplayStep` induction over the
  accepted chronological prefix — only stores transport the memory map; loads and
  non-memory ops are `.mem`-invariant);
* the already-derived read-soundness `prefixReadSound` (PR#65); and
* a single, **explicit, named trace-coherence residual** (`RowTraceCoherence`),

with the load's Sail `state` left **opaque** (`stateAt priorRows`), so the
derivation does **not** freeze registers / PC the way the whole-`SailState`
`MemoryPrefixStateAlignment` identity does.

## What is *derived* vs what *remains* (anti-laundering, plan §3 P0/P1/P2)

The Sail↔circuit memory connection is *conserved*: the replay engine only
**transports** agreement, it never manufactures it. Concretely:

* **Derived here:** the byte-local agreement `stateBytesAtPrefix` and the full
  `MemoryTraceAgreement` for the selected load, obtained by folding the per-store
  steps from the seed agreement and combining with `prefixReadSound`.
* **The named residual (`RowTraceCoherence`):** at each consumed prefix row the
  Sail state at the next execution cursor must be the row's memory transition of
  the Sail state at the current cursor. This is the *trace-coherence* premise
  (`stateAt (i+1)` is the execution successor of `stateAt i`); `ProgramBinding`
  carries no field for it, so it stands as **external trust**, exactly like
  channel-balance. It is NOT removed by this reduction — it is named, exposed as a
  binder, and is *strictly smaller* than the original whole-state
  `MemoryPrefixStateAlignment` existential (see §metric below).
* **Also a residual:** the *seed* `initialAgreement` (the segment's initial Sail
  memory agrees with the replay's initial memory) — the seg-0 boot / cross-segment
  seed correctness already tracked as external trust.

This reduction does **not** make the load arms premise-free. It **reduces** the load
memory obligation from the whole-`SailState` identity to {byte-local agreement,
which is derived} + {`RowTraceCoherence`, a named trace-coherence residual}.

## Metric shrink (plan §5 gate 5, §7 invariant 3)

* **Before:** `MemoryPrefixStateAlignment initialState state priorRows`, i.e.
  `state = stateAfterMemoryBusRows initialState priorRows` — a *whole-`SailState`*
  equality. It pins every field of `state` (regs, choiceState, mem, tags,
  cycleCount, sailOutput) to a closed-form replay of the prefix. This is strictly
  stronger than anything the load consumer needs and is unprovable without a
  closed form for the entire execution state.
* **After:** `RowTraceCoherence stateAt [] priorRows` — a *per-row, memory-map-only*
  chain of `EventReplayStep`s. Each conjunct constrains only `.mem` (`regs`/PC are
  free); the load `state` is `stateAt priorRows`, left opaque. The byte agreement
  the consumer needs is then *derived*, not assumed.

`RowTraceCoherence` is strictly weaker than the whole-state identity: it never
constrains `regs`/`choiceState`/`cycleCount`/`sailOutput`, and it is a memory-map
agreement chain rather than a closed-form whole-state identity. The non-vacuity
witness below exhibits a model where the load state's `regs` **and** `cycleCount`
differ from the initial state — impossible under the frozen `MemoryPrefixStateAlignment`
route, demonstrating the residual genuinely shrank.

No new project (`ZiskFv.*`) axioms; everything here is kernel-only
(`propext`/`Classical.choice`/`Quot.sound`).
-/

namespace ZiskFv.ZiskCircuit.MemTimeline.Spike

open Goldilocks
open Interaction
open ZiskFv.ZiskCircuit.MemTrace

/-! ## The named trace-coherence residual and the Fold-B core -/

/-- **Named trace-coherence residual** (plan §3 P1, §6 (c)).

For an opaque cursor-indexed Sail state assignment `stateAt`, every consumed
prefix row is an `EventReplayStep` between the Sail states at consecutive
execution cursors: the row's memory transition takes any replay memory agreeing
with the current cursor's Sail memory to one agreeing with the next cursor's Sail
memory. Stores transport the map via `writeMemoryOfEntry`; reads / inactive /
non-memory rows leave it unchanged. **Only `.mem` is constrained** — `regs`, PC,
`cycleCount`, etc. are free, so this never freezes the whole Sail state.

This is the trace-coherence premise that `ProgramBinding` does not supply; it is
carried as explicit external trust (like channel-balance), NOT derived here. -/
def RowTraceCoherence
    (stateAt : List (MemoryBusEntry FGL) → SailState) :
    List (MemoryBusEntry FGL) → List (MemoryBusEntry FGL) → Prop
  | _done, [] => True
  | done, row :: rest =>
      (∀ mem : Std.ExtHashMap Nat (BitVec 8),
        ReplayMemoryAgreement (stateAt done) mem →
          ReplayMemoryAgreement (stateAt (done ++ [row]))
            (replayMemoryAfterBusRow mem row))
      ∧ RowTraceCoherence stateAt (done ++ [row]) rest

/-- Trace coherence restricts to any prefix of the consumed rows. -/
theorem rowTraceCoherence_of_append
    (stateAt : List (MemoryBusEntry FGL) → SailState)
    (done pref suffix : List (MemoryBusEntry FGL))
    (h_steps : RowTraceCoherence stateAt done (pref ++ suffix)) :
    RowTraceCoherence stateAt done pref := by
  induction pref generalizing done with
  | nil => trivial
  | cons row rest ih =>
      simp only [List.cons_append, RowTraceCoherence] at h_steps ⊢
      exact ⟨h_steps.1, ih (done ++ [row]) h_steps.2⟩

/-- **Fold-B core.** From a seed agreement at the prefix start and the named
trace-coherence residual over the prefix, derive whole-map Sail/replay agreement
at the prefix end. The replay engine only *transports* the seed agreement through
the per-store memory transitions; the Sail state at the end is `stateAt …`, opaque.

This is the genuine store-driven derivation (plan §7 invariant 1): the agreement
is folded out of the per-row steps, never re-posited. -/
theorem replayAgreement_of_rowTraceCoherence
    (stateAt : List (MemoryBusEntry FGL) → SailState)
    (done rows : List (MemoryBusEntry FGL))
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (h_initial : ReplayMemoryAgreement (stateAt done) mem)
    (h_steps : RowTraceCoherence stateAt done rows) :
    ReplayMemoryAgreement (stateAt (done ++ rows))
      (replayMemoryAfterBusRows mem rows) := by
  induction rows generalizing done mem with
  | nil =>
      simpa [RowTraceCoherence, replayMemoryAfterBusRows] using h_initial
  | cons row rest ih =>
      simp only [RowTraceCoherence] at h_steps
      have h_next := h_steps.1 mem h_initial
      have h_tail :=
        ih (done ++ [row]) (replayMemoryAfterBusRow mem row) h_next h_steps.2
      simpa [replayMemoryAfterBusRows, List.append_assoc] using h_tail

/-! ## Per-row step constructors (store-driven; loads/non-memory invariant) -/

/-- **Per-store step (plan §3 P2 producer side, §5 gate 3).** A write row is a
`RowTraceCoherence` step whenever the next cursor's Sail memory is the eight-lane
`bus_effect` write of the current cursor's Sail memory. This is discharged from
the canonical write-entry transition `replayMemoryAgreement_write_entry` (the same
`{state with mem := writeMemoryOfEntry …}` shape `bus_effect.2` produces for
stores), **not** a hand-built `{state with mem}`. Only the memory field of the
post-state is constrained, so the store's nextPC `writeReg` (regs / PC mutation)
is free. -/
theorem rowStep_store_entry
    (before after : SailState) (row : MemoryBusEntry FGL)
    (h_as : row.as = (2 : FGL))
    (h_write : row.multiplicity = (1 : FGL))
    (h_after_mem : after.mem = writeMemoryOfEntry before.mem row)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (h_agree : ReplayMemoryAgreement before mem) :
    ReplayMemoryAgreement after (replayMemoryAfterBusRow mem row) := by
  rw [replayMemoryAfterBusRow, if_pos h_as, if_pos h_write]
  have h_step := replayMemoryAgreement_write_entry before mem row h_agree
  intro addr
  have h_addr := h_step addr
  rw [h_after_mem]
  simpa using h_addr

/-- **Load / non-memory step (plan §3 P2, §6 (d)).** Any row that is not an active
memory write is a `RowTraceCoherence` step whenever the next cursor's Sail memory
equals the current cursor's Sail memory. Regs / PC are free, so a load's `rd`
write or a non-memory opcode's register effect does not interfere. -/
theorem rowStep_mem_invariant
    (before after : SailState) (row : MemoryBusEntry FGL)
    (h_not_write : ¬ (row.as = (2 : FGL) ∧ row.multiplicity = (1 : FGL)))
    (h_after_mem : after.mem = before.mem)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (h_agree : ReplayMemoryAgreement before mem) :
    ReplayMemoryAgreement after (replayMemoryAfterBusRow mem row) := by
  have h_row : replayMemoryAfterBusRow mem row = mem := by
    unfold replayMemoryAfterBusRow
    by_cases h_as : row.as = (2 : FGL)
    · by_cases h_w : row.multiplicity = (1 : FGL)
      · exact absurd ⟨h_as, h_w⟩ h_not_write
      · simp [h_as, h_w]
    · simp [h_as]
  rw [h_row]
  intro addr
  rw [h_after_mem]
  exact h_agree addr

/-! ## The byte-local payoff: derived from the fold + the seed + prefixReadSound -/

/-- **The byte-local agreement, DERIVED.** Given generated replay facts (which carry
the seed `initialAgreement` and `prefixReadSound`), an opaque cursor-indexed state
assignment whose empty-prefix state is the segment initial state, and the named
trace-coherence residual over the selected prefix, the load state
`stateAt priorRows` byte-agrees with the replayed prefix at the read pointer.

This is exactly the `stateBytesAtPrefix` field of `MemoryTimelineEvidence`, now
*folded out* of the per-store steps rather than read off a whole-state identity.
The load `state` here is `stateAt priorRows` — **opaque**, NOT let-bound to
`stateAfterMemoryBusRows …`. -/
theorem stateBytesAtPrefix_of_rowTraceCoherence
    {initialState : SailState}
    {rows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (stateAt : List (MemoryBusEntry FGL) → SailState)
    (priorRows : List (MemoryBusEntry FGL))
    (h_seed : stateAt [] = initialState)
    (h_coherence : RowTraceCoherence stateAt [] priorRows) :
    ReplayMemoryAgreementOnBytes (stateAt priorRows)
      (replayMemoryAfterBusRows facts.initialMemory priorRows)
      entry.ptr.toNat := by
  have h_seed_agree : ReplayMemoryAgreement (stateAt []) facts.initialMemory := by
    rw [h_seed]; exact facts.initialAgreement
  have h_whole :
      ReplayMemoryAgreement (stateAt ([] ++ priorRows))
        (replayMemoryAfterBusRows facts.initialMemory priorRows) :=
    replayAgreement_of_rowTraceCoherence stateAt [] priorRows
      facts.initialMemory h_seed_agree h_coherence
  intro i _hi
  simpa using h_whole (entry.ptr.toNat + i)

/-- **Full selected-load byte agreement, DERIVED.** Combining the byte-local
agreement (from the store fold) with the read row's `prefixReadSound` (PR#65) gives
the `MemoryTraceAgreement` shape that the local load cores consume — for an opaque
load `state`. This is the PR-76.0 end-to-end deliverable: the load memory
obligation is satisfied from {fold + seed + prefixReadSound} modulo the single
named `RowTraceCoherence` residual. -/
theorem memoryTraceAgreement_of_rowTraceCoherence
    {initialState : SailState}
    {rows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (stateAt : List (MemoryBusEntry FGL) → SailState)
    (priorRows laterRows : List (MemoryBusEntry FGL))
    (h_traceSplit : rows = priorRows ++ entry :: laterRows)
    (h_selectedRead :
      memoryBusTraceEventOfRow entry = some (MemoryBusTraceEvent.read entry))
    (h_seed : stateAt [] = initialState)
    (h_coherence : RowTraceCoherence stateAt [] priorRows) :
    MemoryTraceAgreement (stateAt priorRows) (eventOfEntry entry) := by
  obtain ⟨h_as, h_mult⟩ :=
    read_tags_of_memoryBusTraceEventOfRow_read entry h_selectedRead
  have h_read :
      ReadEventReplayAgreement
        (replayMemoryAfterBusRows facts.initialMemory priorRows)
        (eventOfEntry entry) :=
    facts.prefixReadSound priorRows entry laterRows h_traceSplit h_as h_mult
  exact
    memoryTraceAgreement_of_replayAgreementOnBytes
      (stateAt priorRows)
      (replayMemoryAfterBusRows facts.initialMemory priorRows)
      (eventOfEntry entry)
      (by
        simpa using
          stateBytesAtPrefix_of_rowTraceCoherence (entry := entry)
            facts stateAt priorRows h_seed h_coherence)
      h_read

/-! ## Non-degenerate non-vacuity witness (plan §5 gates 1-4, §7 invariant 4)

A realistic store-then-read same-address segment. The store writes value chunks
`(1, 0)` at byte pointer `100`; the load reads the same address. The Sail state
assignment `stAt` makes the load state differ from the initial state in **both**
`regs` and `cycleCount` — impossible under the frozen whole-state alignment, so
this is genuinely non-degenerate (NOT the empty-prefix `rfl` floor §5 warns about).
The store step is discharged via `rowStep_store_entry` (from the canonical write
transition), and the full `MemoryTraceAgreement` is derived end-to-end. -/

/-- The store row: write `(value_0, value_1) = (1, 0)` at byte pointer `100`. -/
def witnessStoreRow : MemoryBusEntry FGL :=
  { as := 2, ptr := 100, value_0 := 1, value_1 := 0, timestamp := 5, multiplicity := 1 }

/-- The selected read row at the same address, reading the stored value. -/
def witnessReadRow : MemoryBusEntry FGL :=
  { as := 2, ptr := 100, value_0 := 1, value_1 := 0, timestamp := 7, multiplicity := -1 }

/-- The segment's initial Sail state: empty memory, arbitrary regs / choice. -/
def witnessInitState
    (regs0 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) : SailState :=
  { regs := regs0, choiceState := cs0, mem := {}, tags := (),
    cycleCount := 0, sailOutput := #[] }

/-- The cursor-indexed Sail state assignment. The empty prefix is the initial
state; after the store the load cursor's state has the written memory **and** a
mutated `regs` (`regs1`) **and** a bumped `cycleCount` (`99`) — modelling the
store's `nextPC`/register effect, which the byte-local route leaves free. -/
def witnessStateAt
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    List (MemoryBusEntry FGL) → SailState
  | [] => witnessInitState regs0 cs0
  | _ =>
      { regs := regs1, choiceState := cs0,
        mem := writeMemoryOfEntry (witnessInitState regs0 cs0).mem witnessStoreRow,
        tags := (), cycleCount := 99, sailOutput := #[] }

/-- The named trace-coherence residual holds on the witness `[store]` prefix: the
single store step is discharged from the canonical write-entry transition. -/
theorem witness_rowTraceCoherence
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    RowTraceCoherence (witnessStateAt regs0 regs1 cs0) [] [witnessStoreRow] := by
  refine ⟨?_, trivial⟩
  intro mem h_agree
  exact
    rowStep_store_entry
      (witnessStateAt regs0 regs1 cs0 [])
      (witnessStateAt regs0 regs1 cs0 ([] ++ [witnessStoreRow]))
      witnessStoreRow (by simp [witnessStoreRow]) (by simp [witnessStoreRow])
      rfl mem h_agree

/-- **Non-degeneracy (plan §5 gate 2).** Whenever `regs1 ≠ regs0`, the load state's
`regs` and `cycleCount` both differ from the initial state's. This is exactly the
non-frozen case that the whole-state `MemoryPrefixStateAlignment` identity cannot
accommodate, proving the byte-local route is not the laundering `rfl`/frozen floor. -/
theorem witness_nondegenerate
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α)
    (h_regs : regs1 ≠ regs0) :
    (witnessStateAt regs0 regs1 cs0 [witnessStoreRow]).regs
        ≠ (witnessStateAt regs0 regs1 cs0 []).regs
    ∧ (witnessStateAt regs0 regs1 cs0 [witnessStoreRow]).cycleCount
        ≠ (witnessStateAt regs0 regs1 cs0 []).cycleCount := by
  refine ⟨?_, ?_⟩
  · simp [witnessStateAt, witnessInitState, h_regs]
  · simp [witnessStateAt, witnessInitState]

/-- `prefixReadSound` for the witness rows from empty initial memory: the selected
read reads exactly what the store wrote. -/
theorem witness_prefixReadSound :
    MemoryBusRowsPrefixReadSound ({} : Std.ExtHashMap Nat (BitVec 8))
      [witnessStoreRow, witnessReadRow] := by
  intro priorRows row laterRows h_split h_as h_mult
  match priorRows, h_split with
  | [], h =>
      simp only [List.nil_append, List.cons.injEq] at h
      have hr : row = witnessStoreRow := h.1.symm
      rw [hr] at h_mult
      simp only [witnessStoreRow] at h_mult
      exact absurd h_mult (by decide)
  | [a], h =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨ha, hrow, hlater⟩ := h
      subst a; subst row; subst laterRows
      have h_replay :
          replayMemoryAfterBusRows ({} : Std.ExtHashMap Nat (BitVec 8))
              [witnessStoreRow]
            = writeMemoryOfEntry ({} : Std.ExtHashMap Nat (BitVec 8)) witnessStoreRow := by
        simp [replayMemoryAfterBusRows, replayMemoryAfterBusRow, witnessStoreRow,
          replayStoreEvent_storeEventOfEntry]
      rw [h_replay]
      exact
        readEventReplayAgreement_of_writeMemoryOfEntry_same _
          (by simp [witnessReadRow, witnessStoreRow])
          (by simp [witnessReadRow, witnessStoreRow])
          (by simp [witnessReadRow, witnessStoreRow])
  | a :: b :: rest, h =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨_, _, h3⟩ := h
      exact absurd h3.symm (by simp)

/-- The witness initial state agrees with the empty replay memory (seed). -/
theorem witness_initialAgreement
    (regs0 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    ReplayMemoryAgreement (witnessInitState regs0 cs0)
      ({} : Std.ExtHashMap Nat (BitVec 8)) := by
  intro addr; rfl

/-- The generated replay facts for the witness segment. -/
def witnessFacts
    (regs0 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts
      (witnessInitState regs0 cs0) [witnessStoreRow, witnessReadRow] :=
  { initialMemory := {}
    prefixReadSound := witness_prefixReadSound
    initialAgreement := witness_initialAgreement regs0 cs0 }

/-- The selected read row is tagged as a memory read. -/
theorem witness_selectedRead :
    memoryBusTraceEventOfRow witnessReadRow
      = some (MemoryBusTraceEvent.read witnessReadRow) := by
  simp [memoryBusTraceEventOfRow, witnessReadRow]

/-- **End-to-end non-vacuity (plan §5, §7 invariant 4).** On the realistic
store-then-read witness — the load state `witnessStateAt … [witnessStoreRow]` is
variable-bound, and its `regs`/`cycleCount` differ from the initial state — the full
selected-load `MemoryTraceAgreement` is **derived** from the store fold + seed +
`prefixReadSound`, modulo the named `RowTraceCoherence` residual only. This is the
non-degenerate, non-`rfl` witness §5 requires. -/
theorem witness_memoryTraceAgreement
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    MemoryTraceAgreement
      (witnessStateAt regs0 regs1 cs0 [witnessStoreRow])
      (eventOfEntry witnessReadRow) :=
  memoryTraceAgreement_of_rowTraceCoherence
    (entry := witnessReadRow)
    (witnessFacts regs0 cs0)
    (witnessStateAt regs0 regs1 cs0)
    [witnessStoreRow] []
    (by rfl)
    witness_selectedRead
    (by rfl)
    (witness_rowTraceCoherence regs0 regs1 cs0)

#print axioms replayAgreement_of_rowTraceCoherence
#print axioms rowStep_store_entry
#print axioms rowStep_mem_invariant
#print axioms stateBytesAtPrefix_of_rowTraceCoherence
#print axioms memoryTraceAgreement_of_rowTraceCoherence
#print axioms witness_rowTraceCoherence
#print axioms witness_nondegenerate
#print axioms witness_memoryTraceAgreement

end ZiskFv.ZiskCircuit.MemTimeline.Spike
