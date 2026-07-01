import ZiskFv.Compliance.OpEnvelope

/-!
# Issue #115 — collapse the load/store `RowTraceCoherence` floor to one memory-replay equation

**Status: exploratory reduction study (make-or-break feasibility for #115). Not imported by any
canonical theorem, `Compliance`, or `root_soundness`. No axioms, no `sorry`.**

Issue #115 asks us to eliminate the load memory *trace-coherence floor*: the load memory
obligation `LoadMemoryTimelineCoherenceEvidence` (`ZiskFv/Compliance/OpEnvelope.lean`)
existentially quantifies an opaque cursor-indexed Sail-state assignment `stateAt` and demands the
per-row memory chain `RowTraceCoherence stateAt [] priorRows`. The only concrete discharge today
(`trust/consistency/global_theorem_instantiation_ld.lean`) cheats with `priorRows = []`, so
`RowTraceCoherence … [] [] = True`.

## What this module proves (the reduction)

For a *fixed* memory-bus prefix, the whole opaque `∃ stateAt, … ∧ RowTraceCoherence` bundle is
**equivalent** to a single, mem-only equation:

> `state.mem = replayMemoryAfterBusRows initialMemory priorRows`

i.e. *the load's Sail memory is the replay of exactly the memory-bus writes that chronologically
precede the load's read row*. This is the issue's own target phrasing ("so the Sail memory
sequence is the replay of the trace's memory writes"), and it is:

* **mem-only** — `regs`/PC/`cycleCount`/… stay free (not the whole-`SailState` identity #76 replaced);
* **not opaque** — no existential `stateAt`, no per-row `RowTraceCoherence` chain;
* **not stronger** than the current evidence — the two are proven equivalent below
  (`loadEvidence_of_loadMemReplay` ⟸, `loadMemReplay_of_loadEvidence` ⟹), so this is a genuine
  reduction of the residual's *shape*, not a strengthening (anti-laundering trap #3).

`prefixReadSound` (PR#65 — the actual "the load reads the right bytes" content) is carried through
untouched: the reduction reuses the caller's `GeneratedMemReplayFacts.initialMemory` /
`prefixReadSound`, only re-choosing the *state-side* existentials.

## What remains (the honest residual, for the deferred rewire)

The equation `state.mem = replayMemoryAfterBusRows initialMemory priorRows` is manifestly a
`List.foldl` over the memory-bus rows. At the deferred `root_soundness` rewire it is *derived*, not
posited, from: the accepted trace's memory-bus rows (`channels_balanced` + Mem AIR ordering),
per-op store soundness (`state_effect_via_channels` writes `writeMemoryOfEntry`), a boot seed, and
a named *execution-successor* premise (the Sail states are a genuine execution sequence). Those
named premises are the same external-trust class as channel-balance; this module does not wire them.

## Store side (#119 / #185)

`StoreRmwMemoryCoherenceEvidence` shares the *identical* `RowTraceCoherence` core plus one extra
posited conjunct `StoreRmwPreservedBytesAtPrefix`. The same reduction discharges the store core
(`storeEvidence_of_loadMemReplay`), confirming the preserved-byte conjunct (→ #185) is the *only*
store-specific residual.
-/

namespace ZiskFv.ZiskCircuit.MemTimeline.CoherenceSpike

open Goldilocks
open Interaction
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.ZiskCircuit.MemTimeline.Spike
open ZiskFv.Compliance

/-! ## Step 1 — pin the target: the two evidence types and the floor. -/

-- The load memory obligation (`OpEnvelope.lean`): opaque `∃ stateAt … ∧ RowTraceCoherence`.
#check @LoadMemoryTimelineCoherenceEvidence
-- The store analogue: identical core plus the extra `StoreRmwPreservedBytesAtPrefix` conjunct.
#check @StoreRmwMemoryCoherenceEvidence
#check @StoreRmwPreservedBytesAtPrefix
-- The floor `trust/consistency/global_theorem_instantiation_ld.lean` picks `priorRows = []`, so
-- `RowTraceCoherence … [] [] = True`.  This module replaces that with a nonempty-prefix route.

/-! ## Step 3 — the fold: a uniform replay-memory `stateAt` satisfies `RowTraceCoherence`.

Choosing `stateAt X := { base with mem := replayMemoryAfterBusRows im X }` makes every
`RowTraceCoherence` step definitional: a store row's memory transition is
`replayMemoryAfterBusRow`, which unfolds to `writeMemoryOfEntry` (`replayStoreEvent_storeEventOfEntry`)
— exactly the shape `rowStep_store_entry` consumes; a non-store row leaves the map fixed
(`rowStep_mem_invariant`). No opaque residual survives the choice. -/
theorem rowTraceCoherence_of_uniformReplayMem
    (base : SailState) (im : Std.ExtHashMap Nat (BitVec 8)) :
    ∀ (done rows : List (MemoryBusEntry FGL)),
      RowTraceCoherence (fun X => { base with mem := replayMemoryAfterBusRows im X }) done rows := by
  intro done rows
  induction rows generalizing done with
  | nil => trivial
  | cons row rest ih =>
      refine ⟨?_, ih (done ++ [row])⟩
      intro mem h_agree
      by_cases h : row.as = (2 : FGL) ∧ row.multiplicity = (1 : FGL)
      · refine rowStep_store_entry _ _ row h.1 h.2 ?_ mem h_agree
        show replayMemoryAfterBusRows im (done ++ [row])
            = writeMemoryOfEntry (replayMemoryAfterBusRows im done) row
        rw [replayMemoryAfterBusRows_append]
        show replayMemoryAfterBusRow (replayMemoryAfterBusRows im done) row
            = writeMemoryOfEntry (replayMemoryAfterBusRows im done) row
        rw [replayMemoryAfterBusRow, if_pos h.1, if_pos h.2, replayStoreEvent_storeEventOfEntry]
      · refine rowStep_mem_invariant _ _ row h ?_ mem h_agree
        show replayMemoryAfterBusRows im (done ++ [row]) = replayMemoryAfterBusRows im done
        rw [replayMemoryAfterBusRows_append]
        show replayMemoryAfterBusRow (replayMemoryAfterBusRows im done) row
            = replayMemoryAfterBusRows im done
        unfold replayMemoryAfterBusRow
        by_cases h_as : row.as = (2 : FGL)
        · by_cases h_w : row.multiplicity = (1 : FGL)
          · exact absurd ⟨h_as, h_w⟩ h
          · simp [h_as, h_w]
        · simp [h_as]

/-! ## Step 3/5 — the reduction: the clean equation *implies* the full evidence.

`loadEvidence_of_loadMemReplay` discharges the entire opaque `LoadMemoryTimelineCoherenceEvidence`
from `state.mem = replayMemoryAfterBusRows facts.initialMemory priorRows`, re-choosing the state-side
existentials as `initialState := { state with mem := initialMemory }` and the uniform `stateAt`
above (so the seed pin is `rfl` and the state pin is the equation). The read content
(`prefixReadSound`) is inherited from the caller's `facts`. -/
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
  · -- seed pin: stateAt [] = { state with mem := im }
    show ({ state with mem := replayMemoryAfterBusRows im [] } : SailState)
        = { state with mem := im }
    rfl
  · -- state pin: stateAt priorRows = state
    show ({ state with mem := replayMemoryAfterBusRows im priorRows } : SailState) = state
    rw [← h_load_mem]

/-! The store evidence's `RowTraceCoherence` core is discharged by the *same* reduction; the only
extra obligation is the posited preserved-byte conjunct (#185), passed through here as an explicit
hypothesis so this module shows it is the sole store-specific residual. -/
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

/-! ## Step 6 (assessment) — the converse: the evidence *implies* the clean equation.

Together with `loadEvidence_of_loadMemReplay` this proves the residual is *equivalent* to the
existing evidence (for the witnessed prefix), so the reduction does not smuggle in a stronger
premise. The endpoint agreement is folded out of `RowTraceCoherence` by the existing
`replayAgreement_of_rowTraceCoherence` (the seed transported through the per-store steps). -/
theorem loadMemReplay_of_loadEvidence
    {state : SailState} {entry : MemoryBusEntry FGL}
    (h : LoadMemoryTimelineCoherenceEvidence state entry) :
    ∃ (initialState : SailState) (rows : List (MemoryBusEntry FGL))
      (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
      (priorRows laterRows : List (MemoryBusEntry FGL)),
      rows = priorRows ++ entry :: laterRows ∧
      ReplayMemoryAgreement state (replayMemoryAfterBusRows facts.initialMemory priorRows) := by
  obtain ⟨initialState, rows, facts, stateAt, priorRows, laterRows,
    h_split, h_seed, h_state, h_coh⟩ := h
  refine ⟨initialState, rows, facts, priorRows, laterRows, h_split, ?_⟩
  have h_seed_agree : ReplayMemoryAgreement (stateAt []) facts.initialMemory := by
    rw [h_seed]; exact facts.initialAgreement
  have h_end :=
    replayAgreement_of_rowTraceCoherence stateAt [] priorRows facts.initialMemory h_seed_agree h_coh
  rw [List.nil_append, h_state] at h_end
  exact h_end

/-- Pointwise form of the reduction: the `ReplayMemoryAgreement` residual — the *exact* form
`loadMemReplay_of_loadEvidence` produces — also discharges the evidence, via `ExtHashMap`
extensionality (`Std.ExtHashMap.ext_getElem?`). Paired with `loadMemReplay_of_loadEvidence` this
closes the equivalence in the *same* form both ways, so the reduction provably does not smuggle in a
stronger premise (anti-laundering trap #3). -/
theorem loadEvidence_of_replayAgreement
    {state initialState : SailState}
    {rows priorRows laterRows : List (MemoryBusEntry FGL)}
    {entry : MemoryBusEntry FGL}
    (facts : ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts initialState rows)
    (h_split : rows = priorRows ++ entry :: laterRows)
    (h_agree :
      ReplayMemoryAgreement state (replayMemoryAfterBusRows facts.initialMemory priorRows)) :
    LoadMemoryTimelineCoherenceEvidence state entry :=
  loadEvidence_of_loadMemReplay facts h_split
    (Std.ExtHashMap.ext_getElem? (fun addr => h_agree addr))

/-! ## Step 4 — non-floor witness (make-or-break).

A concrete instance where `priorRows` is **nonempty** (`[witnessStoreRow]`), the load state's `mem`
is the replay of that prior store, and its `regs`/`cycleCount` differ from the segment initial
state — exactly the case the empty-prefix floor cannot express.  The full
`LoadMemoryTimelineCoherenceEvidence` is produced through `loadEvidence_of_loadMemReplay`. -/

/-- The load state on the witness: the store's written memory, with mutated regs/cycleCount. -/
def witnessLoadState
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) : SailState :=
  { regs := regs1, choiceState := cs0,
    mem := replayMemoryAfterBusRows (witnessFacts regs0 cs0).initialMemory [witnessStoreRow],
    tags := (), cycleCount := 99, sailOutput := #[] }

/-- **Make-or-break:** a genuine `LoadMemoryTimelineCoherenceEvidence` on a nonempty prefix,
derived from the clean equation — not the `priorRows = []` floor. -/
theorem witness_loadEvidence_nonempty_prefix
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α) :
    LoadMemoryTimelineCoherenceEvidence
      (witnessLoadState regs0 regs1 cs0) witnessReadRow :=
  loadEvidence_of_loadMemReplay
    (facts := witnessFacts regs0 cs0)
    (priorRows := [witnessStoreRow]) (laterRows := [])
    (by rfl)
    rfl

/-- The witness load state genuinely differs from the segment initial state in `regs` and
`cycleCount` — so this is not the frozen/`rfl` floor. -/
theorem witness_nondegenerate
    (regs0 regs1 : Std.ExtDHashMap Register RegisterType)
    (cs0 : Sail.trivialChoiceSource.α)
    (h_regs : regs1 ≠ regs0) :
    (witnessLoadState regs0 regs1 cs0).regs ≠ (witnessInitState regs0 cs0).regs
    ∧ (witnessLoadState regs0 regs1 cs0).cycleCount ≠ (witnessInitState regs0 cs0).cycleCount := by
  refine ⟨?_, ?_⟩
  · simpa [witnessLoadState, witnessInitState] using h_regs
  · simp [witnessLoadState, witnessInitState]

#print axioms rowTraceCoherence_of_uniformReplayMem
#print axioms loadEvidence_of_loadMemReplay
#print axioms storeEvidence_of_loadMemReplay
#print axioms loadMemReplay_of_loadEvidence
#print axioms loadEvidence_of_replayAgreement
#print axioms witness_loadEvidence_nonempty_prefix
#print axioms witness_nondegenerate

end ZiskFv.ZiskCircuit.MemTimeline.CoherenceSpike
