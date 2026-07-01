import ZiskFv.ZiskCircuit.MemTimeline.CoherenceSpike
import ZiskFv.Airs.Bus.BusEmission
import ZiskFv.Channels.StateEffect

/-!
# Issue #115 Phase-A make-or-break — derive the load memory equation in-export (scratch)

**Exploratory (Phase A of the #115 rewire plan). Built via explicit target, NOT added to the ZiskFv
aggregator. No axioms, no `sorry` at completion.**

Goal: show that `state.mem = replayMemoryAfterBusRows initialMemory priorRows` — the single residual
`CoherenceSpike.loadEvidence_of_loadMemReplay` consumes — is derivable from accepted-trace data plus a
named memory-coherence premise, rather than caller-supplied per load.

Step 1 (this file, first): the store-mem projection — one width-independent lemma that the fold uses
to know what each prior store wrote into the Sail memory. `bus_effect`'s `as=2/mult=1` write branch is
definitionally `writeMemoryOfEntry`, isolated by `bus_effect_matches_sail_store_rrrw`.
-/

namespace ZiskFv.ZiskCircuit.MemTimeline.TraceMemDerivation

open Goldilocks
open Interaction
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.Airs.Bus

/-- Memory of the post-state of a Sail execution result (`none` on error). The fold only cares about
the memory component, so this ignores `regs`/`nextPC`. -/
def resultMem
    (r : EStateM.Result (Sail.Error exception)
      (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult) :
    Option (Std.ExtHashMap Nat (BitVec 8)) :=
  match r with
  | .ok _ s => some s.mem
  | .error _ _ => none

/-- **Store-mem projection.** For any store-shaped bus emission (two register-read entries `e0,e1`
and one memory-write entry `e2`), the post-state memory of `bus_effect` is exactly
`writeMemoryOfEntry state.mem e2`. Width-independent: the `as=2` branch always writes the full eight
lanes; narrow-store width lives on the Sail side, not here. -/
theorem store_bus_effect_mem
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (exec_row : List (ExecutionBusEntry FGL))
    (e0 e1 e2 : MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val)) = nextPC_val)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1)  (h_m2_as : e2.as.val = 2) :
    resultMem (bus_effect exec_row [e0, e1, e2] state).2
      = some (writeMemoryOfEntry state.mem e2) := by
  rw [BusEmission.bus_effect_matches_sail_store_rrrw state exec_row e0 e1 e2 nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [resultMem, writeMemoryOfEntry, Sail.writeReg, PreSail.writeReg, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, bind, pure, EStateM.bind, EStateM.pure]

#print axioms store_bus_effect_mem

/-! ## Step 3 (crux) — the execution-order fold.

The load evidence existentially quantifies its row list `rows`, so we are free to take it in
**execution order** — the per-instruction memory-bus rows concatenated by instruction index — rather
than the Mem AIR's address-major sort. In execution order the whole-map alignment
`(binding i).mem = replay(initialMemory, rows-before-i)` is not only satisfiable but *forced* by a
single named per-step premise: that each Sail step's memory is the replay of that instruction's
memory-bus rows onto the previous step's memory. Given that premise (`h_step`, the mem-projected
execution-successor) and the boot seed (`h_boot`), the alignment is a one-line induction. -/
theorem exec_order_fold
    (binding : ℕ → SailState)
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_boot : (binding 0).mem = initialMemory)
    (h_step : ∀ j, (binding (j + 1)).mem
        = replayMemoryAfterBusRows (binding j).mem (rowsOf j)) :
    ∀ i, (binding i).mem
        = replayMemoryAfterBusRows initialMemory ((List.range i).flatMap rowsOf) := by
  intro i
  induction i with
  | zero => simpa using h_boot
  | succ k ih =>
      rw [h_step k, ih, List.range_succ, List.flatMap_append]
      simp

#print axioms exec_order_fold

/-! ## Step 4 (crux, end-to-end) — the fold discharges the load evidence.

Composing `exec_order_fold` with `CoherenceSpike.loadEvidence_of_loadMemReplay`: for a load at
execution position `i` whose read row sits after the execution-order prefix `(range i).flatMap rowsOf`,
the full `LoadMemoryTimelineCoherenceEvidence` is discharged from the named boot seed + execution-
successor premise, the trace's read-soundness over the execution-order rows, and the structural fact
that the load's read row is at position `i`. This CLOSES the crux modulo exactly:
* `h_boot`, `h_step` — the named boot seed + mem-projected execution-successor (the honest external
  trust, to become the new `root_soundness` binder);
* `prefixReadSound` over the execution-order rows — the read-soundness reconciliation (Phase-B
  plumbing: reconcile the Mem AIR's address-major read-soundness with execution order);
* `h_rows_split` — the load's read row is at execution position `i` (a structural trace fact). -/
theorem loadEvidence_of_execOrder
    (binding : ℕ → SailState)
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_boot : (binding 0).mem = initialMemory)
    (h_step : ∀ j, (binding (j + 1)).mem
        = replayMemoryAfterBusRows (binding j).mem (rowsOf j))
    (i : ℕ) (entry : MemoryBusEntry FGL) (laterRows rows : List (MemoryBusEntry FGL))
    (h_rows_split : rows = (List.range i).flatMap rowsOf ++ entry :: laterRows)
    (h_readSound : MemoryBusRowsPrefixReadSound initialMemory rows) :
    ZiskFv.Compliance.LoadMemoryTimelineCoherenceEvidence (binding i) entry := by
  refine CoherenceSpike.loadEvidence_of_loadMemReplay
    (initialState := binding 0)
    (facts :=
      { initialMemory := initialMemory
        prefixReadSound := h_readSound
        initialAgreement := fun addr => by rw [h_boot] })
    (priorRows := (List.range i).flatMap rowsOf) (laterRows := laterRows)
    h_rows_split ?_
  -- h_load_mem : (binding i).mem = replay initialMemory ((range i).flatMap rowsOf)
  exact exec_order_fold binding initialMemory rowsOf h_boot h_step i

#print axioms loadEvidence_of_execOrder

/-! ## Step 1 (Phase B) — single-address read agreement from the last same-address write.

The read-soundness `loadEvidence_of_execOrder` needs — `ReadEventReplayAgreement (replay im rows) entry`
for the execution-order rows — reduces to: the last active write to the read's address matches the
read's value, and every row after it is byte-disjoint from the read. This is the projection that lets
us reuse the Mem AIR's read-soundness in execution order without a whole-map permutation argument. -/
theorem readAgreement_of_lastSameAddrWrite
    (im : Std.ExtHashMap Nat (BitVec 8))
    (before after : List (MemoryBusEntry FGL))
    (writeEntry entry : MemoryBusEntry FGL)
    (h_write_as : writeEntry.as = (2 : FGL)) (h_write_mult : writeEntry.multiplicity = (1 : FGL))
    (h_ptr : entry.ptr = writeEntry.ptr)
    (h_v0 : entry.value_0 = writeEntry.value_0) (h_v1 : entry.value_1 = writeEntry.value_1)
    (h_after_disjoint : ∀ row ∈ after, MemoryBusEntryByteDisjoint entry row) :
    ReadEventReplayAgreement
      (replayMemoryAfterBusRows im (before ++ writeEntry :: after)) (eventOfEntry entry) := by
  rw [replayMemoryAfterBusRows_append]
  show ReadEventReplayAgreement
    (replayMemoryAfterBusRows
      (replayMemoryAfterBusRow (replayMemoryAfterBusRows im before) writeEntry) after)
    (eventOfEntry entry)
  rw [replayMemoryAfterBusRow, if_pos h_write_as, if_pos h_write_mult,
    replayStoreEvent_storeEventOfEntry]
  refine readEventReplayAgreement_of_replayMemoryAfterBusRows_disjoint ?_ h_after_disjoint
  exact readEventReplayAgreement_of_writeMemoryOfEntry_same _ h_ptr h_v0 h_v1

#print axioms readAgreement_of_lastSameAddrWrite

/-! ## Phase B — Fin-indexed fold + range split for the real trace.

The live `binding : SailTrace n = Fin n → SailState` is Fin-indexed, so `exec_order_fold` (ℕ-indexed)
needs a Fin-aware sibling. And the load's single memory row sits at a clean `flatMap` boundary of the
full execution-order row list, so the evidence's existential `rows` split is a `List.range` split. -/

/-- Fin-indexed execution-order fold: the Sail memory at instruction `i` is the replay of every
strictly-earlier instruction's memory rows, from the boot memory. -/
theorem exec_order_fold_fin
    {n : ℕ} (binding : Fin n → SailState)
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h0 : 0 < n)
    (h_boot : (binding ⟨0, h0⟩).mem = initialMemory)
    (h_step : ∀ (j : ℕ) (h : j + 1 < n),
        (binding ⟨j + 1, h⟩).mem
          = replayMemoryAfterBusRows (binding ⟨j, Nat.lt_of_succ_lt h⟩).mem (rowsOf j)) :
    ∀ (i : Fin n),
      (binding i).mem
        = replayMemoryAfterBusRows initialMemory ((List.range i.val).flatMap rowsOf) := by
  suffices H : ∀ iv (hi : iv < n),
      (binding ⟨iv, hi⟩).mem
        = replayMemoryAfterBusRows initialMemory ((List.range iv).flatMap rowsOf) by
    intro i; simpa using H i.val i.isLt
  intro iv
  induction iv with
  | zero => intro hi; simpa using h_boot
  | succ k ih =>
      intro hi
      have hk : k < n := Nat.lt_of_succ_lt hi
      rw [h_step k hi, ih hk, List.range_succ, List.flatMap_append]
      simp

#print axioms exec_order_fold_fin

/-- The full execution-order row list splits at instruction `i` whose memory row list is a single
entry: everything before `i`, then that entry, then the rest. Used to instantiate the evidence's
existential `rows`/`priorRows`/`laterRows` at the load's read. -/
theorem exists_flatMap_range_split_of_singleton
    {n : ℕ} (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (i : ℕ) (hi : i < n) (entry : MemoryBusEntry FGL)
    (h_row : rowsOf i = [entry]) :
    ∃ laterRows,
      (List.range n).flatMap rowsOf
        = (List.range i).flatMap rowsOf ++ entry :: laterRows := by
  refine ⟨((List.range (n - (i + 1))).map (fun x => i + 1 + x)).flatMap rowsOf, ?_⟩
  have hn : n = (i + 1) + (n - (i + 1)) := by omega
  have hsplit :
      List.range n = List.range i ++ i :: (List.range (n - (i + 1))).map (fun x => i + 1 + x) := by
    conv_lhs => rw [hn, List.range_add, List.range_succ]
    simp [List.append_assoc]
  rw [hsplit, List.flatMap_append, List.flatMap_cons, h_row]
  simp

#print axioms exists_flatMap_range_split_of_singleton

end ZiskFv.ZiskCircuit.MemTimeline.TraceMemDerivation
