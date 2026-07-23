import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence
import ZiskFv.Compliance.AcceptedZiskTrace.MemProviders
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.TraceLevelExport.Dispatcher
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import Mathlib.Data.List.Perm.Subperm

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
* `step` — the per-step **execution-successor**: each Sail step's memory is the replay of that
  step's memory-bus rows onto the previous step's memory (cross-row memory coherence);
* `readSoundInputs` — narrow, nonsemantic replay/order inputs from which memory-bus
  **read-soundness** over the whole execution-order row list is derived for nonempty segments.  This
  keeps the accepted Mem replay bridge, the explicit boot/cross-segment initial-memory bridge, and
  the replay-safe order-transfer certificate visible instead of carrying raw read-soundness;
* `placement` — the *structural* tie pinning `rowsOf i` to each op's real memory-bus rows: loads
  use their read `busLd .. .e1`, stores use their write `busSt .. .e2`, non-memory ops emit no rows,
  and narrow stores additionally carry their preserved-byte prefix fact.

`memEvidence_of_bootSeed` derives each op's `MemoryOpEvidenceFor` residual by the execution-order fold
(`Spike.exec_order_fold_fin` gives the per-op state pin from `boot` + `step`;
`Spike.exists_flatMap_range_split_of_singleton` locates the op's row; `loadEvidence_of_loadMemReplay` /
`storeEvidence_of_loadMemReplay` build the evidence).

This is a **constructibility restatement, net-zero-to-marginally-stronger on trust** — NOT a
reduction — versus #185's free-`stateAt` / `RowTraceCoherence` form.
`Spike.rowTraceCoherence_of_uniformReplayMem` mechanizes only the reconstruction direction
(`step + boot` ⟹ the uniform-replay cursor satisfies `RowTraceCoherence`; there is no converse), and
the concrete `step` pins `binding.mem` at *every* index where the free-cursor chain tied it only at
memory-op indices — a difference real traces satisfy trivially (no vacuity).  The value is
*constructibility*: the memory premise is now concrete, with no free `stateAt` existential, no
whole-sequence `RowTraceCoherence`, and no raw read-soundness predicate on the assumed surface.  The
read-soundness half is assembled from accepted Mem replay evidence plus explicit initial-memory and
replay-safe order bridges. -/

namespace ZiskFv.Compliance

open Interaction
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.ZiskCircuit.MemTimeline.Spike

variable {numInstructions : Nat}

/-! ## Accepted Mem replay chronology wrappers -/

/-- Accepted-trace wrapper for generated same-address chronology: an active
replay entry from a strictly prior generated Mem row at the same address is
chronologically no later than any active replay entry from the selected row. -/
theorem acceptedMemReplayRows_prior_same_addr_timestamp_le_active
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {h_present : MutableMemPresent ziskTrace.witness}
    (priorIdx selectedIdx :
      Fin (ziskTrace.memReplayBridge h_present).table.table.length)
    (h_prior_lt : priorIdx.val < selectedIdx.val)
    (h_addr_eq :
      (ziskTrace.memReplayBridge h_present).mem.addr priorIdx.val =
        (ziskTrace.memReplayBridge h_present).mem.addr selectedIdx.val)
    {priorEntry selectedEntry : MemoryBusEntry FGL}
    (h_prior_entry :
      priorEntry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem priorIdx.val))
    (h_selected_entry :
      selectedEntry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem selectedIdx.val)) :
    priorEntry.timestamp.toNat ≤ selectedEntry.timestamp.toNat :=
  prior_activeMemReplayEntry_timestamp_le_activeMemReplayEntry_of_fullWitnessMemReplayBridge_same_addr
    (ziskTrace.memReplayBridge h_present)
    priorIdx selectedIdx h_prior_lt h_addr_eq h_prior_entry h_selected_entry

/-- Accepted-trace wrapper for active replay-row membership: any accepted Mem
replay row comes from some generated Mem row's active replay projection. -/
theorem acceptedMemReplayRows_exists_active_rowAt
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {h_present : MutableMemPresent ziskTrace.witness}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_present) :
    ∃ idx : Fin (ziskTrace.memReplayBridge h_present).table.table.length,
      entry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem idx.val) :=
  exists_activeMemReplayEntry_rowAt_of_fullWitnessMemReplayBridge
    (ziskTrace.memReplayBridge h_present) h_entry

/-- Accepted-trace wrapper for Mem-source chronology within one byte pointer:
accepted active replay rows are ordered by nondecreasing timestamps whenever
their byte pointers agree. -/
theorem acceptedMemReplayRows_pairwise_timestamp_toNat_le_of_same_ptr
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {h_present : MutableMemPresent ziskTrace.witness} :
    (ziskTrace.memReplayRows h_present).Pairwise
      (fun earlier later =>
        earlier.ptr.toNat = later.ptr.toNat →
          earlier.timestamp.toNat ≤ later.timestamp.toNat) :=
  activeMemReplayRows_pairwise_timestamp_toNat_le_of_same_ptr_of_fullWitnessMemReplayBridge
    (ziskTrace.memReplayBridge h_present)

/-- Accepted-trace wrapper for the different-address crossing case: active
replay entries from different generated Mem addresses are bidirectionally safe
for replay-safe adjacent swaps. -/
theorem acceptedMemReplayRows_noActiveWriteOverlap_of_addr_ne
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {h_present : MutableMemPresent ziskTrace.witness}
    (leftIdx rightIdx :
      Fin (ziskTrace.memReplayBridge h_present).table.table.length)
    {leftEntry rightEntry : MemoryBusEntry FGL}
    (h_left :
      leftEntry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem leftIdx.val))
    (h_right :
      rightEntry ∈ activeMemReplayEntriesOfRow
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem rightIdx.val))
    (h_addr_ne :
      (ziskTrace.memReplayBridge h_present).mem.addr leftIdx.val ≠
        (ziskTrace.memReplayBridge h_present).mem.addr rightIdx.val) :
    MemoryBusEntryNoActiveWriteOverlap leftEntry rightEntry ∧
      MemoryBusEntryNoActiveWriteOverlap rightEntry leftEntry :=
  activeMemReplayEntry_noActiveWriteOverlap_of_fullWitnessMemReplayBridge_addr_ne
    (ziskTrace.memReplayBridge h_present)
    leftIdx rightIdx h_left h_right h_addr_ne

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

/-- Explicit structural certificate for sorted-to-execution replay order.

This states that the execution-order memory rows are obtainable from the
accepted Mem replay rows by replay-safe adjacent swaps. It is not a read-value
agreement predicate. The #115 direct-Mem path derives this certificate from
scoped source/target chronology plus the named row-count certificate; the generic
seed API keeps the order certificate as the reusable assembly boundary. -/
abbrev BootSegmentReplaySafeOrderCertificate
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_present : MutableMemPresent ziskTrace.witness) : Prop :=
  MemoryBusRowsReplaySafePermutation
    (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (ziskTrace.memReplayBridge h_present)).rows
    ((List.range ziskTrace.numInstructions).flatMap rowsOf)

/-- A plain accepted-replay/execution row permutation becomes a boot order
certificate when every accepted replay row can cross every other accepted
replay row safely.

This bridge is intentionally strong. Same-address mixed write/read rows usually
need a sharper no-crossing argument rather than an all-pairs safety proof. -/
theorem bootSegmentReplaySafeOrderCertificate_of_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_present := by
  have h_perm_rows :
      (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
        (ziskTrace.memReplayBridge h_present)).rows.Perm
        ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
    simpa [AcceptedZiskTrace.memReplayRows, AcceptedZiskTrace.memReplayBridge] using h_perm
  refine
    MemoryBusRowsReplaySafePermutation.of_perm_pairwise_noActiveWriteOverlap
      h_perm_rows ?_
  intro left h_left right h_right
  exact h_safe left
    (by
      simpa [AcceptedZiskTrace.memReplayRows, AcceptedZiskTrace.memReplayBridge] using h_left)
    right
    (by
      simpa [AcceptedZiskTrace.memReplayRows, AcceptedZiskTrace.memReplayBridge] using h_right)

/-- Nonsemantic inputs needed to derive execution-order seed read-soundness
from accepted Mem replay evidence.

The accepted trace supplies the guarded Mem replay bridge. `initialMemory_eq` is
the explicit boot/cross-segment memory bridge. `order` is the named structural
order-transfer certificate `BootSegmentReplaySafeOrderCertificate`. -/
structure BootSegmentReadSoundInputs
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_present : MutableMemPresent ziskTrace.witness) : Type 2 where
  initialMemory_eq :
    memInit =
      (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
        (ziskTrace.memReplayBridge h_present)).initialMemory
  order : BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_present

/-- Build seed read-soundness inputs from pairwise-safe permutation evidence. -/
def bootSegmentReadSoundInputs_of_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order :=
    bootSegmentReplaySafeOrderCertificate_of_perm_pairwise_noActiveWriteOverlap
      h_perm h_safe

/-- Assemble the exact seed-level execution-order read-soundness predicate from
accepted Mem replay evidence plus the explicit initial-memory and order-transfer
bridges. -/
theorem readSound_of_bootSegmentReadSoundInputs
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  let acceptedReplay :=
    ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (ziskTrace.memReplayBridge h_present)
  have h_prefix :
      MemoryBusRowsPrefixReadSound
        acceptedReplay.initialMemory
        ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
    memoryBusRowsPrefixReadSound_of_replaySafePermutation
      acceptedReplay.initialMemory inputs.order acceptedReplay.prefixReadSound
  rwa [inputs.initialMemory_eq]

/-- Direct read-soundness assembly from pairwise-safe permutation evidence plus
the explicit initial-memory bridge. -/
theorem readSound_of_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_perm_pairwise_noActiveWriteOverlap
      h_initialMemory h_perm h_safe)

/-- Rows in the accepted Mem replay source occur in the execution-order row list
selected by the seed's replay-safe order certificate. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_memReplayRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_present) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  have h_source :
      entry ∈
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (ziskTrace.memReplayBridge h_present)).rows := by
    simpa [AcceptedZiskTrace.memReplayBridge, AcceptedZiskTrace.memReplayRows] using h_entry
  exact inputs.order.mem_target_of_mem_source h_source

/-- The replay-safe order certificate exposes the bag/permutation equality
between accepted Mem replay rows and execution-order rows. -/
theorem BootSegmentReadSoundInputs.memReplayRows_perm_executionRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present) :
    (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  simpa [BootSegmentReplaySafeOrderCertificate, AcceptedZiskTrace.memReplayBridge,
    AcceptedZiskTrace.memReplayRows] using inputs.order.perm

/-- The replay-safe order certificate preserves the row-list length, exposing a
duplicate-sensitive consequence of the accepted replay/execution-order bag
equality. -/
theorem BootSegmentReadSoundInputs.memReplayRows_length_eq_executionRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present) :
    (ziskTrace.memReplayRows h_present).length =
      ((List.range ziskTrace.numInstructions).flatMap rowsOf).length := by
  simpa [BootSegmentReplaySafeOrderCertificate, AcceptedZiskTrace.memReplayBridge,
    AcceptedZiskTrace.memReplayRows] using inputs.order.length_eq

/-- The replay-safe order certificate preserves the multiplicity of each
concrete memory-bus row, which is the duplicate-sensitive row-correspondence
fact needed beyond mere membership. -/
theorem BootSegmentReadSoundInputs.memReplayRows_count_eq_executionRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (entry : MemoryBusEntry FGL) :
    (ziskTrace.memReplayRows h_present).count entry =
      ((List.range ziskTrace.numInstructions).flatMap rowsOf).count entry := by
  simpa [BootSegmentReplaySafeOrderCertificate, AcceptedZiskTrace.memReplayBridge,
    AcceptedZiskTrace.memReplayRows] using inputs.order.count_eq entry

/-- Execution-order rows are accepted Mem replay rows when viewed through the
explicit replay-safe order certificate. This is the reverse membership direction
needed by row-correspondence callers that start from `rowsOf`. -/
theorem BootSegmentReadSoundInputs.memReplayRows_of_mem_executionRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  (inputs.memReplayRows_perm_executionRows.mem_iff).mpr h_entry

/-- Accepted mutable-Mem provider coverage plus the seed order certificate
places the selected active Main memory entry in execution order.

The remaining hypotheses are syntactic/certificate residues: exclusion of
non-mutable providers for this Main message and the explicit replay-safe order
certificate already carried by `inputs`. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_activeMainMutableMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ ziskTrace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ ziskTrace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (ziskTrace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_mem_op :
      (eval (ziskTrace.mainTable.environment mainRow) mainMsg).mem_op = 1)
    {entry : MemoryBusEntry FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable mainRow mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (ziskTrace.mainTable.environment mainRow) mainMsg) (-1) 2)) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.activeMainMutableMemProviderEntryMemOfReplayBridge_of_main_mem_op_one
      h_present h_mainRow h_mainInteraction h_mainEval h_active h_main_mem_op
      h_no_nonmutable h_entry)

/-- Store analogue of
`BootSegmentReadSoundInputs.mem_executionRows_of_activeMainMutableMemProviderEntry`.

The Clean Main interaction is an active pull (`mult = -1`), while the legacy
execution row is a write row (`multiplicity = 1`, `as = 2`). -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_activeMainMutableStoreMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ ziskTrace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ ziskTrace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (ziskTrace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_mem_op :
      (eval (ziskTrace.mainTable.environment mainRow) mainMsg).mem_op = 2)
    {entry : MemoryBusEntry FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable mainRow mainInteraction mainMsg 1 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (ziskTrace.mainTable.environment mainRow) mainMsg) 1 2)) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.activeMainMutableMemProviderEntryMemOfReplayBridge_of_main_mem_op_two
      h_present h_mainRow h_mainInteraction h_mainEval h_active h_main_mem_op
      h_no_nonmutable h_entry)

@[reducible] noncomputable def loadBMemMainRow
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Array FGL :=
  ziskTrace.mainTable.table.get ⟨i.val, ziskTrace.mainTable_index i⟩

@[reducible] noncomputable def storeCMemMainRow
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Array FGL :=
  ziskTrace.mainTable.table.get ⟨i.val, ziskTrace.mainTable_index i⟩

@[reducible] def loadBMemMainMessage
    (ziskTrace : AcceptedZiskTrace numInstructions) :
    ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL) :=
  ZiskFv.AirsClean.Main.bMemMessageExpr
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
      ziskTrace.programLength ziskTrace.program).rowInputVar

@[reducible] def storeCMemMainMessage
    (ziskTrace : AcceptedZiskTrace numInstructions) :
    ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL) :=
  ZiskFv.AirsClean.Main.cMemMessageExpr
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
      ziskTrace.programLength ziskTrace.program).rowInputVar

@[reducible] def loadBMemMainMultiplicity
    (ziskTrace : AcceptedZiskTrace numInstructions) : Expression FGL :=
  -((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_mem
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_ind
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_reg)

@[reducible] def storeCMemMainMultiplicity
    (ziskTrace : AcceptedZiskTrace numInstructions) : Expression FGL :=
  -((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_mem
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_ind
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_reg)

@[reducible] noncomputable def loadBMemMainInteraction
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Interaction FGL :=
  (((MemBusChannel.emitted (loadBMemMainMultiplicity ziskTrace)
    (loadBMemMainMessage ziskTrace)).toRaw).eval
    (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i)))

@[reducible] noncomputable def storeCMemMainInteraction
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Interaction FGL :=
  (((MemBusChannel.emitted (storeCMemMainMultiplicity ziskTrace)
    (storeCMemMainMessage ziskTrace)).toRaw).eval
    (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i)))

/-- Load-`b` specialization of the selected general-MemAlign prove-branch
pins. This names the remaining syntactic residue needed to follow a general
MemAlign provider row; byte-provider branches are handled separately. -/
abbrev LoadBSelectedMemAlignPins
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Prop :=
  ActiveMainMemAlignSelectedProveBranchPins ziskTrace.witness
    (loadBMemMainInteraction ziskTrace i)

/-- Load-`b` specialization of the explicit general-MemAlign ROM/value residue
needed to turn a structural provider row into the legacy subdoubleword provider
witness. -/
abbrev LoadBMemAlignRomValueFacts
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (entry : MemoryBusEntry FGL) : Prop :=
  MemAlignLoadProviderRomValueFacts ziskTrace.program ziskTrace.witness
    main r_main entry

/-- Trace-level form of the narrow-load defect boundary for every legacy entry
matching the concrete Main load-`b` row.  `RowOutsideDefectRegion` supplies
this at the dispatcher; it is not a provider-side or caller-supplied data fact. -/
abbrev LoadBNoMemAlignNarrowLoadLaneForge
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Prop :=
  ∀ entry,
    ZiskFv.Airs.MemoryBus.matches_memory_entry
      (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
    ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness entry

/-- Extend the dispatcher-provided selected-entry exclusion across the legacy
    equality-shaped memory-entry adapter used by the load-provider bridge. -/
theorem loadBNoMemAlignNarrowLoadLaneForge_of_selected
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    (h_selected :
      ¬ Defects.MemAlignNarrowLoadLaneForge ziskTrace.program ziskTrace.witness
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1) :
    LoadBNoMemAlignNarrowLoadLaneForge ziskTrace i := by
  intro entry h_match
  have h_eq : (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 = entry :=
    ZiskFv.ZiskCircuit.MemTimeline.eq_of_matches_memory_entry h_match
  rw [← h_eq]
  exact h_selected

/-- The trace-level narrow-load defect exclusion supplies the high-lane equality
for a selected general MemAlign provider row.  This is the only route from the
v0.17.0 defect boundary into the legacy subdoubleword provider witness; the
separate ROM/range package contains no data-lane assertion. -/
theorem exists_subdoublewordLoadProviderWitness_of_not_memAlignNarrowLoadLaneForge
    {length : ℕ} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : Air.Flat.EnsembleWitness
      (ZiskFv.AirsClean.FullEnsemble.fullRv64imEnsemble length program).ensemble}
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    {mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL}
    {marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL}
    {r_main : ℕ} {entry : MemoryBusEntry FGL}
    (h_not_forge : ¬ Defects.MemAlignNarrowLoadLaneForge program witness entry)
    (h_rom : MemAlignLoadProviderRomValueFacts program witness main r_main entry)
    (h_provider : MemAlignLoadProviderRowMatchSpec program witness entry) :
    ∃ ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL,
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        main mab marb ma r_main entry := by
  refine exists_subdoublewordLoadProviderWitness_of_memAlignLoadProviderRowMatchSpec
    (main := main) (mab := mab) (marb := marb) (r_main := r_main) h_rom ?_ h_provider
  intro providerTable providerRow h_providerTable h_providerRow h_spec h_component h_match
  exact Defects.memAlignNarrowLoadLane_zero_of_not_forge h_not_forge h_providerTable
    h_providerRow h_spec h_component h_match

/-- The accepted mutable-Mem provider path places the concrete load `b` row in
the accepted Mem replay row list before any seed-specific order certificate is
used.

The generic accepted-trace theorem still needs an active Main interaction, its
evaluated message equality, and the load `mem_op = 1` fact. For the concrete
load b-side memory row, the interaction membership, evaluated message equality,
`mem_op = 1`, and entry match are derived from accepted Main table structure
and the load-decoder/active-pull facts. The remaining residue is still the
syntactic non-mutable provider exclusion. -/
theorem AcceptedZiskTrace.memReplayRows_of_loadBMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∈
      ziskTrace.memReplayRows h_present := by
  have h_mainRow : loadBMemMainRow ziskTrace i ∈ ziskTrace.mainTable.table :=
    List.mem_iff_get.mpr ⟨⟨i.val, ziskTrace.mainTable_index i⟩, rfl⟩
  have h_mainInteraction :
      loadBMemMainInteraction ziskTrace i ∈
        ziskTrace.mainTable.interactionsWith MemBusChannel.toRaw := by
    simpa [loadBMemMainInteraction, loadBMemMainRow, loadBMemMainMessage] using
      RomDecodeBinding.mainRowWithRomLd_bMemInteraction_mem ziskTrace i
  have h_mainEval :
      loadBMemMainInteraction ziskTrace i =
        ((MemBusChannel.emitted (loadBMemMainMultiplicity ziskTrace)
          (loadBMemMainMessage ziskTrace)).toRaw).eval
          (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i)) := rfl
  have h_row_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            ziskTrace.programLength ziskTrace.program).rowInputVar =
        mainRowWithRomLd ziskTrace i := by
    simpa [loadBMemMainRow, mainRowWithRomLd] using
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
        ziskTrace.program ziskTrace.mainTable
        ⟨i.val, ziskTrace.mainTable_index i⟩).symm
  have h_active_mult :
      Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (loadBMemMainMultiplicity ziskTrace) = (-1 : FGL) := by
    have h_source_sum :=
      ZiskFv.AirsClean.Main.eval_bSourceSumExpr
        (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          ziskTrace.programLength ziskTrace.program).rowInputVar
    have h_source_sum' :
        Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_reg) =
          (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.b_src_mem
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.b_src_ind
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.b_src_reg := by
      simpa using h_source_sum
    rw [loadBMemMainMultiplicity]
    change
      (-1 : FGL) *
          Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_reg) = -1
    rw [h_source_sum', h_row_eval]
    simpa using h_active
  have h_active_interaction :
      (loadBMemMainInteraction ziskTrace i).mult = -1 := by
    rw [h_mainEval]
    change
      Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (loadBMemMainMultiplicity ziskTrace) = -1
    exact h_active_mult
  have h_msg_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (loadBMemMainMessage ziskTrace) =
        ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd ziskTrace i) := by
    rw [loadBMemMainMessage, ZiskFv.AirsClean.Main.eval_bMemMessageExpr, h_row_eval]
  have h_main_mem_op :
      (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (loadBMemMainMessage ziskTrace)).mem_op = 1 := by
    rw [h_msg_eval]
    exact RomDecodeBinding.mainRowWithRomLd_bMemMessage_mem_op_eq_one_of_active
      ziskTrace i h_b_src_ind h_active
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            (loadBMemMainMessage ziskTrace)) (-1) 2) := by
    rw [h_msg_eval]
    simp
  exact ziskTrace.activeMainMutableMemProviderEntryMemOfReplayBridge_of_main_mem_op_one
    h_present h_mainRow h_mainInteraction h_mainEval h_active_interaction h_main_mem_op
    h_no_nonmutable h_entry

/-- Store-`c` analogue of `AcceptedZiskTrace.memReplayRows_of_loadBMemProviderEntry`.

Accepted trace data proves the concrete store write row occurs in accepted Mem
replay rows before the seed-specific order certificate is used. The remaining
residue is the syntactic exclusion of non-mutable provider branches for the
store-shaped Main message. -/
theorem AcceptedZiskTrace.memReplayRows_of_storeCMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (h_store_ind : (mainRowWithRomSt ziskTrace i).rom.store_ind = 1)
    (h_active :
      -((mainRowWithRomSt ziskTrace i).rom.store_mem
        + (mainRowWithRomSt ziskTrace i).rom.store_ind
        + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
        (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2) :
    (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 ∈
      ziskTrace.memReplayRows h_present := by
  have h_mainRow : storeCMemMainRow ziskTrace i ∈ ziskTrace.mainTable.table :=
    List.mem_iff_get.mpr ⟨⟨i.val, ziskTrace.mainTable_index i⟩, rfl⟩
  have h_mainInteraction :
      storeCMemMainInteraction ziskTrace i ∈
        ziskTrace.mainTable.interactionsWith MemBusChannel.toRaw := by
    simpa [storeCMemMainInteraction, storeCMemMainRow, storeCMemMainMessage] using
      RomDecodeBinding.mainRowWithRomSt_cMemInteraction_mem ziskTrace i
  have h_mainEval :
      storeCMemMainInteraction ziskTrace i =
        ((MemBusChannel.emitted (storeCMemMainMultiplicity ziskTrace)
          (storeCMemMainMessage ziskTrace)).toRaw).eval
          (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i)) := rfl
  have h_row_eval :
      eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            ziskTrace.programLength ziskTrace.program).rowInputVar =
        mainRowWithRomSt ziskTrace i := by
    simpa [storeCMemMainRow, mainRowWithRomSt] using
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
        ziskTrace.program ziskTrace.mainTable
        ⟨i.val, ziskTrace.mainTable_index i⟩).symm
  have h_active_mult :
      Expression.eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
          (storeCMemMainMultiplicity ziskTrace) = (-1 : FGL) := by
    have h_source_sum :=
      ZiskFv.AirsClean.Main.eval_cSourceSumExpr
        (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          ziskTrace.programLength ziskTrace.program).rowInputVar
    have h_source_sum' :
        Expression.eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_reg) =
          (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.store_mem
            + (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.store_ind
            + (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.store_reg := by
      simpa using h_source_sum
    rw [storeCMemMainMultiplicity]
    change
      (-1 : FGL) *
          Expression.eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.store_reg) = -1
    rw [h_source_sum', h_row_eval]
    simpa using h_active
  have h_active_interaction :
      (storeCMemMainInteraction ziskTrace i).mult = -1 := by
    rw [h_mainEval]
    change
      Expression.eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
        (storeCMemMainMultiplicity ziskTrace) = -1
    exact h_active_mult
  have h_msg_eval :
      eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
          (storeCMemMainMessage ziskTrace) =
        ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt ziskTrace i) := by
    rw [storeCMemMainMessage, ZiskFv.AirsClean.Main.eval_cMemMessageExpr, h_row_eval]
  have h_main_mem_op :
      (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
        (storeCMemMainMessage ziskTrace)).mem_op = 2 := by
    rw [h_msg_eval]
    exact RomDecodeBinding.mainRowWithRomSt_cMemMessage_mem_op_eq_two_of_active
      ziskTrace i h_store_ind h_active
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
            (storeCMemMainMessage ziskTrace)) 1 2) := by
    rw [h_msg_eval]
    simp
  exact ziskTrace.activeMainMutableMemProviderEntryMemOfReplayBridge_of_main_mem_op_two
    h_present h_mainRow h_mainInteraction h_mainEval h_active_interaction h_main_mem_op
    h_no_nonmutable h_entry

/-- Seed-order transport wrapper for the accepted mutable-Mem load `b`
provider path.

Accepted trace data proves the concrete load row occurs in accepted Mem replay
rows; the seed's replay-safe order certificate transports that row to the
execution-order `rowsOf` list. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∈
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  exact inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_loadBMemProviderEntry h_present i h_b_src_ind h_active
      h_no_nonmutable)

/-- Branch-split accepted replay version of
`AcceptedZiskTrace.memReplayRows_of_loadBMemProviderEntry`.

The caller keeps only the MemAlign-family exclusions. The RegisterBoundary and
Main self-provider exclusions are derived from the load's `mem_op = 1` message
plus accepted Main selector Booleanity, and the resulting mutable-Mem branch
places the concrete load row in accepted Mem replay rows before any seed order
certificate is used. -/
theorem AcceptedZiskTrace.memReplayRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∈
      ziskTrace.memReplayRows h_present := by
  have h_row_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            ziskTrace.programLength ziskTrace.program).rowInputVar =
        mainRowWithRomLd ziskTrace i := by
    simpa [loadBMemMainRow, mainRowWithRomLd] using
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
        ziskTrace.program ziskTrace.mainTable
        ⟨i.val, ziskTrace.mainTable_index i⟩).symm
  have h_msg_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (loadBMemMainMessage ziskTrace) =
        ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd ziskTrace i) := by
    rw [loadBMemMainMessage, ZiskFv.AirsClean.Main.eval_bMemMessageExpr, h_row_eval]
  have h_main_mem_op :
      (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (loadBMemMainMessage ziskTrace)).mem_op = 1 := by
    rw [h_msg_eval]
    exact RomDecodeBinding.mainRowWithRomLd_bMemMessage_mem_op_eq_one_of_active
      ziskTrace i h_b_src_ind h_active
  have h_mainEval :
      loadBMemMainInteraction ziskTrace i =
        ((MemBusChannel.emitted (loadBMemMainMultiplicity ziskTrace)
          (loadBMemMainMessage ziskTrace)).toRaw).eval
          (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i)) := rfl
  have h_no_regBoundary :
      ¬ ActiveMainRegisterBoundaryProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2 :=
    not_activeMainRegisterBoundaryProviderRowMatchSpec_of_main_mem_op_one
      h_mainEval h_main_mem_op
  have h_no_main :
      ¬ ActiveMainSelfMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2 :=
    not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one
      ziskTrace.constraints_hold h_mainEval h_main_mem_op
  exact ziskTrace.memReplayRows_of_loadBMemProviderEntry h_present i h_b_src_ind h_active
    (activeMainNonMutableMemProviderRowMatchSpec_of_no_branch
      h_no_marb h_no_mab h_no_memAlign h_no_main h_no_regBoundary)

/-- Branch-split version of
`BootSegmentReadSoundInputs.mem_executionRows_of_loadBMemProviderEntry`.

This keeps the remaining non-mutable-provider residue decomposed into the
MemAlign-family cases instead of accepting the aggregate non-mutable exclusion
directly. The RegisterBoundary and Main self-provider cases are discharged from
the load's `mem_op = 1` message plus accepted Main selector Booleanity. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 ∈
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  exact inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
      h_present i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign)

/-- Accepted replay coverage version of the load `b` provider split.

Instead of requiring the caller to exclude every MemAlign-family branch, this
theorem follows accepted provider coverage far enough to expose the available
structural alternatives. The mutable-Mem branch places the concrete load row in
accepted Mem replay rows before any seed order certificate is used; the
MemAlign-family branches expose structural provider-row predicates for an entry
matching that concrete load row. The general MemAlign branch keeps its selected
prove-branch pins explicit. -/
theorem AcceptedZiskTrace.memReplayRows_or_memAlignProvider_of_loadBMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ziskTrace.memReplayRows h_present
        ∨ MemAlignReadByteLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry
        ∨ MemAlignByteLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry
        ∨ MemAlignLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry) := by
  have h_mainRow : loadBMemMainRow ziskTrace i ∈ ziskTrace.mainTable.table :=
    List.mem_iff_get.mpr ⟨⟨i.val, ziskTrace.mainTable_index i⟩, rfl⟩
  have h_mainInteraction :
      loadBMemMainInteraction ziskTrace i ∈
        ziskTrace.mainTable.interactionsWith MemBusChannel.toRaw := by
    simpa [loadBMemMainInteraction, loadBMemMainRow, loadBMemMainMessage] using
      RomDecodeBinding.mainRowWithRomLd_bMemInteraction_mem ziskTrace i
  have h_mainEval :
      loadBMemMainInteraction ziskTrace i =
        ((MemBusChannel.emitted (loadBMemMainMultiplicity ziskTrace)
          (loadBMemMainMessage ziskTrace)).toRaw).eval
          (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i)) := rfl
  have h_row_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            ziskTrace.programLength ziskTrace.program).rowInputVar =
        mainRowWithRomLd ziskTrace i := by
    simpa [loadBMemMainRow, mainRowWithRomLd] using
      (ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
        ziskTrace.program ziskTrace.mainTable
        ⟨i.val, ziskTrace.mainTable_index i⟩).symm
  have h_active_mult :
      Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (loadBMemMainMultiplicity ziskTrace) = (-1 : FGL) := by
    have h_source_sum :=
      ZiskFv.AirsClean.Main.eval_bSourceSumExpr
        (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          ziskTrace.programLength ziskTrace.program).rowInputVar
    have h_source_sum' :
        Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_reg) =
          (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.b_src_mem
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.b_src_ind
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar).rom.b_src_reg := by
      simpa using h_source_sum
    rw [loadBMemMainMultiplicity]
    change
      (-1 : FGL) *
          Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                ziskTrace.programLength ziskTrace.program).rowInputVar.rom.b_src_reg) = -1
    rw [h_source_sum', h_row_eval]
    simpa using h_active
  have h_active_interaction :
      (loadBMemMainInteraction ziskTrace i).mult = -1 := by
    rw [h_mainEval]
    change
      Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (loadBMemMainMultiplicity ziskTrace) = -1
    exact h_active_mult
  have h_msg_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (loadBMemMainMessage ziskTrace) =
        ZiskFv.AirsClean.Main.bMemMessage (mainRowWithRomLd ziskTrace i) := by
    rw [loadBMemMainMessage, ZiskFv.AirsClean.Main.eval_bMemMessageExpr, h_row_eval]
  have h_main_mem_op :
      (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
        (loadBMemMainMessage ziskTrace)).mem_op = 1 := by
    rw [h_msg_eval]
    exact RomDecodeBinding.mainRowWithRomLd_bMemMessage_mem_op_eq_one_of_active
      ziskTrace i h_b_src_ind h_active
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            (loadBMemMainMessage ziskTrace)) (-1) 2) := by
    rw [h_msg_eval]
    simp
  have h_match :=
    ziskTrace.activeMainMemProviderRowMatchSpec_of_active_main_eval
      h_mainRow h_mainInteraction h_mainEval h_active_interaction
      (multiplicity := (-1 : FGL)) (as := (2 : FGL))
  rcases activeMainMemProviderRowMatchSpec_mutable_or_nonmutable h_match.2 with
    h_mutable | h_nonmutable
  · refine ⟨(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1,
      ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _, Or.inl ?_⟩
    exact activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded_of_main_mem_op_one
      h_mutable h_mainEval h_main_mem_op h_entry
      (mutableActiveMemReplayRowsEmbeddedInTrace_of_fullWitnessMemReplayBridge
        (ziskTrace.memReplayBridge h_present)
        (ziskTrace.memReplayBridge_coversMutableMemTables h_present))
  · rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases
      h_nonmutable with h_marb | h_mab | h_memAlign | h_main | h_regBoundary
    · refine ⟨_, h_entry, Or.inr (Or.inl ?_)⟩
      exact memAlignReadByteLoadProviderRowMatchSpec_of_activeMain_branch
        (h_as := rfl) h_marb
    · refine ⟨_, h_entry, Or.inr (Or.inr (Or.inl ?_))⟩
      exact memAlignByteLoadProviderRowMatchSpec_of_activeMain_branch
        h_mainEval h_main_mem_op (h_as := rfl) h_mab
    · refine ⟨_, h_entry, Or.inr (Or.inr (Or.inr ?_))⟩
      exact memAlignLoadProviderRowMatchSpec_of_activeMain_branch
        h_mainEval h_main_mem_op (h_as := rfl) h_memAlign h_selectedMemAlignPins
    · exact False.elim
        (not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one
          ziskTrace.constraints_hold h_mainEval h_main_mem_op h_main)
    · exact False.elim
        (not_activeMainRegisterBoundaryProviderRowMatchSpec_of_main_mem_op_one
          h_mainEval h_main_mem_op h_regBoundary)

/-- Coverage version of the load `b` provider split.

Instead of requiring the caller to exclude every MemAlign-family branch, this
theorem follows the accepted provider coverage far enough to expose the
available structural alternatives. The mutable-Mem branch places the concrete
load row in execution order; the MemAlign-family branches expose structural
provider-row predicates for an entry matching that concrete load row. The
general MemAlign branch keeps its selected prove-branch pins explicit. -/
theorem BootSegmentReadSoundInputs.mem_or_memAlignProvider_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)
        ∨ MemAlignReadByteLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry
        ∨ MemAlignByteLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry
        ∨ MemAlignLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_memAlignProvider_of_loadBMemProviderEntry
      h_present i h_b_src_ind h_active h_selectedMemAlignPins
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_marb | h_mab | h_memAlign
  · exact Or.inl (inputs.mem_executionRows_of_memReplayRows h_mem)
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr h_memAlign))

/-- Accepted replay coverage with byte-oriented MemAlign branches converted to
the legacy subdoubleword provider-witness shape.

The mutable-Mem branch proves accepted replay membership; the seed order
certificate is not used until the seed wrapper below. -/
theorem AcceptedZiskTrace.memReplayRows_or_subdoublewordProvider_or_memAlignProvider_of_loadBMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (r_main : ℕ)
    (h_width : main.ind_width r_main = 1)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ziskTrace.memReplayRows h_present
        ∨ (∃ marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab marb' ma r_main entry)
        ∨ (∃ mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab' marb ma r_main entry)
        ∨ MemAlignLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_memAlignProvider_of_loadBMemProviderEntry
      h_present i h_b_src_ind h_active h_selectedMemAlignPins
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_marb | h_mab | h_memAlign
  · exact Or.inl h_mem
  · exact Or.inr (Or.inl
      (exists_subdoublewordLoadProviderWitness_of_memAlignReadByteLoadProviderRowMatchSpec
        (main := main) (mab := mab) (ma := ma) (r_main := r_main)
        h_width h_marb))
  · exact Or.inr (Or.inr (Or.inl
      (exists_subdoublewordLoadProviderWitness_of_memAlignByteLoadProviderRowMatchSpec
        (main := main) (marb := marb) (ma := ma) (r_main := r_main)
        h_width h_mab)))
  · exact Or.inr (Or.inr (Or.inr h_memAlign))

/-- Load `b` provider coverage with byte-oriented MemAlign branches converted to
the legacy subdoubleword provider-witness shape.

The mutable-Mem branch places the concrete load row in execution order. The
MemAlignReadByte/MemAlignByte branches now produce the provider part of a
`SubdoublewordLoadProviderWitness`; the remaining general MemAlign branch stays
as the explicit structural residue because its ROM/value pins are not supplied
by row-local memory-bus balance. -/
theorem BootSegmentReadSoundInputs.mem_or_subdoublewordProvider_or_memAlignProvider_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (r_main : ℕ)
    (h_width : main.ind_width r_main = 1)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)
        ∨ (∃ marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab marb' ma r_main entry)
        ∨ (∃ mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab' marb ma r_main entry)
        ∨ MemAlignLoadProviderRowMatchSpec
            ziskTrace.program ziskTrace.witness entry) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_subdoublewordProvider_or_memAlignProvider_of_loadBMemProviderEntry
      h_present i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_marb | h_mab | h_memAlign
  · exact Or.inl (inputs.mem_executionRows_of_memReplayRows h_mem)
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr h_memAlign))

/-- Load `b` provider coverage with every MemAlign-family branch converted to
the legacy subdoubleword provider-witness shape.

The mutable-Mem branch proves accepted replay membership; the seed order
certificate is not used until the seed wrapper below. -/
theorem AcceptedZiskTrace.memReplayRows_or_subdoublewordProvider_of_loadBMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (r_main : ℕ)
    (h_width : main.ind_width r_main = 1)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i)
    (h_generalMemAlignRomValues :
      ∀ entry,
        ZiskFv.Airs.MemoryBus.matches_memory_entry
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
        LoadBMemAlignRomValueFacts ziskTrace main r_main entry)
    (h_no_narrow_load_lane_forge : LoadBNoMemAlignNarrowLoadLaneForge ziskTrace i) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ziskTrace.memReplayRows h_present
        ∨ ∃ mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL,
          ∃ marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL,
          ∃ ma' : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab' marb' ma' r_main entry) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_subdoublewordProvider_or_memAlignProvider_of_loadBMemProviderEntry
      h_present i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_marb | h_mab | h_memAlign
  · exact Or.inl h_mem
  · rcases h_marb with ⟨marb', h_provider⟩
    exact Or.inr ⟨mab, marb', ma, h_provider⟩
  · rcases h_mab with ⟨mab', h_provider⟩
    exact Or.inr ⟨mab', marb, ma, h_provider⟩
  · rcases
      exists_subdoublewordLoadProviderWitness_of_not_memAlignNarrowLoadLaneForge
        (main := main) (mab := mab) (marb := marb) (r_main := r_main)
        (h_no_narrow_load_lane_forge entry h_entry)
        (h_generalMemAlignRomValues entry h_entry) h_memAlign with
      ⟨ma', h_provider⟩
    exact Or.inr ⟨mab, marb, ma', h_provider⟩

/-- Load `b` provider coverage with every MemAlign-family branch converted to
the legacy subdoubleword provider-witness shape.

The mutable-Mem branch still proves execution-row membership. All MemAlign
branches now return a `SubdoublewordLoadProviderWitness`; the general branch
uses the trace-level narrow-load defect boundary plus the explicit ROM/range
residue for the selected structural provider row. -/
theorem BootSegmentReadSoundInputs.mem_or_subdoublewordProvider_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (r_main : ℕ)
    (h_width : main.ind_width r_main = 1)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i)
    (h_generalMemAlignRomValues :
      ∀ entry,
        ZiskFv.Airs.MemoryBus.matches_memory_entry
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
        LoadBMemAlignRomValueFacts ziskTrace main r_main entry)
    (h_no_narrow_load_lane_forge : LoadBNoMemAlignNarrowLoadLaneForge ziskTrace i) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)
        ∨ ∃ mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL,
          ∃ marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL,
          ∃ ma' : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab' marb' ma' r_main entry) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_subdoublewordProvider_of_loadBMemProviderEntry
      h_present i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins h_generalMemAlignRomValues h_no_narrow_load_lane_forge
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_provider
  · exact Or.inl (inputs.mem_executionRows_of_memReplayRows h_mem)
  · exact Or.inr h_provider

/-- Load `b` provider coverage at the existing `MemAlignWitness` consumer
surface.

The mutable-Mem branch proves accepted replay membership; the seed order
certificate is not used until the seed wrapper below. -/
theorem AcceptedZiskTrace.memReplayRows_or_memAlignWitness_of_loadBMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (r_main : ℕ)
    (h_width : main.ind_width r_main = 1)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i)
    (h_generalMemAlignRomValues :
      ∀ entry,
        ZiskFv.Airs.MemoryBus.matches_memory_entry
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
        LoadBMemAlignRomValueFacts ziskTrace main r_main entry)
    (h_no_narrow_load_lane_forge : LoadBNoMemAlignNarrowLoadLaneForge ziskTrace i)
    (h_coreLookup :
      ∀ entry
        (mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
        (marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
        (ma' : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL),
        ZiskFv.Airs.MemoryBus.matches_memory_entry
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
        ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
          main mab' marb' ma' r_main entry →
        MemAlignCoreLookupFacts mab' marb') :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ziskTrace.memReplayRows h_present
        ∨ Nonempty (ZiskFv.Compliance.MemAlignWitness main r_main entry)) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_subdoublewordProvider_of_loadBMemProviderEntry
      h_present i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins h_generalMemAlignRomValues h_no_narrow_load_lane_forge
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_provider
  · exact Or.inl h_mem
  · rcases h_provider with ⟨mab', marb', ma', h_provider⟩
    have h_coreLookup' := h_coreLookup entry mab' marb' ma' h_entry h_provider
    exact Or.inr
      ⟨memAlignWitness_of_coreLookupFacts_provider h_coreLookup' h_provider⟩

/-- Load `b` provider coverage at the existing `MemAlignWitness` consumer
surface.

The mutable-Mem branch still proves execution-row membership. The MemAlign
branch returns the legacy `MemAlignWitness` bundle once the trace-level
narrow-load defect boundary, general-MemAlign ROM/range residue, and
MemAlignByte/MemAlignReadByte core/lookup residue are supplied. -/
theorem BootSegmentReadSoundInputs.mem_or_memAlignWitness_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (r_main : ℕ)
    (h_width : main.ind_width r_main = 1)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_selectedMemAlignPins : LoadBSelectedMemAlignPins ziskTrace i)
    (h_generalMemAlignRomValues :
      ∀ entry,
        ZiskFv.Airs.MemoryBus.matches_memory_entry
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
        LoadBMemAlignRomValueFacts ziskTrace main r_main entry)
    (h_no_narrow_load_lane_forge : LoadBNoMemAlignNarrowLoadLaneForge ziskTrace i)
    (h_coreLookup :
      ∀ entry
        (mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
        (marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
        (ma' : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL),
        ZiskFv.Airs.MemoryBus.matches_memory_entry
          (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry →
        ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
          main mab' marb' ma' r_main entry →
        MemAlignCoreLookupFacts mab' marb') :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)
        ∨ Nonempty (ZiskFv.Compliance.MemAlignWitness main r_main entry)) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_memAlignWitness_of_loadBMemProviderEntry
      h_present i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins h_generalMemAlignRomValues h_no_narrow_load_lane_forge h_coreLookup
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_provider
  · exact Or.inl (inputs.mem_executionRows_of_memReplayRows h_mem)
  · exact Or.inr h_provider

/-- The concrete execution-order memory-bus rows emitted by one decoded step. -/
noncomputable def memoryRowsOfStep
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → List (MemoryBusEntry FGL)
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ =>
      [(busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1]
  | .sb _ | .sh _ | .sw _ | .sd _ =>
      [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]
  | .sub _ | .and _ | .or _ | .xor _ | .slt _ | .sltu _
  | .andi _ | .ori _ | .xori _ | .slti _ | .sltiu _
  | .sll _ | .srl _ | .sra _ | .slli _ | .srli _ | .srai _
  | .add _ | .addi _ | .subw _ | .addw _ | .addiw _
  | .sllw _ | .srlw _ | .sraw _ | .slliw _ | .srliw _ | .sraiw _
  | .mul _ | .mulh _ | .mulhsu _ | .mulw _ | .mulhu _
  | .div _ | .rem _ | .divw _ | .remw _ | .divu _ | .divuw _
  | .remu _ | .remuw _
  | .beq _ | .bne _ | .blt _ | .bge _ | .bltu _ | .bgeu _
  | .lui _ | .auipc _ | .jal _ | .jalr _ | .fence _ =>
      []

/-- Structural decoded steps that emit a load memory row. -/
@[reducible]
def ZiskStepLoadMemoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ =>
      True
  | .sb _ | .sh _ | .sw _ | .sd _
  | .sub _ | .and _ | .or _ | .xor _ | .slt _ | .sltu _
  | .andi _ | .ori _ | .xori _ | .slti _ | .sltiu _
  | .sll _ | .srl _ | .sra _ | .slli _ | .srli _ | .srai _
  | .add _ | .addi _ | .subw _ | .addw _ | .addiw _
  | .sllw _ | .srlw _ | .sraw _ | .slliw _ | .srliw _ | .sraiw _
  | .mul _ | .mulh _ | .mulhsu _ | .mulw _ | .mulhu _
  | .div _ | .rem _ | .divw _ | .remw _ | .divu _ | .divuw _
  | .remu _ | .remuw _
  | .beq _ | .bne _ | .blt _ | .bge _ | .bltu _ | .bgeu _
  | .lui _ | .auipc _ | .jal _ | .jalr _ | .fence _ =>
      False

/-- Structural decoded steps that emit a store memory row. -/
@[reducible]
def ZiskStepStoreMemoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .sb _ | .sh _ | .sw _ | .sd _ =>
      True
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _
  | .sub _ | .and _ | .or _ | .xor _ | .slt _ | .sltu _
  | .andi _ | .ori _ | .xori _ | .slti _ | .sltiu _
  | .sll _ | .srl _ | .sra _ | .slli _ | .srli _ | .srai _
  | .add _ | .addi _ | .subw _ | .addw _ | .addiw _
  | .sllw _ | .srlw _ | .sraw _ | .slliw _ | .srliw _ | .sraiw _
  | .mul _ | .mulh _ | .mulhsu _ | .mulw _ | .mulhu _
  | .div _ | .rem _ | .divw _ | .remw _ | .divu _ | .divuw _
  | .remu _ | .remuw _
  | .beq _ | .bne _ | .blt _ | .bge _ | .bltu _ | .bgeu _
  | .lui _ | .auipc _ | .jal _ | .jalr _ | .fence _ =>
      False

/-- Structural decoded steps that emit no memory-bus rows. -/
@[reducible]
def ZiskStepNoMemoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .sub _ | .and _ | .or _ | .xor _ | .slt _ | .sltu _
  | .andi _ | .ori _ | .xori _ | .slti _ | .sltiu _
  | .sll _ | .srl _ | .sra _ | .slli _ | .srli _ | .srai _
  | .add _ | .addi _ | .subw _ | .addw _ | .addiw _
  | .sllw _ | .srlw _ | .sraw _ | .slliw _ | .srliw _ | .sraiw _
  | .mul _ | .mulh _ | .mulhsu _ | .mulw _ | .mulhu _
  | .div _ | .rem _ | .divw _ | .remw _ | .divu _ | .divuw _
  | .remu _ | .remuw _
  | .beq _ | .bne _ | .blt _ | .bge _ | .bltu _ | .bgeu _
  | .lui _ | .auipc _ | .jal _ | .jalr _ | .fence _ =>
      True
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _
  | .sb _ | .sh _ | .sw _ | .sd _ =>
      False

/-- A decoded no-memory step emits an empty structural memory-row list. -/
theorem memoryRowsOfStep_eq_nil_of_noMemoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepNoMemoryRows ziskTrace i step) :
    memoryRowsOfStep ziskTrace i step = [] := by
  cases step <;> simp [ZiskStepNoMemoryRows, memoryRowsOfStep] at h_step ⊢

/-- Named syntactic residue for the direct mutable-Mem load path.

The active source-sum fact says the concrete Main `b` memory-bus pull is active.
The three exclusions rule out the remaining MemAlign-family provider branches,
leaving the mutable-Mem provider branch. -/
structure LoadBDirectMutableMemResidues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) where
  active :
    -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
      + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
      + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL)
  no_marb :
    ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
      ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
      (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2
  no_mab :
    ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
      ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
      (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2
  no_memAlign :
    ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
      ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
      (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2

/-- Named syntactic residue for the direct mutable-Mem store path.

The active source-sum fact says the concrete Main `c` memory-bus pull is active.
The exclusion rules out non-mutable provider branches, leaving the mutable-Mem
provider branch. -/
structure StoreCDirectMutableMemResidues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) where
  active :
    -((mainRowWithRomSt ziskTrace i).rom.store_mem
      + (mainRowWithRomSt ziskTrace i).rom.store_ind
      + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL)
  no_nonmutable :
    ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
      ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
      (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2

/-- Structural decoded steps whose emitted memory rows are already routed
through the direct mutable-Mem provider path.

The constructors carry the remaining syntactic route residues for the direct
load/store paths. They deliberately do not include MemAlign-family provider
alternatives: those stay named separately until the broader row-correspondence
scope is resolved. -/
inductive ZiskStepDirectMutableMemRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    ZiskStep ziskTrace i → Prop
  | load {step : ZiskStep ziskTrace i}
      (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
      (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
      (h_active :
        -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
          + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
          + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
      (h_no_marb :
        ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
          ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
          (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
      (h_no_mab :
        ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
          ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
          (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
      (h_no_memAlign :
        ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
          ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
          (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
      ZiskStepDirectMutableMemRows ziskTrace i step
  | store {step : ZiskStep ziskTrace i}
      (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
      (h_store_ind : (mainRowWithRomSt ziskTrace i).rom.store_ind = 1)
      (h_active :
        -((mainRowWithRomSt ziskTrace i).rom.store_mem
          + (mainRowWithRomSt ziskTrace i).rom.store_ind
          + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
      (h_no_nonmutable :
        ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
          ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
          (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2) :
      ZiskStepDirectMutableMemRows ziskTrace i step

/-- Structural decoded steps in the current scoped direct-Mem correspondence:
either a direct mutable-Mem load/store row with its explicit route residues, or
an instruction that emits no memory rows. -/
inductive ZiskStepScopedDirectMemRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    ZiskStep ziskTrace i → Prop
  | direct {step : ZiskStep ziskTrace i}
      (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step) :
      ZiskStepScopedDirectMemRows ziskTrace i step
  | noMemory {step : ZiskStep ziskTrace i}
      (h_empty : memoryRowsOfStep ziskTrace i step = []) :
      ZiskStepScopedDirectMemRows ziskTrace i step

/-- Build the scoped no-memory branch from the named structural no-memory
classifier. -/
theorem ZiskStepScopedDirectMemRows.noMemory_of_noMemoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepNoMemoryRows ziskTrace i step) :
    ZiskStepScopedDirectMemRows ziskTrace i step :=
  ZiskStepScopedDirectMemRows.noMemory
    (memoryRowsOfStep_eq_nil_of_noMemoryRows h_step)

/-- Build the scoped direct mutable-Mem load classification from the existing
per-op decode record, so callers do not need to pass the load selector pin
separately. -/
theorem ZiskStepDirectMutableMemRows.load_of_rowDecode
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    ZiskStepDirectMutableMemRows ziskTrace i step := by
  cases step <;> simp [ZiskStepLoadMemoryRows] at h_load
  all_goals
    exact ZiskStepDirectMutableMemRows.load h_load h_decode.h_b_src_ind h_active
      h_no_marb h_no_mab h_no_memAlign

/-- Residue-bundle form of `ZiskStepDirectMutableMemRows.load_of_rowDecode`. -/
theorem ZiskStepDirectMutableMemRows.load_of_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : LoadBDirectMutableMemResidues ziskTrace i) :
    ZiskStepDirectMutableMemRows ziskTrace i step :=
  ZiskStepDirectMutableMemRows.load_of_rowDecode ziskTrace i h_load h_decode
    h_residue.active h_residue.no_marb h_residue.no_mab h_residue.no_memAlign

/-- Build the scoped direct mutable-Mem store classification from the existing
per-op decode record, so callers do not need to pass the store selector pin
separately. The active c-side pull and non-mutable-provider exclusion remain
explicit residues. -/
theorem ZiskStepDirectMutableMemRows.store_of_rowDecode
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_active :
      -((mainRowWithRomSt ziskTrace i).rom.store_mem
        + (mainRowWithRomSt ziskTrace i).rom.store_ind
        + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
        (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2) :
    ZiskStepDirectMutableMemRows ziskTrace i step := by
  cases step <;> simp [ZiskStepStoreMemoryRows] at h_store
  all_goals
    exact ZiskStepDirectMutableMemRows.store h_store h_decode.h_store_ind h_active
      h_no_nonmutable

/-- Residue-bundle form of `ZiskStepDirectMutableMemRows.store_of_rowDecode`. -/
theorem ZiskStepDirectMutableMemRows.store_of_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : StoreCDirectMutableMemResidues ziskTrace i) :
    ZiskStepDirectMutableMemRows ziskTrace i step :=
  ZiskStepDirectMutableMemRows.store_of_rowDecode ziskTrace i h_store h_decode
    h_residue.active h_residue.no_nonmutable

/-- Scoped wrapper for decoded direct mutable-Mem loads with named residues. -/
theorem ZiskStepScopedDirectMemRows.load_of_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : LoadBDirectMutableMemResidues ziskTrace i) :
    ZiskStepScopedDirectMemRows ziskTrace i step :=
  ZiskStepScopedDirectMemRows.direct
    (ZiskStepDirectMutableMemRows.load_of_rowDecode_residues
      ziskTrace i h_load h_decode h_residue)

/-- Scoped wrapper for decoded direct mutable-Mem stores with named residues. -/
theorem ZiskStepScopedDirectMemRows.store_of_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : StoreCDirectMutableMemResidues ziskTrace i) :
    ZiskStepScopedDirectMemRows ziskTrace i step :=
  ZiskStepScopedDirectMemRows.direct
    (ZiskStepDirectMutableMemRows.store_of_rowDecode_residues
      ziskTrace i h_store h_decode h_residue)

/-- Scoped structural row correspondence for direct mutable-Mem load rows.

For a decoded load step, any row in `memoryRowsOfStep` is the concrete `busLd.e1`
row. Accepted provider coverage plus the remaining syntactic MemAlign-family
exclusion residue place that row in the accepted Mem replay rows before any
seed-specific order transport is used. -/
theorem AcceptedZiskTrace.memReplayRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present := by
  cases step <;> simp [ZiskStepLoadMemoryRows, memoryRowsOfStep] at h_load h_entry
  all_goals
    subst entry
    exact ziskTrace.memReplayRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
      h_present i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign

/-- Duplicate-sensitive singleton form of the scoped direct-Mem load
correspondence.

Each structural load step emits exactly one memory row, so membership in the
accepted replay rows is equivalently a subpermutation of that singleton row
list. This is the per-step bag-correspondence shape needed by later list
assembly. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_load_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_present) := by
  cases step <;> simp [ZiskStepLoadMemoryRows, memoryRowsOfStep] at h_load ⊢
  all_goals
    exact ziskTrace.memReplayRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
      h_present i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign

/-- Scoped structural row correspondence for direct mutable-Mem store rows.

For a decoded store step, any row in `memoryRowsOfStep` is the concrete
`busSt.e2` write row. Accepted provider coverage places that row in accepted
Mem replay rows before any seed-specific order transport is used. -/
theorem AcceptedZiskTrace.memReplayRows_of_storeMemoryRowsOfStep_of_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_store_ind : (mainRowWithRomSt ziskTrace i).rom.store_ind = 1)
    (h_active :
      -((mainRowWithRomSt ziskTrace i).rom.store_mem
        + (mainRowWithRomSt ziskTrace i).rom.store_ind
        + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
        (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present := by
  cases step <;> simp [ZiskStepStoreMemoryRows, memoryRowsOfStep] at h_store h_entry
  all_goals
    subst entry
    exact ziskTrace.memReplayRows_of_storeCMemProviderEntry
      h_present i h_store_ind h_active h_no_nonmutable

/-- Duplicate-sensitive singleton form of the scoped direct-Mem store
correspondence. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_store_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_store_ind : (mainRowWithRomSt ziskTrace i).rom.store_ind = 1)
    (h_active :
      -((mainRowWithRomSt ziskTrace i).rom.store_mem
        + (mainRowWithRomSt ziskTrace i).rom.store_ind
        + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
        (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_present) := by
  cases step <;> simp [ZiskStepStoreMemoryRows, memoryRowsOfStep] at h_store ⊢
  all_goals
    exact ziskTrace.memReplayRows_of_storeCMemProviderEntry
      h_present i h_store_ind h_active h_no_nonmutable

/-- Seed-order transport wrapper for the scoped structural load correspondence.

The accepted trace proves the structural load row occurs in accepted Mem replay
rows; the seed's replay-safe order certificate transports it to the full
execution-order row list. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
      h_present i h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign h_entry)

/-- Duplicate-sensitive singleton form after seed order transport. -/
theorem BootSegmentReadSoundInputs.memoryRowsOfStep_subperm_executionRows_of_load_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_b_src_ind : (mainRowWithRomLd ziskTrace i).rom.b_src_ind = 1)
    (h_active :
      -((mainRowWithRomLd ziskTrace i).rom.b_src_mem
        + (mainRowWithRomLd ziskTrace i).rom.b_src_ind
        + (mainRowWithRomLd ziskTrace i).rom.b_src_reg) = (-1 : FGL))
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (loadBMemMainRow ziskTrace i)
        (loadBMemMainInteraction ziskTrace i) (loadBMemMainMessage ziskTrace) (-1) 2) :
    (memoryRowsOfStep ziskTrace i step).Subperm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  cases step <;> simp [ZiskStepLoadMemoryRows, memoryRowsOfStep] at h_load ⊢
  all_goals
    have h_mem := inputs.mem_executionRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
      i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign
    simpa using List.mem_flatMap.mp h_mem

/-- Seed-order transport wrapper for the scoped structural store correspondence.

The accepted trace proves the structural store row occurs in accepted Mem replay
rows; the seed's replay-safe order certificate transports it to the full
execution-order row list. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_storeMemoryRowsOfStep_of_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_store_ind : (mainRowWithRomSt ziskTrace i).rom.store_ind = 1)
    (h_active :
      -((mainRowWithRomSt ziskTrace i).rom.store_mem
        + (mainRowWithRomSt ziskTrace i).rom.store_ind
        + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
        (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_storeMemoryRowsOfStep_of_no_nonmutableBranches
      h_present i h_store h_store_ind h_active h_no_nonmutable h_entry)

/-- Duplicate-sensitive singleton form after seed order transport. -/
theorem BootSegmentReadSoundInputs.memoryRowsOfStep_subperm_executionRows_of_store_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_store_ind : (mainRowWithRomSt ziskTrace i).rom.store_ind = 1)
    (h_active :
      -((mainRowWithRomSt ziskTrace i).rom.store_mem
        + (mainRowWithRomSt ziskTrace i).rom.store_ind
        + (mainRowWithRomSt ziskTrace i).rom.store_reg) = (-1 : FGL))
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec ziskTrace.program ziskTrace.witness
        ziskTrace.mainTable (storeCMemMainRow ziskTrace i)
        (storeCMemMainInteraction ziskTrace i) (storeCMemMainMessage ziskTrace) 1 2) :
    (memoryRowsOfStep ziskTrace i step).Subperm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  cases step <;> simp [ZiskStepStoreMemoryRows, memoryRowsOfStep] at h_store ⊢
  all_goals
    have h_mem := inputs.mem_executionRows_of_memReplayRows
      (ziskTrace.memReplayRows_of_storeCMemProviderEntry
        h_present i h_store_ind h_active h_no_nonmutable)
    simpa using List.mem_flatMap.mp h_mem

/-- Scoped structural row correspondence for any direct mutable-Mem step. This
packages the direct load and direct store cases without using the seed order
certificate. -/
theorem AcceptedZiskTrace.memReplayRows_of_directMutableMemRowsOfStep
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present := by
  cases h_direct with
  | load h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign =>
      exact ziskTrace.memReplayRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
        h_present i h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign h_entry
  | store h_store h_store_ind h_active h_no_nonmutable =>
      exact ziskTrace.memReplayRows_of_storeMemoryRowsOfStep_of_no_nonmutableBranches
        h_present i h_store h_store_ind h_active h_no_nonmutable h_entry

/-- Duplicate-sensitive singleton form for any direct mutable-Mem step. This is
still step-local; whole-list duplicate accounting needs the later order/count
assembly. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_directMutableMemRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_present) := by
  cases h_direct with
  | load h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign =>
      exact ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_load_no_nonmutableBranches
        h_present i h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign
  | store h_store h_store_ind h_active h_no_nonmutable =>
      exact ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_store_no_nonmutableBranches
        h_present i h_store h_store_ind h_active h_no_nonmutable

/-- Residue-bundle row correspondence for decoded direct mutable-Mem loads. -/
theorem AcceptedZiskTrace.memReplayRows_of_loadMemoryRowsOfStep_of_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : LoadBDirectMutableMemResidues ziskTrace i)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  ziskTrace.memReplayRows_of_directMutableMemRowsOfStep h_present i
    (ZiskStepDirectMutableMemRows.load_of_rowDecode_residues
      ziskTrace i h_load h_decode h_residue)
    h_entry

/-- Residue-bundle row correspondence for decoded direct mutable-Mem stores. -/
theorem AcceptedZiskTrace.memReplayRows_of_storeMemoryRowsOfStep_of_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : StoreCDirectMutableMemResidues ziskTrace i)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  ziskTrace.memReplayRows_of_directMutableMemRowsOfStep h_present i
    (ZiskStepDirectMutableMemRows.store_of_rowDecode_residues
      ziskTrace i h_store h_decode h_residue)
    h_entry

/-- Duplicate-sensitive residue-bundle form for decoded direct mutable-Mem
loads. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_load_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_load : ZiskStepLoadMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : LoadBDirectMutableMemResidues ziskTrace i) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_present) :=
  ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_directMutableMemRows h_present i
    (ZiskStepDirectMutableMemRows.load_of_rowDecode_residues
      ziskTrace i h_load h_decode h_residue)

/-- Duplicate-sensitive residue-bundle form for decoded direct mutable-Mem
stores. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_store_rowDecode_residues
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_store : ZiskStepStoreMemoryRows ziskTrace i step)
    (h_decode : RowDecode ziskTrace i step)
    (h_residue : StoreCDirectMutableMemResidues ziskTrace i) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_present) :=
  ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_directMutableMemRows h_present i
    (ZiskStepDirectMutableMemRows.store_of_rowDecode_residues
      ziskTrace i h_store h_decode h_residue)

/-- Step-local scoped direct-Mem row correspondence, including no-memory
instructions. -/
theorem AcceptedZiskTrace.memReplayRows_of_scopedDirectMemRowsOfStep
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepScopedDirectMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present := by
  cases h_step with
  | direct h_direct =>
      exact ziskTrace.memReplayRows_of_directMutableMemRowsOfStep
        h_present i h_direct h_entry
  | noMemory h_empty =>
      simp [h_empty] at h_entry

/-- Step-local subpermutation form for the scoped direct-Mem correspondence,
including no-memory instructions. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_scopedDirectMemRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepScopedDirectMemRows ziskTrace i step) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_present) := by
  cases h_step with
  | direct h_direct =>
      exact ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_directMutableMemRows
        h_present i h_direct
  | noMemory h_empty =>
      simp [h_empty]

/-- Seed-order transport wrapper for the scoped direct mutable-Mem
correspondence. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_directMutableMemRowsOfStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_directMutableMemRowsOfStep
      h_present i h_direct h_entry)

/-- Seed-order transport wrapper for scoped direct/no-memory decoded steps. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_scopedDirectMemRowsOfStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepScopedDirectMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_scopedDirectMemRowsOfStep
      h_present i h_step h_entry)

/-- The full execution-order memory-bus row list obtained directly from the
structural per-step decoder view. -/
noncomputable def executionMemoryRowsOfSteps
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) :
    List (MemoryBusEntry FGL) :=
  (List.finRange ziskTrace.numInstructions).flatMap
    (fun i => memoryRowsOfStep ziskTrace i (ziskStep i))

/-- Count memory-bus entries with the lawful `BEq` instance induced by
`DecidableEq`. The generated `MemoryBusEntry` also has a derived `BEq`, but the
`List.Subperm` count characterization is stated for a lawful equality test. -/
private abbrev memoryBusEntryDecidableCount
    (entry : MemoryBusEntry FGL) (rows : List (MemoryBusEntry FGL)) : Nat :=
  @List.count (MemoryBusEntry FGL)
    (@instBEqOfDecidableEq (MemoryBusEntry FGL) inferInstance) entry rows

/-- Named row-count certificate for the #115 / #219 boundary.

This is deliberately only a cardinality statement: scoped direct-Mem support inclusion plus
structural `Nodup` supply the permutation proof. The remaining content is that the accepted active
Mem replay table emits exactly as many rows as the segment's structural direct-Mem execution rows.
That fact is channel-balance class, and should eventually be derived from whole-channel accepted
trace construction rather than from memory read-soundness. -/
structure ScopedDirectMemReplayLengthCertificate
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_present : MutableMemPresent ziskTrace.witness) : Prop where
  length_eq :
    (ziskTrace.memReplayRows h_present).length =
      ((List.range ziskTrace.numInstructions).flatMap rowsOf).length

private theorem fgl_neg_one_ne_one : ¬ ((-1 : FGL) = (1 : FGL)) := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [GL_eq] at hv

/-- The structural Main load memory row is a memory read, not an active write. -/
theorem busLd_e1_not_active_write
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    ¬(((busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1).as = (2 : FGL)
      ∧ ((busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1).multiplicity = (1 : FGL)) := by
  intro h
  exact fgl_neg_one_ne_one (by
    simpa [busLd, ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] using h.2)

/-- Structural steps whose emitted memory rows are replay-neutral: loads and
non-memory ops emit no active memory writes; stores are excluded. -/
@[reducible]
def ZiskStepReplayNeutralMemoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : ZiskStep ziskTrace i → Prop
  | .ld _ | .lbu _ | .lhu _ | .lwu _ | .lb _ | .lh _ | .lw _ =>
      True
  | .sb _ | .sh _ | .sw _ | .sd _ =>
      False
  | .sub _ | .and _ | .or _ | .xor _ | .slt _ | .sltu _
  | .andi _ | .ori _ | .xori _ | .slti _ | .sltiu _
  | .sll _ | .srl _ | .sra _ | .slli _ | .srli _ | .srai _
  | .add _ | .addi _ | .subw _ | .addw _ | .addiw _
  | .sllw _ | .srlw _ | .sraw _ | .slliw _ | .srliw _ | .sraiw _
  | .mul _ | .mulh _ | .mulhsu _ | .mulw _ | .mulhu _
  | .div _ | .rem _ | .divw _ | .remw _ | .divu _ | .divuw _
  | .remu _ | .remuw _
  | .beq _ | .bne _ | .blt _ | .bge _ | .bltu _ | .bgeu _
  | .lui _ | .auipc _ | .jal _ | .jalr _ | .fence _ =>
      True

/-- Replay-neutral structural steps emit no active memory writes. -/
theorem memoryRowsOfStep_not_active_write_of_replayNeutralStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepReplayNeutralMemoryRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    ¬(entry.as = (2 : FGL) ∧ entry.multiplicity = (1 : FGL)) := by
  cases step <;> simp [ZiskStepReplayNeutralMemoryRows, memoryRowsOfStep] at h_step h_entry ⊢
  all_goals
    subst entry
    intro _h_as h_mult
    exact fgl_neg_one_ne_one (by
      simpa [ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] using h_mult)

/-- Per-memory-op placement relative to the concrete seed: the *structural* tie pinning `rowsOf i` to
    this op's real memory-bus rows. Loads use the read row `busLd .. .e1`; all stores use the write
    row `busSt .. .e2`; non-memory ops emit no memory rows. Narrow stores additionally require the
    preserved high bytes already present in the replay memory at that op's execution-order prefix
    `(List.range i).flatMap rowsOf`. The split, cursor tie, and coherence chain #185 carried are now
    *derived*, not assumed. -/
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
  | .sd _ =>
      rowsOf i.val = [(busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2]
  | .sub _ | .and _ | .or _ | .xor _ | .slt _ | .sltu _
  | .andi _ | .ori _ | .xori _ | .slti _ | .sltiu _
  | .sll _ | .srl _ | .sra _ | .slli _ | .srli _ | .srai _
  | .add _ | .addi _ | .subw _ | .addw _ | .addiw _
  | .sllw _ | .srlw _ | .sraw _ | .slliw _ | .srliw _ | .sraiw _
  | .mul _ | .mulh _ | .mulhsu _ | .mulw _ | .mulhu _
  | .div _ | .rem _ | .divw _ | .remw _ | .divu _ | .divuw _
  | .remu _ | .remuw _
  | .beq _ | .bne _ | .blt _ | .bge _ | .bltu _ | .bgeu _
  | .lui _ | .auipc _ | .jal _ | .jalr _ | .fence _ =>
      rowsOf i.val = []

/-- **The single named boot / cross-segment memory seed premise of `root_soundness`.**

    One shared assumption for the whole segment, replacing the ten former per-op memory residuals,
    stated concretely (see the module header): `memInit`/`boot` (boot seed), `step` (execution-
    successor), derived read-soundness inputs, and the structural `placement`.
    `memEvidence_of_bootSeed` derives every op's `MemoryOpEvidenceFor` residual from it by the
    execution-order fold.  The read-soundness field is no longer an opaque semantic predicate: it is
    reconstructed from accepted Mem replay evidence, the explicit initial-memory bridge, and a
    replay-safe order certificate. -/
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
  /-- Narrow replay/order inputs from which memory-carrying read-soundness is derived. The guard
      is the objective witness fact that a nonempty mutable-Mem table exists; memory-less traces do
      not fabricate a replay bridge. -/
  readSoundInputs :
    ∀ (h : MutableMemPresent ziskTrace.witness),
      BootSegmentReadSoundInputs ziskTrace memInit rowsOf h
  /-- If this seed emits any execution-order memory row, the accepted witness must contain a
      nonempty mutable-Mem table. Memory-less concrete witnesses discharge this field vacuously from
      `((List.range n).flatMap rowsOf) = []`; memory-carrying traces use it to enter the guarded
      replay bridge without weakening that bridge's obligations. -/
  memPresent_of_executionRows_nonempty :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf ≠ []) →
      MutableMemPresent ziskTrace.witness
  /-- Structural placement pinning `rowsOf` to each op's real bus rows (+ narrow-store bytes). -/
  placement : ∀ i : Fin ziskTrace.numInstructions,
    MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i)

/-- Derived memory-bus read-soundness for a memory-carrying concrete seed. -/
theorem readSound_of_bootSeed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs (seed.readSoundInputs h_present)

/-- Empty execution-order memory rows are read-sound without consulting any accepted Mem replay
bridge or initial-memory equality. -/
theorem readSound_of_empty_executionRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    (h_empty : ((List.range ziskTrace.numInstructions).flatMap rowsOf) = []) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  rw [h_empty]
  intro priorRows entry laterRows h_split _h_selected
  simp at h_split

/-- Seed-level empty-row read-soundness. This is the no-memory variant used by concrete witnesses
whose accepted trace has no mutable-Mem rows. -/
theorem readSound_of_bootSeed_noMemory
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_empty : ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) = []) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_empty_executionRows h_empty

theorem rowsOf_eq_memoryRowsOfStep_of_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i)
    (h_placement : MemoryOpPlacement ziskTrace rowsOf memInit i step) :
    rowsOf i.val = memoryRowsOfStep ziskTrace i step := by
  cases step <;> simp [memoryRowsOfStep, MemoryOpPlacement] at h_placement ⊢
  all_goals
    first
    | exact h_placement
    | exact h_placement.1

/-- Placement identifies the whole execution-order `rowsOf` list with the
structural per-step decoder row list, not merely row membership. This is the
duplicate-sensitive form needed by row-correspondence/order-certificate proofs. -/
theorem executionRows_eq_memoryRowsOfSteps_of_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i)) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf) =
      executionMemoryRowsOfSteps ziskTrace ziskStep := by
  rw [executionMemoryRowsOfSteps]
  rw [← List.map_coe_finRange_eq_range]
  induction List.finRange ziskTrace.numInstructions with
  | nil => simp
  | cons i is ih =>
      simp [rowsOf_eq_memoryRowsOfStep_of_placement i (ziskStep i) (h_placement i), ih]

/-- Length consequence of structural placement for execution-order rows. -/
theorem executionRows_length_eq_memoryRowsOfSteps_of_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i)) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).length =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).length := by
  rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]

/-- Multiplicity consequence of structural placement for execution-order rows. -/
theorem executionRows_count_eq_memoryRowsOfSteps_of_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (entry : MemoryBusEntry FGL) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).count entry =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).count entry := by
  rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]

/-- Seed-level wrapper for the whole-list structural placement equality. -/
theorem BootSegmentMemorySeed.executionRows_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) =
      executionMemoryRowsOfSteps ziskTrace ziskStep :=
  executionRows_eq_memoryRowsOfSteps_of_placement seed.placement

/-- Seed-level length consequence of structural placement. -/
theorem BootSegmentMemorySeed.executionRows_length_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).length =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).length :=
  executionRows_length_eq_memoryRowsOfSteps_of_placement seed.placement

/-- Seed-level multiplicity consequence of structural placement. -/
theorem BootSegmentMemorySeed.executionRows_count_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (entry : MemoryBusEntry FGL) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).count entry =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).count entry :=
  executionRows_count_eq_memoryRowsOfSteps_of_placement seed.placement entry

/-- Seed-level permutation between accepted Mem replay rows and the structural
per-step decoder row list, conditional on the seed's replay-safe order
certificate. This composes the order certificate with structural placement so
later correspondence work can target decoder rows directly. -/
theorem BootSegmentMemorySeed.memReplayRows_perm_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness) :
    (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
  have h_perm := (seed.readSoundInputs h_present).memReplayRows_perm_executionRows
  rw [BootSegmentMemorySeed.executionRows_eq_memoryRowsOfSteps seed] at h_perm
  exact h_perm

/-- Length consequence for accepted Mem replay rows versus structural per-step
decoder rows. -/
theorem BootSegmentMemorySeed.memReplayRows_length_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness) :
    (ziskTrace.memReplayRows h_present).length =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).length := by
  have h_len := (seed.readSoundInputs h_present).memReplayRows_length_eq_executionRows
  rw [BootSegmentMemorySeed.executionRows_eq_memoryRowsOfSteps seed] at h_len
  exact h_len

/-- Multiplicity consequence for accepted Mem replay rows versus structural
per-step decoder rows. -/
theorem BootSegmentMemorySeed.memReplayRows_count_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (entry : MemoryBusEntry FGL) :
    (ziskTrace.memReplayRows h_present).count entry =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).count entry := by
  have h_count := (seed.readSoundInputs h_present).memReplayRows_count_eq_executionRows entry
  rw [BootSegmentMemorySeed.executionRows_eq_memoryRowsOfSteps seed] at h_count
  exact h_count

/-- Accepted Mem replay rows occur in the structural per-step decoder row list
when transported through the seed's replay-safe order certificate and
placement. -/
theorem BootSegmentMemorySeed.mem_memoryRowsOfSteps_of_memReplayRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_present) :
    entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep :=
  (seed.memReplayRows_perm_memoryRowsOfSteps h_present).mem_iff.mp h_entry

/-- Structural per-step decoder rows occur in accepted Mem replay rows when
transported back through the seed's replay-safe order certificate and
placement. -/
theorem BootSegmentMemorySeed.memReplayRows_of_mem_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  (seed.memReplayRows_perm_memoryRowsOfSteps h_present).mem_iff.mpr h_entry

/-- Membership in the structural per-step decoder row list is exactly
membership in one decoded step's structural memory rows. -/
theorem exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep) :
    ∃ i : Fin ziskTrace.numInstructions, entry ∈ memoryRowsOfStep ziskTrace i (ziskStep i) := by
  rw [executionMemoryRowsOfSteps] at h_entry
  obtain ⟨i, _h_i, h_entry⟩ := List.mem_flatMap.mp h_entry
  exact ⟨i, h_entry⟩

/-- A structural row emitted by one decoded step is in the full structural
per-step decoder row list. -/
theorem mem_executionMemoryRowsOfSteps_of_memoryRowsOfStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (i : Fin ziskTrace.numInstructions)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i (ziskStep i)) :
    entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep := by
  rw [executionMemoryRowsOfSteps]
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, h_entry⟩

/-- Each decoded step emits at most one structural memory row, hence no
duplicates inside the step-local memory-row list. -/
theorem memoryRowsOfStep_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i) :
    (memoryRowsOfStep ziskTrace i step).Nodup := by
  cases step <;> simp [memoryRowsOfStep]

/-- Each decoded step emits at most one structural memory row. -/
theorem memoryRowsOfStep_length_le_one
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i) :
    (memoryRowsOfStep ziskTrace i step).length ≤ 1 := by
  cases step <;> simp [memoryRowsOfStep]

/-- Two rows emitted by the same decoded step are equal. -/
theorem memoryRowsOfStep_eq_of_mem
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    {step : ZiskStep ziskTrace i}
    {left right : MemoryBusEntry FGL}
    (h_left : left ∈ memoryRowsOfStep ziskTrace i step)
    (h_right : right ∈ memoryRowsOfStep ziskTrace i step) :
    left = right := by
  have h_len_le := memoryRowsOfStep_length_le_one i step
  have h_len_pos : 0 < (memoryRowsOfStep ziskTrace i step).length :=
    List.length_pos_of_mem h_left
  have h_len_eq : (memoryRowsOfStep ziskTrace i step).length = 1 := by
    omega
  obtain ⟨only, h_singleton⟩ := List.length_eq_one_iff.mp h_len_eq
  rw [h_singleton] at h_left h_right
  exact (List.eq_of_mem_singleton h_left).trans
    (List.eq_of_mem_singleton h_right).symm

/-- Named syntactic residue for the timestamp/range side of scoped structural
row duplicate-freedom.

This says only that two different decoded instruction indices do not emit
structural memory rows with the same timestamp. It is intentionally narrower
than list disjointness, and it carries no read-value agreement. -/
@[reducible]
def MemoryRowsOfStepIndexwiseTimestampDisjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) : Prop :=
  ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
    ∀ entry_i entry_j : MemoryBusEntry FGL,
      entry_i ∈ memoryRowsOfStep ziskTrace i (ziskStep i) →
      entry_j ∈ memoryRowsOfStep ziskTrace j (ziskStep j) →
      entry_i.timestamp ≠ entry_j.timestamp

/-- Shared Main+ROM row used by the structural load and store memory rows at
trace index `i`. The load/store construction modules expose separate names,
but both are this same underlying Main table row. -/
@[reducible]
noncomputable def mainRowWithRom
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero
    ziskTrace.program ziskTrace.mainTable i.val

/-- The load-side Main row accessor is definitionally the shared Main row. -/
theorem mainRowWithRomLd_eq_mainRowWithRom
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    mainRowWithRomLd ziskTrace i = mainRowWithRom ziskTrace i := by
  rfl

/-- The store-side Main row accessor is definitionally the shared Main row. -/
theorem mainRowWithRomSt_eq_mainRowWithRom
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    mainRowWithRomSt ziskTrace i = mainRowWithRom ziskTrace i := by
  rfl

/-- The concrete load row emitted by `memoryRowsOfStep` uses Main's b-side
memory timestamp formula. -/
theorem busLd_e1_timestamp
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1.timestamp =
      2 + (mainRowWithRom ziskTrace i).rom.main_step * 4 := by
  rfl

/-- The concrete store row emitted by `memoryRowsOfStep` uses Main's c-side
memory timestamp formula. -/
theorem busSt_e2_timestamp
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2.timestamp =
      3 + (mainRowWithRom ziskTrace i).rom.main_step * 4 := by
  rfl

/-- Formula-level timestamp inequalities for the rows that `memoryRowsOfStep`
can emit, written directly in terms of the shared Main `main_step` column for
each trace index.

This is the shape expected from a later PIL/range proof for `STEP =
main_segment * N + SEGMENT_STEP`; it does not assert that `main_step` is the
trace index. -/
@[reducible]
def MemoryRowsOfStepIndexwiseMainStepTimestampSeparated
    (ziskTrace : AcceptedZiskTrace numInstructions) : Prop :=
  ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
    2 + (mainRowWithRom ziskTrace i).rom.main_step * 4 ≠
      2 + (mainRowWithRom ziskTrace j).rom.main_step * 4 ∧
    2 + (mainRowWithRom ziskTrace i).rom.main_step * 4 ≠
      3 + (mainRowWithRom ziskTrace j).rom.main_step * 4 ∧
    3 + (mainRowWithRom ziskTrace i).rom.main_step * 4 ≠
      2 + (mainRowWithRom ziskTrace j).rom.main_step * 4 ∧
    3 + (mainRowWithRom ziskTrace i).rom.main_step * 4 ≠
      3 + (mainRowWithRom ziskTrace j).rom.main_step * 4

/-- Main `main_step` values are distinct at unequal trace indices. This is
the same-offset half of timestamp separation: load/load and store/store
collisions follow by cancellation of the nonzero `* 4` scale factor. -/
@[reducible]
def MemoryRowsOfStepIndexwiseMainStepDistinct
    (ziskTrace : AcceptedZiskTrace numInstructions) : Prop :=
  ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
    (mainRowWithRom ziskTrace i).rom.main_step ≠
      (mainRowWithRom ziskTrace j).rom.main_step

/-- Cross-offset no-collision residue for Main memory timestamps at unequal
trace indices.

Together with distinct `main_step` values, this proves the full four-case
timestamp separation predicate. The remaining proof should come from the same
range/no-wrap facts that justify `STEP = main_segment * N + SEGMENT_STEP`. -/
@[reducible]
def MemoryRowsOfStepIndexwiseMainStepCrossOffsetSeparated
    (ziskTrace : AcceptedZiskTrace numInstructions) : Prop :=
  ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
    2 + (mainRowWithRom ziskTrace i).rom.main_step * 4 ≠
      3 + (mainRowWithRom ziskTrace j).rom.main_step * 4 ∧
    3 + (mainRowWithRom ziskTrace i).rom.main_step * 4 ≠
      2 + (mainRowWithRom ziskTrace j).rom.main_step * 4

/-- The accepted-trace Main `main_step` index certificate specialized to the
shared Main+ROM row accessor used by structural memory rows. -/
theorem mainRowWithRom_main_step_eq_index
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    (mainRowWithRom ziskTrace i).rom.main_step = (i.val : FGL) :=
  ziskTrace.mainTable_main_step_index_fixed.main_step_eq_index i

/-- Load-side timestamp no-wrap evidence specialized to `mainRowWithRom`. -/
theorem mainRowWithRom_load_timestamp_toNat
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    (2 + (mainRowWithRom ziskTrace i).rom.main_step * 4).toNat =
      2 + 4 * i.val :=
  ziskTrace.mainTable_main_step_index_fixed.load_timestamp_toNat i

/-- Store-side timestamp no-wrap evidence specialized to `mainRowWithRom`. -/
theorem mainRowWithRom_store_timestamp_toNat
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) :
    (3 + (mainRowWithRom ziskTrace i).rom.main_step * 4).toNat =
      3 + 4 * i.val :=
  ziskTrace.mainTable_main_step_index_fixed.store_timestamp_toNat i

/-- The consolidated Main-step index certificate implies the old same-offset
`main_step` distinctness residue. -/
theorem memoryRowsOfStep_mainStep_distinct_of_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions} :
    MemoryRowsOfStepIndexwiseMainStepDistinct ziskTrace := by
  intro i j h_ne h_eq
  have h_ts_eq :
      (2 + (mainRowWithRom ziskTrace i).rom.main_step * 4).toNat =
        (2 + (mainRowWithRom ziskTrace j).rom.main_step * 4).toNat := by
    rw [h_eq]
  have h_i := mainRowWithRom_load_timestamp_toNat ziskTrace i
  have h_j := mainRowWithRom_load_timestamp_toNat ziskTrace j
  rw [h_i, h_j] at h_ts_eq
  have h_val : i.val = j.val := by omega
  exact h_ne (Fin.ext h_val)

/-- The consolidated Main-step index certificate implies the old cross-offset
no-collision residue. -/
theorem memoryRowsOfStep_mainStep_crossOffsetSeparated_of_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions} :
    MemoryRowsOfStepIndexwiseMainStepCrossOffsetSeparated ziskTrace := by
  intro i j _h_ne
  constructor
  · intro h_eq
    have h_nat :
        (2 + (mainRowWithRom ziskTrace i).rom.main_step * 4).toNat =
          (3 + (mainRowWithRom ziskTrace j).rom.main_step * 4).toNat := by
      rw [h_eq]
    have h_i := mainRowWithRom_load_timestamp_toNat ziskTrace i
    have h_j := mainRowWithRom_store_timestamp_toNat ziskTrace j
    rw [h_i, h_j] at h_nat
    -- `h_eq` is an `FGL = Fin GL_prime` equation; `omega` would expand its
    -- composite `Fin` arithmetic modulo the 2^64-scale Goldilocks prime.
    clear h_eq h_i h_j
    omega
  · intro h_eq
    have h_nat :
        (3 + (mainRowWithRom ziskTrace i).rom.main_step * 4).toNat =
          (2 + (mainRowWithRom ziskTrace j).rom.main_step * 4).toNat := by
      rw [h_eq]
    have h_i := mainRowWithRom_store_timestamp_toNat ziskTrace i
    have h_j := mainRowWithRom_load_timestamp_toNat ziskTrace j
    rw [h_i, h_j] at h_nat
    clear h_eq h_i h_j
    omega

/-- Same-offset timestamp collision is impossible for distinct Main steps on
the load-side offset. -/
theorem two_add_mul_four_ne_of_ne (x y : FGL) (h_ne : x ≠ y) :
    2 + x * 4 ≠ 2 + y * 4 := by
  intro h_eq
  have h_mul : x * 4 = y * 4 := by
    exact add_left_cancel h_eq
  have h_four : (4 : FGL) ≠ 0 := by
    decide
  exact h_ne (mul_right_cancel₀ h_four h_mul)

/-- Same-offset timestamp collision is impossible for distinct Main steps on
the store-side offset. -/
theorem three_add_mul_four_ne_of_ne (x y : FGL) (h_ne : x ≠ y) :
    3 + x * 4 ≠ 3 + y * 4 := by
  intro h_eq
  have h_mul : x * 4 = y * 4 := by
    exact add_left_cancel h_eq
  have h_four : (4 : FGL) ≠ 0 := by
    decide
  exact h_ne (mul_right_cancel₀ h_four h_mul)

/-- Distinct Main steps plus the cross-offset no-collision facts imply the
full formula-level timestamp separation predicate. -/
theorem memoryRowsOfStep_mainStep_timestamp_separated_of_distinct_crossOffset
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (h_distinct : MemoryRowsOfStepIndexwiseMainStepDistinct ziskTrace)
    (h_cross : MemoryRowsOfStepIndexwiseMainStepCrossOffsetSeparated ziskTrace) :
    MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace := by
  intro i j h_ne
  have h_step_ne := h_distinct i j h_ne
  obtain ⟨h_load_store, h_store_load⟩ := h_cross i j h_ne
  exact ⟨
    two_add_mul_four_ne_of_ne
      (mainRowWithRom ziskTrace i).rom.main_step
      (mainRowWithRom ziskTrace j).rom.main_step
      h_step_ne,
    h_load_store,
    h_store_load,
    three_add_mul_four_ne_of_ne
      (mainRowWithRom ziskTrace i).rom.main_step
      (mainRowWithRom ziskTrace j).rom.main_step
      h_step_ne⟩

/-- The single Main-step index certificate discharges the full formula-level
timestamp separation predicate formerly assembled from two step-counter
residues. -/
theorem memoryRowsOfStep_mainStep_timestamp_separated_of_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions} :
    MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace :=
  memoryRowsOfStep_mainStep_timestamp_separated_of_distinct_crossOffset
    memoryRowsOfStep_mainStep_distinct_of_main_step_index_fixed
    memoryRowsOfStep_mainStep_crossOffsetSeparated_of_main_step_index_fixed

/-- Concrete structural timestamp inequalities for the rows that
`memoryRowsOfStep` can emit.

The four cases cover load/load, load/store, store/load, and store/store rows
for two unequal decoded instruction indices. Later range work can target this
syntactic shape directly. -/
@[reducible]
def MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint
    (ziskTrace : AcceptedZiskTrace numInstructions) : Prop :=
  ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1.timestamp ≠
      (busLd ziskTrace j (Pilot.execRowOf ziskTrace j)).e1.timestamp ∧
    (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1.timestamp ≠
      (busSt ziskTrace j (Pilot.execRowOf ziskTrace j)).e2.timestamp ∧
    (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2.timestamp ≠
      (busLd ziskTrace j (Pilot.execRowOf ziskTrace j)).e1.timestamp ∧
    (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2.timestamp ≠
      (busSt ziskTrace j (Pilot.execRowOf ziskTrace j)).e2.timestamp

/-- The formula-level Main-step timestamp separation implies the same four-case
predicate over the concrete structural rows. -/
theorem memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace := by
  intro i j h_ne
  simpa [busLd_e1_timestamp, busSt_e2_timestamp] using h_timestamp i j h_ne

/-- Distinct Main steps plus cross-offset no-collision facts imply the
structural load/store timestamp-disjoint predicate. -/
theorem memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_distinct_crossOffset
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (h_distinct : MemoryRowsOfStepIndexwiseMainStepDistinct ziskTrace)
    (h_cross : MemoryRowsOfStepIndexwiseMainStepCrossOffsetSeparated ziskTrace) :
    MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace :=
  memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
    (memoryRowsOfStep_mainStep_timestamp_separated_of_distinct_crossOffset
      h_distinct h_cross)

/-- Any structural row emitted by a decoded step is either the step's concrete
load memory row or its concrete store memory row. No-memory steps have no rows. -/
theorem memoryRowsOfStep_eq_load_or_store_of_mem
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    {step : ZiskStep ziskTrace i}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry = (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1
      ∨ entry = (busSt ziskTrace i (Pilot.execRowOf ziskTrace i)).e2 := by
  cases step <;> simp [memoryRowsOfStep] at h_entry ⊢
  all_goals first | exact Or.inl h_entry | exact Or.inr h_entry

/-- Step-local target-order timestamp shape derived from the consolidated
Main-step index certificate: every structural memory row emitted by trace index
`i` has timestamp representative `2 + 4*i` (load) or `3 + 4*i` (store). -/
theorem memoryRowsOfStep_timestamp_toNat_eq_load_or_store_offset
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i : Fin ziskTrace.numInstructions}
    {step : ZiskStep ziskTrace i}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry.timestamp.toNat = 2 + 4 * i.val ∨
      entry.timestamp.toNat = 3 + 4 * i.val := by
  rcases memoryRowsOfStep_eq_load_or_store_of_mem h_entry with h_entry | h_entry
  · subst entry
    left
    simpa [busLd_e1_timestamp] using mainRowWithRom_load_timestamp_toNat ziskTrace i
  · subst entry
    right
    simpa [busSt_e2_timestamp] using mainRowWithRom_store_timestamp_toNat ziskTrace i

/-- Rows emitted by strictly increasing trace indices are chronologically
monotone in the target execution list. -/
theorem memoryRowsOfStep_timestamp_toNat_le_of_index_lt
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {i j : Fin ziskTrace.numInstructions}
    (h_lt : i < j)
    {entry_i entry_j : MemoryBusEntry FGL}
    (h_entry_i : entry_i ∈ memoryRowsOfStep ziskTrace i (ziskStep i))
    (h_entry_j : entry_j ∈ memoryRowsOfStep ziskTrace j (ziskStep j)) :
    entry_i.timestamp.toNat ≤ entry_j.timestamp.toNat := by
  have h_i :=
    memoryRowsOfStep_timestamp_toNat_eq_load_or_store_offset
      (ziskTrace := ziskTrace) h_entry_i
  have h_j :=
    memoryRowsOfStep_timestamp_toNat_eq_load_or_store_offset
      (ziskTrace := ziskTrace) h_entry_j
  have h_val_lt : i.val < j.val := h_lt
  rcases h_i with h_i | h_i <;> rcases h_j with h_j | h_j
  · rw [h_i, h_j]
    omega
  · rw [h_i, h_j]
    omega
  · rw [h_i, h_j]
    omega
  · rw [h_i, h_j]
    omega

/-- Each step-local structural memory-row list is chronologically ordered. At
the moment each decoded step emits at most one load/store row, so the local
side of the flatMap order proof is structural. -/
theorem memoryRowsOfStep_pairwise_timestamp_toNat_le
    {ziskTrace : AcceptedZiskTrace numInstructions}
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i) :
    (memoryRowsOfStep ziskTrace i step).Pairwise
      (fun left right => left.timestamp.toNat ≤ right.timestamp.toNat) := by
  cases step <;> simp [memoryRowsOfStep]

/-- The consolidated Main-step index certificate gives the full execution-order
target chronology over structural memory rows. -/
theorem executionMemoryRowsOfSteps_pairwise_timestamp_toNat_le_of_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i} :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Pairwise
      (fun left right => left.timestamp.toNat ≤ right.timestamp.toNat) := by
  rw [executionMemoryRowsOfSteps, List.pairwise_flatMap]
  constructor
  · intro i _h_i
    exact memoryRowsOfStep_pairwise_timestamp_toNat_le i (ziskStep i)
  · exact List.Pairwise.imp
      (fun {i j} h_lt => by
        intro entry_i h_entry_i entry_j h_entry_j
        exact memoryRowsOfStep_timestamp_toNat_le_of_index_lt
          (ziskTrace := ziskTrace) (ziskStep := ziskStep) h_lt h_entry_i h_entry_j)
      (List.pairwise_lt_finRange ziskTrace.numInstructions)

/-- Sublist-aware target chronology needed by the crossed-pair permutation
builder. The recursive builder works over sublists of the target list, so the
order fact is stated directly in that shape. -/
@[reducible]
def ExecutionMemoryRowsTargetChronological
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) : Prop :=
  ∀ {currentTarget row moved},
    List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
    MemoryBusRowsPairBefore row moved currentTarget →
    row.timestamp.toNat ≤ moved.timestamp.toNat

/-- A concrete pair-before witness contains the corresponding two-element
sublist. -/
theorem memoryBusRowsPairBefore_pair_sublist
    {left right : MemoryBusEntry FGL}
    {rows : List (MemoryBusEntry FGL)}
    (h_before : MemoryBusRowsPairBefore left right rows) :
    [left, right].Sublist rows := by
  rcases h_before with ⟨pref, middle, suffix, h_rows⟩
  subst rows
  have h_tail : [right].Sublist (middle ++ right :: suffix) :=
    (List.Sublist.cons₂ right (List.nil_sublist suffix)).trans
      (List.sublist_append_right middle (right :: suffix))
  have h_pair : [left, right].Sublist (left :: middle ++ right :: suffix) :=
    List.Sublist.cons₂ left h_tail
  have h_pref :
      (left :: middle ++ right :: suffix).Sublist
        (pref ++ left :: middle ++ right :: suffix) := by
    induction pref with
    | nil => simp
    | cons a pref ih =>
        exact List.Sublist.cons a ih
  exact h_pair.trans h_pref

/-- Source-order chronology for a crossed pair in an accepted Mem replay
sublist, specialized to equal byte pointers. -/
theorem acceptedMemReplayRows_timestamp_toNat_le_of_pairBefore_same_ptr
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {h_present : MutableMemPresent ziskTrace.witness}
    {currentSource : List (MemoryBusEntry FGL)}
    {moved row : MemoryBusEntry FGL}
    (h_source_sublist : List.Sublist currentSource (ziskTrace.memReplayRows h_present))
    (h_before : MemoryBusRowsPairBefore moved row currentSource)
    (h_ptr_eq : moved.ptr.toNat = row.ptr.toNat) :
    moved.timestamp.toNat ≤ row.timestamp.toNat := by
  have h_pair_source : [moved, row].Sublist (ziskTrace.memReplayRows h_present) :=
    (memoryBusRowsPairBefore_pair_sublist h_before).trans h_source_sublist
  exact
    (List.pairwise_iff_forall_sublist.mp
      acceptedMemReplayRows_pairwise_timestamp_toNat_le_of_same_ptr)
      h_pair_source h_ptr_eq

/-- Pairwise target chronology implies the sublist-aware crossed-pair target
chronology shape. -/
theorem executionMemoryRowsOfSteps_targetChronological_of_pairwise_timestamp_toNat_le
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_pairwise :
      (executionMemoryRowsOfSteps ziskTrace ziskStep).Pairwise
        (fun left right => left.timestamp.toNat ≤ right.timestamp.toNat)) :
    ExecutionMemoryRowsTargetChronological ziskTrace ziskStep := by
  intro currentTarget row moved h_sublist h_before
  have h_pair_target :
      [row, moved].Sublist (executionMemoryRowsOfSteps ziskTrace ziskStep) :=
    (memoryBusRowsPairBefore_pair_sublist h_before).trans h_sublist
  exact (List.pairwise_iff_forall_sublist.mp h_pairwise) h_pair_target

/-- The consolidated Main-step index certificate supplies the target execution
chronology over `executionMemoryRowsOfSteps`, including the sublist shape used by
the no-unsafe-crossings permutation builder. -/
theorem executionMemoryRowsOfSteps_targetChronological_of_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i} :
    ExecutionMemoryRowsTargetChronological ziskTrace ziskStep :=
  executionMemoryRowsOfSteps_targetChronological_of_pairwise_timestamp_toNat_le
    executionMemoryRowsOfSteps_pairwise_timestamp_toNat_le_of_main_step_index_fixed

/-- Unequal timestamps for every pair of step-local structural rows imply the
two step-local row lists are disjoint. -/
theorem memoryRowsOfStep_disjoint_of_timestamp_ne
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {i j : Fin ziskTrace.numInstructions}
    {step_i : ZiskStep ziskTrace i}
    {step_j : ZiskStep ziskTrace j}
    (h_timestamp : ∀ entry_i entry_j : MemoryBusEntry FGL,
      entry_i ∈ memoryRowsOfStep ziskTrace i step_i →
      entry_j ∈ memoryRowsOfStep ziskTrace j step_j →
      entry_i.timestamp ≠ entry_j.timestamp) :
    List.Disjoint (memoryRowsOfStep ziskTrace i step_i)
      (memoryRowsOfStep ziskTrace j step_j) := by
  intro entry h_i h_j
  exact h_timestamp entry entry h_i h_j rfl

/-- The four concrete structural timestamp inequalities imply the entry-level
indexwise timestamp-disjoint predicate. -/
theorem memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep := by
  intro i j h_ne entry_i entry_j h_i h_j
  obtain ⟨h_ll, h_ls, h_sl, h_ss⟩ := h_timestamp i j h_ne
  rcases memoryRowsOfStep_eq_load_or_store_of_mem h_i with h_i_load | h_i_store
  · rcases memoryRowsOfStep_eq_load_or_store_of_mem h_j with h_j_load | h_j_store
    · rw [h_i_load, h_j_load]
      exact h_ll
    · rw [h_i_load, h_j_store]
      exact h_ls
  · rcases memoryRowsOfStep_eq_load_or_store_of_mem h_j with h_j_load | h_j_store
    · rw [h_i_store, h_j_load]
      exact h_sl
    · rw [h_i_store, h_j_store]
      exact h_ss

/-- Structural duplicate-freedom for execution memory rows from per-step
duplicate-freedom plus pairwise-disjoint step row lists.

This is the row-list shape expected from a later timestamp/range argument:
prove each decoded step emits no duplicate memory rows, and prove two distinct
decoded steps cannot emit the same concrete memory row. -/
theorem executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup := by
  rw [executionMemoryRowsOfSteps]
  exact List.nodup_flatMap.mpr ⟨fun i _ => h_step_nodup i, h_pairwise⟩

/-- Structural duplicate-freedom for execution memory rows from only
pairwise-disjoint step row lists.

The per-step duplicate-freedom side is discharged by
`memoryRowsOfStep_nodup`, because each structural step emits either zero or
one memory-bus row. -/
theorem executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup :=
  executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint
    (fun i => memoryRowsOfStep_nodup i (ziskStep i)) h_pairwise

/-- Build the pairwise structural row-disjointness shape from an indexwise
obligation over unequal decoded steps. -/
theorem pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    (List.finRange ziskTrace.numInstructions).Pairwise
      (fun i j =>
        List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
          (memoryRowsOfStep ziskTrace j (ziskStep j))) :=
  (List.nodup_finRange ziskTrace.numInstructions).pairwise_of_forall_ne
    (fun i _ j _ h_ne => h_disjoint i j h_ne)

/-- Indexwise timestamp separation implies the indexwise list-disjointness
obligation for structural step rows. -/
theorem indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j)) :=
  fun i j h_ne => memoryRowsOfStep_disjoint_of_timestamp_ne (h_timestamp i j h_ne)

/-- Build pairwise structural row-disjointness from indexwise timestamp
separation between unequal decoded steps. -/
theorem pairwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    (List.finRange ziskTrace.numInstructions).Pairwise
      (fun i j =>
        List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
          (memoryRowsOfStep ziskTrace j (ziskStep j))) :=
  pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint
    (indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint h_timestamp)

/-- Structural duplicate-freedom for execution memory rows from indexwise
disjointness between unequal decoded steps. -/
theorem executionMemoryRowsOfSteps_nodup_of_indexwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup :=
  executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint_memoryRows
    (pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint h_disjoint)

/-- Structural duplicate-freedom for execution memory rows from indexwise
timestamp separation between unequal decoded steps. -/
theorem executionMemoryRowsOfSteps_nodup_of_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup :=
  executionMemoryRowsOfSteps_nodup_of_indexwise_disjoint_memoryRows
    (indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint h_timestamp)

/-- Structural duplicate-freedom for execution memory rows from the four
concrete load/store timestamp inequalities. -/
theorem executionMemoryRowsOfSteps_nodup_of_structural_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup :=
  executionMemoryRowsOfSteps_nodup_of_indexwise_timestamp_disjoint
    (memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
      h_timestamp)

/-- Structural duplicate-freedom for execution memory rows from formula-level
Main-step timestamp separation. -/
theorem executionMemoryRowsOfSteps_nodup_of_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup :=
  executionMemoryRowsOfSteps_nodup_of_structural_timestamp_disjoint
    (memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
      h_timestamp)

/-- Two structural execution rows with the same timestamp are the same row.

The consolidated Main-step index certificate rules out equal timestamps across
different decoded steps; within one decoded step, `memoryRowsOfStep` emits at
most one row. -/
theorem executionMemoryRowsOfSteps_eq_of_timestamp_toNat_eq
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {left right : MemoryBusEntry FGL}
    (h_left : left ∈ executionMemoryRowsOfSteps ziskTrace ziskStep)
    (h_right : right ∈ executionMemoryRowsOfSteps ziskTrace ziskStep)
    (h_timestamp_eq : left.timestamp.toNat = right.timestamp.toNat) :
    left = right := by
  obtain ⟨i, h_left_i⟩ :=
    exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps h_left
  obtain ⟨j, h_right_j⟩ :=
    exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps h_right
  by_cases h_idx : i = j
  · subst j
    exact memoryRowsOfStep_eq_of_mem h_left_i h_right_j
  · have h_timestamp :
        MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep :=
      memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
        (memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
          memoryRowsOfStep_mainStep_timestamp_separated_of_main_step_index_fixed)
    have h_timestamp_fin : left.timestamp = right.timestamp := Fin.ext h_timestamp_eq
    exact False.elim
      ((h_timestamp i j h_idx left right h_left_i h_right_j) h_timestamp_fin)

/-- Equal-timestamp target crossings are vacuous for structural execution
rows: timestamp equality identifies the row, while the pair-before witness
would require two occurrences in the `Nodup` target list. -/
theorem executionMemoryRowsOfSteps_noActiveWriteOverlap_of_pairBefore_timestamp_toNat_eq
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {currentTarget : List (MemoryBusEntry FGL)}
    {row moved : MemoryBusEntry FGL}
    (h_sublist :
      List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_before : MemoryBusRowsPairBefore row moved currentTarget)
    (h_timestamp_eq : row.timestamp.toNat = moved.timestamp.toNat) :
    MemoryBusEntryNoActiveWriteOverlap row moved ∧
      MemoryBusEntryNoActiveWriteOverlap moved row := by
  have h_pair_target :
      [row, moved].Sublist (executionMemoryRowsOfSteps ziskTrace ziskStep) :=
    (memoryBusRowsPairBefore_pair_sublist h_before).trans h_sublist
  have h_row_mem : row ∈ executionMemoryRowsOfSteps ziskTrace ziskStep :=
    List.Sublist.mem (by simp) h_pair_target
  have h_moved_mem : moved ∈ executionMemoryRowsOfSteps ziskTrace ziskStep :=
    List.Sublist.mem (by simp) h_pair_target
  have h_row_eq_moved :
      row = moved :=
    executionMemoryRowsOfSteps_eq_of_timestamp_toNat_eq h_row_mem h_moved_mem h_timestamp_eq
  have h_nodup :
      (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup :=
    executionMemoryRowsOfSteps_nodup_of_mainStep_timestamp_separated
      memoryRowsOfStep_mainStep_timestamp_separated_of_main_step_index_fixed
  subst moved
  have h_pair_nodup : ([row, row] : List (MemoryBusEntry FGL)).Nodup :=
    List.Nodup.sublist h_pair_target h_nodup
  exfalso
  simp at h_pair_nodup

/-- Crossed source/target pairs are replay-safe once accepted Mem source order
and structural execution target order are both exposed.

Different generated Mem addresses are byte-disjoint. For the same generated
address, both rows have the same byte pointer; source order gives
`moved.timestamp ≤ row.timestamp`, target order gives the reverse, and target
timestamp separation makes the crossing impossible. -/
theorem acceptedMemReplayRows_noActiveWriteOverlap_of_crossed_source_target
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {h_present : MutableMemPresent ziskTrace.witness}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {currentSource currentTarget : List (MemoryBusEntry FGL)}
    {row moved : MemoryBusEntry FGL}
    (h_source_sublist : List.Sublist currentSource (ziskTrace.memReplayRows h_present))
    (h_target_sublist :
      List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_source_before : MemoryBusRowsPairBefore moved row currentSource)
    (h_target_before : MemoryBusRowsPairBefore row moved currentTarget) :
    MemoryBusEntryNoActiveWriteOverlap row moved ∧
      MemoryBusEntryNoActiveWriteOverlap moved row := by
  have h_pair_source : [moved, row].Sublist (ziskTrace.memReplayRows h_present) :=
    (memoryBusRowsPairBefore_pair_sublist h_source_before).trans h_source_sublist
  have h_moved_mem : moved ∈ ziskTrace.memReplayRows h_present :=
    List.Sublist.mem (by simp) h_pair_source
  have h_row_mem : row ∈ ziskTrace.memReplayRows h_present :=
    List.Sublist.mem (by simp) h_pair_source
  obtain ⟨movedIdx, h_moved_entry⟩ :=
    acceptedMemReplayRows_exists_active_rowAt (ziskTrace := ziskTrace) h_moved_mem
  obtain ⟨rowIdx, h_row_entry⟩ :=
    acceptedMemReplayRows_exists_active_rowAt (ziskTrace := ziskTrace) h_row_mem
  by_cases h_addr_ne :
      (ziskTrace.memReplayBridge h_present).mem.addr rowIdx.val ≠
        (ziskTrace.memReplayBridge h_present).mem.addr movedIdx.val
  · exact
      acceptedMemReplayRows_noActiveWriteOverlap_of_addr_ne
        (ziskTrace := ziskTrace) rowIdx movedIdx h_row_entry h_moved_entry h_addr_ne
  · have h_addr_eq :
        (ziskTrace.memReplayBridge h_present).mem.addr movedIdx.val =
          (ziskTrace.memReplayBridge h_present).mem.addr rowIdx.val := by
      have h_row_moved :
          (ziskTrace.memReplayBridge h_present).mem.addr rowIdx.val =
            (ziskTrace.memReplayBridge h_present).mem.addr movedIdx.val := by
        by_contra h_addr
        exact h_addr_ne h_addr
      exact h_row_moved.symm
    have h_moved_range :
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem movedIdx.val).addr.val < 2 ^ 29 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using
        (ziskTrace.memReplayBridge h_present).rowRanges.addrColumns movedIdx
    have h_row_range :
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem rowIdx.val).addr.val < 2 ^ 29 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using
        (ziskTrace.memReplayBridge h_present).rowRanges.addrColumns rowIdx
    have h_moved_ptr :=
      activeMemReplayEntry_ptr_toNat_eq_addr_mul_eight
        h_moved_range h_moved_entry
    have h_row_ptr :=
      activeMemReplayEntry_ptr_toNat_eq_addr_mul_eight
        h_row_range h_row_entry
    have h_addr_row :
        (ZiskFv.AirsClean.Mem.rowAt
          (ziskTrace.memReplayBridge h_present).mem movedIdx.val).addr =
          (ZiskFv.AirsClean.Mem.rowAt
            (ziskTrace.memReplayBridge h_present).mem rowIdx.val).addr := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_addr_eq
    have h_ptr_eq : moved.ptr.toNat = row.ptr.toNat := by
      rw [h_moved_ptr, h_row_ptr, congrArg Fin.val h_addr_row]
    have h_source_le :
        moved.timestamp.toNat ≤ row.timestamp.toNat :=
      acceptedMemReplayRows_timestamp_toNat_le_of_pairBefore_same_ptr
        h_source_sublist h_source_before h_ptr_eq
    have h_target_le :
        row.timestamp.toNat ≤ moved.timestamp.toNat :=
      executionMemoryRowsOfSteps_targetChronological_of_main_step_index_fixed
        h_target_sublist h_target_before
    exact
      executionMemoryRowsOfSteps_noActiveWriteOverlap_of_pairBefore_timestamp_toNat_eq
        h_target_sublist h_target_before (Nat.le_antisymm h_target_le h_source_le)

/-- Placement form of structural duplicate-freedom for execution memory rows. -/
theorem executionRows_nodup_of_pairwise_disjoint_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup := by
  rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]
  exact executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint h_step_nodup h_pairwise

/-- Placement form of structural duplicate-freedom for execution memory rows,
with per-step duplicate-freedom discharged from `memoryRowsOfStep`. -/
theorem executionRows_nodup_of_pairwise_disjoint_memoryRows_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup := by
  rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]
  exact executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint_memoryRows h_pairwise

/-- Placement form of structural duplicate-freedom from indexwise disjointness
between unequal decoded steps. -/
theorem executionRows_nodup_of_indexwise_disjoint_memoryRows_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup :=
  executionRows_nodup_of_pairwise_disjoint_memoryRows_placement
    h_placement
    (pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint h_disjoint)

/-- Placement form of structural duplicate-freedom from indexwise timestamp
separation between unequal decoded steps. -/
theorem executionRows_nodup_of_indexwise_timestamp_disjoint_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup :=
  executionRows_nodup_of_indexwise_disjoint_memoryRows_placement
    h_placement
    (indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint h_timestamp)

/-- Placement form of structural duplicate-freedom from the four concrete
load/store timestamp inequalities. -/
theorem executionRows_nodup_of_structural_timestamp_disjoint_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup :=
  executionRows_nodup_of_indexwise_timestamp_disjoint_placement
    h_placement
    (memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
      h_timestamp)

/-- Placement form of structural duplicate-freedom from formula-level
Main-step timestamp separation. -/
theorem executionRows_nodup_of_mainStep_timestamp_separated_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup :=
  executionRows_nodup_of_structural_timestamp_disjoint_placement
    h_placement
    (memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
      h_timestamp)

/-- Seed-level wrapper for structural duplicate-freedom of execution memory
rows. -/
theorem BootSegmentMemorySeed.executionRows_nodup_of_pairwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup :=
  executionRows_nodup_of_pairwise_disjoint_placement
    seed.placement h_step_nodup h_pairwise

/-- Seed-level wrapper for structural duplicate-freedom of execution memory
rows, with the step-local `Nodup` side discharged from `memoryRowsOfStep`. -/
theorem BootSegmentMemorySeed.executionRows_nodup_of_pairwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup :=
  executionRows_nodup_of_pairwise_disjoint_memoryRows_placement
    seed.placement h_pairwise

/-- Seed-level wrapper for structural duplicate-freedom from indexwise
disjointness between unequal decoded steps. -/
theorem BootSegmentMemorySeed.executionRows_nodup_of_indexwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup :=
  executionRows_nodup_of_indexwise_disjoint_memoryRows_placement
    seed.placement h_disjoint

/-- Seed-level wrapper for structural duplicate-freedom from indexwise
timestamp separation between unequal decoded steps. -/
theorem BootSegmentMemorySeed.executionRows_nodup_of_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup :=
  executionRows_nodup_of_indexwise_timestamp_disjoint_placement
    seed.placement h_timestamp

/-- Seed-level wrapper for structural duplicate-freedom from the four concrete
load/store timestamp inequalities. -/
theorem BootSegmentMemorySeed.executionRows_nodup_of_structural_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup :=
  executionRows_nodup_of_structural_timestamp_disjoint_placement
    seed.placement h_timestamp

/-- Seed-level wrapper for structural duplicate-freedom from formula-level
Main-step timestamp separation. -/
theorem BootSegmentMemorySeed.executionRows_nodup_of_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup :=
  executionRows_nodup_of_mainStep_timestamp_separated_placement
    seed.placement h_timestamp

/-- Whole-structural-list membership direction for the scoped direct-Mem
correspondence.

Every row emitted by a decoded step classified as direct mutable-Mem or
no-memory occurs in accepted Mem replay rows. This is intentionally a
membership direction, not a full-list `Subperm`: duplicate-sensitive assembly
still needs the order/count work. -/
theorem AcceptedZiskTrace.memReplayRows_of_mem_executionMemoryRowsOfSteps_scopedDirect
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep) :
    entry ∈ ziskTrace.memReplayRows h_present := by
  obtain ⟨i, h_entry_i⟩ :=
    exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps h_entry
  exact ziskTrace.memReplayRows_of_scopedDirectMemRowsOfStep
    h_present i (h_steps i) h_entry_i

/-- Count-sensitive whole-list row correspondence for the scoped direct-Mem
case.

The scoped direct/no-memory predicates prove the support inclusion from
structural execution rows to accepted Mem replay rows. The extra `h_count_le`
premise is the remaining duplicate-sensitive obligation: for every accepted row
that appears in the structural support, accepted replay must contain at least
as many copies as the structural execution list. This deliberately does not
derive multiplicity from plain membership. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_count_le
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep →
        memoryBusEntryDecidableCount entry
            (executionMemoryRowsOfSteps ziskTrace ziskStep) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present)) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) := by
  letI : BEq (MemoryBusEntry FGL) :=
    @instBEqOfDecidableEq (MemoryBusEntry FGL) inferInstance
  rw [List.subperm_ext_iff]
  intro entry h_entry
  exact h_count_le entry
    (ziskTrace.memReplayRows_of_mem_executionMemoryRowsOfSteps_scopedDirect
      h_present h_steps h_entry)
    h_entry

/-- Whole-list scoped direct-Mem row correspondence from structural
deduplication.

If a later timestamp/range argument proves that the structural execution rows
are duplicate-free, the existing scoped direct support inclusion is already
strong enough to produce a full `Subperm`. This gives the multiplicity work a
more structural target than an arbitrary count inequality. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_nodup
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  h_nodup.subperm
    (fun _ h_entry =>
      ziskTrace.memReplayRows_of_mem_executionMemoryRowsOfSteps_scopedDirect
        h_present h_steps h_entry)

/-- Whole-list scoped direct-Mem row correspondence from per-step
duplicate-freedom plus pairwise-disjoint structural step row lists. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_pairwise_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_nodup
    h_present h_steps
    (executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint h_step_nodup h_pairwise)

/-- Whole-list scoped direct-Mem row correspondence from pairwise-disjoint
structural step row lists. The step-local duplicate-freedom side is discharged
by `memoryRowsOfStep_nodup`. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_pairwise_disjoint_memoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_nodup
    h_present h_steps
    (executionMemoryRowsOfSteps_nodup_of_pairwise_disjoint_memoryRows h_pairwise)

/-- Whole-list scoped direct-Mem row correspondence from indexwise
disjointness between unequal decoded steps. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_indexwise_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_pairwise_disjoint_memoryRows
    h_present h_steps
    (pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint h_disjoint)

/-- Whole-list scoped direct-Mem row correspondence from indexwise timestamp
separation between unequal decoded steps. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_indexwise_timestamp_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_indexwise_disjoint
    h_present h_steps
    (indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint h_timestamp)

/-- Whole-list scoped direct-Mem row correspondence from the four concrete
load/store timestamp inequalities. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_structural_timestamp_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_indexwise_timestamp_disjoint
    h_present h_steps
    (memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
      h_timestamp)

/-- Whole-list scoped direct-Mem row correspondence from formula-level
Main-step timestamp separation. -/
theorem AcceptedZiskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_mainStep_timestamp_separated
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    (executionMemoryRowsOfSteps ziskTrace ziskStep).Subperm
      (ziskTrace.memReplayRows h_present) :=
  ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_structural_timestamp_disjoint
    h_present h_steps
    (memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
      h_timestamp)

/-- Permutation form of the count-sensitive scoped direct-Mem row
correspondence.

The support/count premise gives the `Subperm` direction from structural
execution rows into accepted Mem replay rows. An independent length equality
turns that duplicate-sensitive inclusion into the row-correspondence
permutation expected by order-transfer assembly. -/
theorem AcceptedZiskTrace.memReplayRows_perm_executionMemoryRowsOfSteps_of_scopedDirect_count_le
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep →
        memoryBusEntryDecidableCount entry
            (executionMemoryRowsOfSteps ziskTrace ziskStep) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        (executionMemoryRowsOfSteps ziskTrace ziskStep).length) :
    (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
  have h_sub :=
    ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_count_le
      h_present h_steps h_count_le
  exact (h_sub.perm_of_length_le (Nat.le_of_eq h_length)).symm

/-- Permutation form of the `Nodup`-based scoped direct-Mem row
correspondence.

This is the same boundary as the count-sensitive theorem, but with structural
deduplication supplying the multiplicity side of the `Subperm`. -/
theorem AcceptedZiskTrace.memReplayRows_perm_executionMemoryRowsOfSteps_of_scopedDirect_nodup
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : (executionMemoryRowsOfSteps ziskTrace ziskStep).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        (executionMemoryRowsOfSteps ziskTrace ziskStep).length) :
    (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
  have h_sub :=
    ziskTrace.executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_nodup
      h_present h_steps h_nodup
  exact (h_sub.perm_of_length_le (Nat.le_of_eq h_length)).symm

/-- Placement transports the scoped direct-Mem membership direction from the
concrete execution-order `rowsOf` flatMap to accepted Mem replay rows. -/
theorem AcceptedZiskTrace.memReplayRows_of_mem_executionRows_scopedDirect_placement
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)) :
    entry ∈ ziskTrace.memReplayRows h_present := by
  have h_structural :
      entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep := by
    rwa [executionRows_eq_memoryRowsOfSteps_of_placement h_placement] at h_entry
  exact ziskTrace.memReplayRows_of_mem_executionMemoryRowsOfSteps_scopedDirect
    h_present h_steps h_structural

/-- Placement form of the count-sensitive scoped direct-Mem row
correspondence.

This is the concrete `rowsOf` version of
`executionMemoryRowsOfSteps_subperm_memReplayRows_of_scopedDirect_count_le`.
The support inclusion is derived from placement plus scoped direct/no-memory
classification; the caller still supplies the explicit per-entry count lower
bound needed for duplicate-sensitive row correspondence. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_count_le
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) →
        memoryBusEntryDecidableCount entry
            ((List.range ziskTrace.numInstructions).flatMap rowsOf) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present)) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) := by
  letI : BEq (MemoryBusEntry FGL) :=
    @instBEqOfDecidableEq (MemoryBusEntry FGL) inferInstance
  rw [List.subperm_ext_iff]
  intro entry h_entry
  exact h_count_le entry
    (ziskTrace.memReplayRows_of_mem_executionRows_scopedDirect_placement
      h_present h_placement h_steps h_entry)
    h_entry

/-- Placement form of the `Nodup`-based scoped direct-Mem row
correspondence. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_nodup
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  h_nodup.subperm
    (fun _ h_entry =>
      ziskTrace.memReplayRows_of_mem_executionRows_scopedDirect_placement
        h_present h_placement h_steps h_entry)

/-- Placement form of the pairwise-disjoint scoped direct-Mem row
correspondence. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_pairwise_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_nodup
    h_present h_placement h_steps
    (executionRows_nodup_of_pairwise_disjoint_placement
      h_placement h_step_nodup h_pairwise)

/-- Placement form of the pairwise-disjoint scoped direct-Mem row
correspondence, with step-local duplicate-freedom discharged from
`memoryRowsOfStep`. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_pairwise_disjoint_memoryRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_nodup
    h_present h_placement h_steps
    (executionRows_nodup_of_pairwise_disjoint_memoryRows_placement
      h_placement h_pairwise)

/-- Placement form of scoped direct-Mem row correspondence from indexwise
disjointness between unequal decoded steps. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_indexwise_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_pairwise_disjoint_memoryRows
    h_present h_placement h_steps
    (pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint h_disjoint)

/-- Placement form of scoped direct-Mem row correspondence from indexwise
timestamp separation between unequal decoded steps. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_indexwise_timestamp_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_indexwise_disjoint
    h_present h_placement h_steps
    (indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint h_timestamp)

/-- Placement form of scoped direct-Mem row correspondence from the four
concrete load/store timestamp inequalities. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_structural_timestamp_disjoint
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_indexwise_timestamp_disjoint
    h_present h_placement h_steps
    (memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
      h_timestamp)

/-- Placement form of scoped direct-Mem row correspondence from formula-level
Main-step timestamp separation. -/
theorem AcceptedZiskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_mainStep_timestamp_separated
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    (((List.range ziskTrace.numInstructions).flatMap rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_structural_timestamp_disjoint
    h_present h_placement h_steps
    (memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
      h_timestamp)

/-- Placement form of the count-sensitive scoped direct-Mem row-correspondence
permutation. -/
theorem AcceptedZiskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_count_le
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) →
        memoryBusEntryDecidableCount entry
            ((List.range ziskTrace.numInstructions).flatMap rowsOf) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  have h_sub :=
    ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_count_le
      h_present h_placement h_steps h_count_le
  exact (h_sub.perm_of_length_le (Nat.le_of_eq h_length)).symm

/-- Placement form of the `Nodup`-based scoped direct-Mem row-correspondence
permutation. -/
theorem AcceptedZiskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_nodup
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_present : MutableMemPresent ziskTrace.witness)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  have h_sub :=
    ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_nodup
      h_present h_placement h_steps h_nodup
  exact (h_sub.perm_of_length_le (Nat.le_of_eq h_length)).symm

/-- Seed-level wrapper for the scoped direct-Mem membership direction. -/
theorem BootSegmentMemorySeed.memReplayRows_of_mem_executionRows_scopedDirect
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf)) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  ziskTrace.memReplayRows_of_mem_executionRows_scopedDirect_placement
    h_present seed.placement h_steps h_entry

/-- Seed-level wrapper for the count-sensitive scoped direct-Mem row
correspondence. This packages the current Stage-2 boundary without using the
seed's replay-safe order certificate to prove row correspondence. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_count_le
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) →
        memoryBusEntryDecidableCount entry
            ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present)) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_count_le
    h_present seed.placement h_steps h_count_le

/-- Seed-level wrapper for the `Nodup`-based scoped direct-Mem row
correspondence. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_nodup
    h_present seed.placement h_steps h_nodup

/-- Seed-level wrapper for the pairwise-disjoint scoped direct-Mem
row-correspondence path. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_pairwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_pairwise_disjoint
    h_present seed.placement h_steps h_step_nodup h_pairwise

/-- Seed-level wrapper for the pairwise-disjoint scoped direct-Mem
row-correspondence path, with step-local duplicate-freedom discharged from
`memoryRowsOfStep`. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_pairwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j)))) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_pairwise_disjoint_memoryRows
    h_present seed.placement h_steps h_pairwise

/-- Seed-level wrapper for scoped direct-Mem row correspondence from indexwise
disjointness between unequal decoded steps. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_indexwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j))) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_indexwise_disjoint
    h_present seed.placement h_steps h_disjoint

/-- Seed-level wrapper for scoped direct-Mem row correspondence from indexwise
timestamp separation between unequal decoded steps. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_indexwise_timestamp_disjoint
    h_present seed.placement h_steps h_timestamp

/-- Seed-level wrapper for scoped direct-Mem row correspondence from the four
concrete load/store timestamp inequalities. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_structural_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_structural_timestamp_disjoint
    h_present seed.placement h_steps h_timestamp

/-- Seed-level wrapper for scoped direct-Mem row correspondence from formula-level
Main-step timestamp separation. -/
theorem BootSegmentMemorySeed.executionRows_subperm_memReplayRows_scopedDirect_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace) :
    (((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Subperm
      (ziskTrace.memReplayRows h_present)) :=
  ziskTrace.executionRows_subperm_memReplayRows_of_scopedDirect_placement_mainStep_timestamp_separated
    h_present seed.placement h_steps h_timestamp

/-- Seed-level permutation wrapper for count-sensitive scoped direct-Mem row
correspondence. -/
theorem BootSegmentMemorySeed.memReplayRows_perm_executionRows_scopedDirect_count_le
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) →
        memoryBusEntryDecidableCount entry
            ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).length) :
    (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  ziskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_count_le
    h_present seed.placement h_steps h_count_le h_length

/-- Seed-level permutation wrapper for the `Nodup` scoped direct-Mem
row-correspondence path. -/
theorem BootSegmentMemorySeed.memReplayRows_perm_executionRows_scopedDirect_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).length) :
    (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  ziskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_nodup
    h_present seed.placement h_steps h_nodup h_length

/-- Seed-level permutation wrapper using the named row-count certificate. -/
theorem BootSegmentMemorySeed.memReplayRows_perm_executionRows_scopedDirect_rowCount
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_present : MutableMemPresent ziskTrace.witness)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf).Nodup)
    (h_rowCount :
      ScopedDirectMemReplayLengthCertificate ziskTrace seed.rowsOf h_present) :
    (ziskTrace.memReplayRows h_present).Perm
      ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  seed.memReplayRows_perm_executionRows_scopedDirect_nodup
    h_present h_steps h_nodup h_rowCount.length_eq

/-- Structural row correspondence plus pairwise-safe accepted replay rows yield
the concrete boot replay-safe order certificate once placement identifies
`rowsOf` with `executionMemoryRowsOfSteps`. -/
theorem bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_present := by
  have h_perm_rows :
      (ziskTrace.memReplayRows h_present).Perm
        ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
    rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]
    exact h_perm
  exact
    bootSegmentReplaySafeOrderCertificate_of_perm_pairwise_noActiveWriteOverlap
      h_perm_rows h_safe

/-- Construct read-soundness inputs from structural row correspondence plus
pairwise-safe accepted replay rows. -/
def bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order :=
    bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
      h_placement h_perm h_safe

/-- Direct execution-order read-soundness from structural row correspondence
plus pairwise-safe accepted replay rows. -/
theorem readSound_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
      h_initialMemory h_placement h_perm h_safe)

/-- Seed-level wrapper for structural row correspondence plus pairwise-safe
accepted replay rows. -/
theorem BootSegmentMemorySeed.replaySafeOrderCertificate_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    BootSegmentReplaySafeOrderCertificate ziskTrace seed.rowsOf h_present :=
  bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    seed.placement h_perm h_safe

/-- Seed-level input assembly from structural row correspondence plus
pairwise-safe accepted replay rows. -/
def BootSegmentMemorySeed.readSoundInputs_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    BootSegmentReadSoundInputs ziskTrace seed.memInit seed.rowsOf h_present :=
  bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    (seed.readSoundInputs h_present).initialMemory_eq seed.placement h_perm h_safe

/-- Seed-level execution-order read-soundness from structural row
correspondence plus pairwise-safe accepted replay rows. -/
theorem BootSegmentMemorySeed.readSound_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_safe :
      ∀ left, left ∈ ziskTrace.memReplayRows h_present →
        ∀ right, right ∈ ziskTrace.memReplayRows h_present →
          MemoryBusEntryNoActiveWriteOverlap left right ∧
            MemoryBusEntryNoActiveWriteOverlap right left) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (seed.readSoundInputs_of_memoryRowsOfSteps_perm_pairwise_noActiveWriteOverlap
      h_perm h_safe)

/-- Structural row correspondence plus crossed-pair safety yields the concrete
boot replay-safe order certificate once placement identifies `rowsOf` with
`executionMemoryRowsOfSteps`.

The safety premise is sublist-aware because the constructive permutation proof
recursively removes selected target heads. It is still a crossed-pair premise:
only rows witnessed by `MemoryBusRowsPairBefore` in opposite source/target
orders must be safe. -/
theorem bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_cross :
      ∀ {currentSource currentTarget row moved},
        List.Sublist currentSource (ziskTrace.memReplayRows h_present) →
        List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
        MemoryBusRowsPairBefore moved row currentSource →
        MemoryBusRowsPairBefore row moved currentTarget →
        MemoryBusEntryNoActiveWriteOverlap row moved ∧
          MemoryBusEntryNoActiveWriteOverlap moved row) :
    BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_present := by
  have h_order_steps :
      MemoryBusRowsReplaySafePermutation
        (ziskTrace.memReplayRows h_present)
        (executionMemoryRowsOfSteps ziskTrace ziskStep) :=
    MemoryBusRowsReplaySafePermutation.of_perm_noUnsafeCrossings h_perm h_cross
  simpa [BootSegmentReplaySafeOrderCertificate, AcceptedZiskTrace.memReplayRows,
    AcceptedZiskTrace.memReplayBridge,
    executionRows_eq_memoryRowsOfSteps_of_placement h_placement] using h_order_steps

/-- Store-inclusive order certificate from an ordinary accepted-replay /
execution-row permutation. Crossed pairs are safe by accepted Mem source order
and structural execution target order, so callers no longer provide a separate
crossing callback. -/
theorem bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_sourceTargetChronology
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep)) :
    BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_present :=
  bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    h_placement h_perm
    (fun h_source_sublist h_target_sublist h_source_before h_target_before =>
      acceptedMemReplayRows_noActiveWriteOverlap_of_crossed_source_target
        h_source_sublist h_target_sublist h_source_before h_target_before)

/-- Construct read-soundness inputs from structural row correspondence plus
crossed-pair safe crossings. -/
def bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_cross :
      ∀ {currentSource currentTarget row moved},
        List.Sublist currentSource (ziskTrace.memReplayRows h_present) →
        List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
        MemoryBusRowsPairBefore moved row currentSource →
        MemoryBusRowsPairBefore row moved currentTarget →
        MemoryBusEntryNoActiveWriteOverlap row moved ∧
          MemoryBusEntryNoActiveWriteOverlap moved row) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order :=
    bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_noUnsafeCrossings
      h_placement h_perm h_cross

/-- Construct read-soundness inputs from a store-inclusive order certificate
derived from accepted Mem source order and structural execution target order. -/
def bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_sourceTargetChronology
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep)) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order :=
    bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_sourceTargetChronology
      h_placement h_perm

/-- Direct execution-order read-soundness from structural row correspondence
plus crossed-pair safe crossings. -/
theorem readSound_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_cross :
      ∀ {currentSource currentTarget row moved},
        List.Sublist currentSource (ziskTrace.memReplayRows h_present) →
        List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
        MemoryBusRowsPairBefore moved row currentSource →
        MemoryBusRowsPairBefore row moved currentTarget →
        MemoryBusEntryNoActiveWriteOverlap row moved ∧
          MemoryBusEntryNoActiveWriteOverlap moved row) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_noUnsafeCrossings
      h_initialMemory h_placement h_perm h_cross)

/-- Direct execution-order read-soundness from a store-inclusive order
certificate derived from source/target chronology. -/
theorem readSound_of_memoryRowsOfSteps_perm_sourceTargetChronology
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep)) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_sourceTargetChronology
      h_initialMemory h_placement h_perm)

/-- Seed-level wrapper for structural row correspondence plus crossed-pair
safe crossings. -/
theorem BootSegmentMemorySeed.replaySafeOrderCertificate_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_cross :
      ∀ {currentSource currentTarget row moved},
        List.Sublist currentSource (ziskTrace.memReplayRows h_present) →
        List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
        MemoryBusRowsPairBefore moved row currentSource →
        MemoryBusRowsPairBefore row moved currentTarget →
        MemoryBusEntryNoActiveWriteOverlap row moved ∧
          MemoryBusEntryNoActiveWriteOverlap moved row) :
    BootSegmentReplaySafeOrderCertificate ziskTrace seed.rowsOf h_present :=
  bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    seed.placement h_perm h_cross

/-- Seed-level store-inclusive order certificate from source/target chronology. -/
theorem BootSegmentMemorySeed.replaySafeOrderCertificate_of_memoryRowsOfSteps_perm_sourceTargetChronology
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep)) :
    BootSegmentReplaySafeOrderCertificate ziskTrace seed.rowsOf h_present :=
  bootSegmentReplaySafeOrderCertificate_of_memoryRowsOfSteps_perm_sourceTargetChronology
    seed.placement h_perm

/-- Seed-level input assembly from structural row correspondence plus
crossed-pair safe crossings. -/
def BootSegmentMemorySeed.readSoundInputs_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_cross :
      ∀ {currentSource currentTarget row moved},
        List.Sublist currentSource (ziskTrace.memReplayRows h_present) →
        List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
        MemoryBusRowsPairBefore moved row currentSource →
        MemoryBusRowsPairBefore row moved currentTarget →
        MemoryBusEntryNoActiveWriteOverlap row moved ∧
          MemoryBusEntryNoActiveWriteOverlap moved row) :
    BootSegmentReadSoundInputs ziskTrace seed.memInit seed.rowsOf h_present :=
  bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    (seed.readSoundInputs h_present).initialMemory_eq seed.placement h_perm h_cross

/-- Seed-level input assembly from source/target chronology. -/
def BootSegmentMemorySeed.readSoundInputs_of_memoryRowsOfSteps_perm_sourceTargetChronology
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep)) :
    BootSegmentReadSoundInputs ziskTrace seed.memInit seed.rowsOf h_present :=
  bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_sourceTargetChronology
    (seed.readSoundInputs h_present).initialMemory_eq seed.placement h_perm

/-- Seed-level execution-order read-soundness from structural row
correspondence plus crossed-pair safe crossings. -/
theorem BootSegmentMemorySeed.readSound_of_memoryRowsOfSteps_perm_noUnsafeCrossings
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_cross :
      ∀ {currentSource currentTarget row moved},
        List.Sublist currentSource (ziskTrace.memReplayRows h_present) →
        List.Sublist currentTarget (executionMemoryRowsOfSteps ziskTrace ziskStep) →
        MemoryBusRowsPairBefore moved row currentSource →
        MemoryBusRowsPairBefore row moved currentTarget →
        MemoryBusEntryNoActiveWriteOverlap row moved ∧
          MemoryBusEntryNoActiveWriteOverlap moved row) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (seed.readSoundInputs_of_memoryRowsOfSteps_perm_noUnsafeCrossings
      h_perm h_cross)

/-- Seed-level execution-order read-soundness from source/target chronology. -/
theorem BootSegmentMemorySeed.readSound_of_memoryRowsOfSteps_perm_sourceTargetChronology
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep)) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (seed.readSoundInputs_of_memoryRowsOfSteps_perm_sourceTargetChronology h_perm)

/-- Store-inclusive scoped direct-Mem input assembly from structural
deduplication plus length equality. Source/target chronology supplies all
crossing safety; no replay-neutrality premise is needed. -/
def bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present := by
  have h_perm_rows :=
    ziskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_nodup
      h_present h_placement h_scoped h_nodup h_length
  have h_perm_steps :
      (ziskTrace.memReplayRows h_present).Perm
        (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
    rwa [executionRows_eq_memoryRowsOfSteps_of_placement h_placement] at h_perm_rows
  exact bootSegmentReadSoundInputs_of_memoryRowsOfSteps_perm_sourceTargetChronology
    h_initialMemory h_placement h_perm_steps

/-- Store-inclusive scoped direct-Mem input assembly from formula-level
Main-step timestamp separation plus length equality. -/
def bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_nodup
    h_initialMemory h_placement h_scoped
    (executionRows_nodup_of_mainStep_timestamp_separated_placement
      h_placement h_timestamp)
    h_length

/-- Store-inclusive scoped direct-Mem input assembly from the consolidated
Main-step index certificate plus length equality. -/
def bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_mainStep_timestamp_separated
    h_initialMemory h_placement h_scoped
    memoryRowsOfStep_mainStep_timestamp_separated_of_main_step_index_fixed
    h_length

/-- Store-inclusive scoped direct-Mem input assembly from the named row-count
certificate. -/
def bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_rowCount
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_rowCount : ScopedDirectMemReplayLengthCertificate ziskTrace rowsOf h_present) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_main_step_index_fixed
    h_initialMemory h_placement h_scoped h_rowCount.length_eq

/-- Store-inclusive scoped direct-Mem read-soundness from structural
deduplication plus length equality. -/
theorem readSound_of_scopedDirect_sourceTargetChronology_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_nodup
      h_initialMemory h_placement h_scoped h_nodup h_length)

/-- Store-inclusive scoped direct-Mem read-soundness from formula-level
Main-step timestamp separation plus length equality. -/
theorem readSound_of_scopedDirect_sourceTargetChronology_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_mainStep_timestamp_separated
      h_initialMemory h_placement h_scoped h_timestamp h_length)

/-- Store-inclusive scoped direct-Mem read-soundness from the consolidated
Main-step index certificate plus length equality. -/
theorem readSound_of_scopedDirect_sourceTargetChronology_main_step_index_fixed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_main_step_index_fixed
      h_initialMemory h_placement h_scoped h_length)

/-- Store-inclusive scoped direct-Mem read-soundness from the named row-count
certificate. -/
theorem readSound_of_scopedDirect_sourceTargetChronology_rowCount
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_rowCount : ScopedDirectMemReplayLengthCertificate ziskTrace rowsOf h_present) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_scopedDirect_sourceTargetChronology_main_step_index_fixed
    h_initialMemory h_placement h_scoped h_rowCount.length_eq

/-- Seed-level store-inclusive scoped direct-Mem input assembly from the named
row-count certificate. -/
def BootSegmentMemorySeed.readSoundInputs_of_scopedDirect_sourceTargetChronology_rowCount
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      seed.memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_rowCount :
      ScopedDirectMemReplayLengthCertificate ziskTrace seed.rowsOf h_present) :
    BootSegmentReadSoundInputs ziskTrace seed.memInit seed.rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_sourceTargetChronology_rowCount
    h_initialMemory seed.placement h_scoped h_rowCount

/-- Seed-level store-inclusive scoped direct-Mem read-soundness from the named
row-count certificate. -/
theorem BootSegmentMemorySeed.readSound_of_scopedDirect_sourceTargetChronology_rowCount
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      seed.memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_rowCount :
      ScopedDirectMemReplayLengthCertificate ziskTrace seed.rowsOf h_present) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (seed.readSoundInputs_of_scopedDirect_sourceTargetChronology_rowCount
      h_initialMemory h_scoped h_rowCount)

/-- If every decoded step emits only replay-neutral memory rows, then the full
structural execution-row list contains no active memory writes. -/
theorem executionMemoryRowsOfSteps_not_active_write_of_replayNeutralSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep) :
    ¬(entry.as = (2 : FGL) ∧ entry.multiplicity = (1 : FGL)) := by
  obtain ⟨i, h_entry_i⟩ :=
    exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps h_entry
  exact memoryRowsOfStep_not_active_write_of_replayNeutralStep (h_steps i) h_entry_i

/-- Placement transports the replay-neutral row fact from structural decoded
steps to the concrete execution-order `rowsOf` flatMap. -/
theorem executionRows_not_active_write_of_replayNeutralSteps_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)) :
    ¬(entry.as = (2 : FGL) ∧ entry.multiplicity = (1 : FGL)) := by
  have h_structural :
      entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep := by
    rwa [executionRows_eq_memoryRowsOfSteps_of_placement h_placement] at h_entry
  exact executionMemoryRowsOfSteps_not_active_write_of_replayNeutralSteps
    h_steps h_structural

/-- Accepted Mem replay rows identify a structural decoded step under the
seed's replay-safe order certificate and placement. -/
theorem BootSegmentMemorySeed.exists_memoryRowsOfStep_of_memReplayRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_present) :
    ∃ i : Fin ziskTrace.numInstructions, entry ∈ memoryRowsOfStep ziskTrace i (ziskStep i) :=
  exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps
    (seed.mem_memoryRowsOfSteps_of_memReplayRows h_entry)

/-- A row emitted by one structural decoded step occurs in accepted Mem replay
rows under the seed's replay-safe order certificate and placement. -/
theorem BootSegmentMemorySeed.memReplayRows_of_memoryRowsOfStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_present : MutableMemPresent ziskTrace.witness}
    (i : Fin ziskTrace.numInstructions)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i (ziskStep i)) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  seed.memReplayRows_of_mem_memoryRowsOfSteps
    (mem_executionMemoryRowsOfSteps_of_memoryRowsOfStep i h_entry)

/-- A row in one step's `rowsOf` list is in the full execution-order memory
row list. -/
theorem mem_executionRows_of_rowsOf_mem
    {n : Nat} {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    (i : Fin n) {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ rowsOf i.val) :
    entry ∈ ((List.range n).flatMap rowsOf) :=
  List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, h_entry⟩

/-- Placement pins every structural row of this step into the full
execution-order memory row list. -/
theorem mem_executionRows_of_memoryRowsOfStep_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i)
    (h_placement : MemoryOpPlacement ziskTrace rowsOf memInit i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  apply mem_executionRows_of_rowsOf_mem (i := i)
  rwa [rowsOf_eq_memoryRowsOfStep_of_placement i step h_placement]

/-- Through the replay-safe order certificate, placement reflects each
structural execution row back to the accepted Mem replay row list. -/
theorem BootSegmentReadSoundInputs.memReplayRows_of_memoryRowsOfStep_placement
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_present : MutableMemPresent ziskTrace.witness}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present)
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i)
    (h_placement : MemoryOpPlacement ziskTrace rowsOf memInit i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_present :=
  inputs.memReplayRows_of_mem_executionRows
    (mem_executionRows_of_memoryRowsOfStep_placement i step h_placement h_entry)

/-- Build the boot replay-safe order certificate for replay-neutral structural
chunks from ordinary duplicate-sensitive row correspondence.

This is the seed-level specialization of
`MemoryBusRowsReplaySafePermutation.of_perm_not_active_write`: if the accepted
replay rows are a plain permutation of structural decoded rows, and every
decoded step emits only replay-neutral memory rows, then the order certificate
contains no semantic read-value premise. Mixed read/write chunks still require
the Mem ordering facts. -/
theorem bootSegmentReplaySafeOrderCertificate_of_perm_replayNeutralSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i)) :
    BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_present := by
  have h_perm_rows :
      (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
        (ziskTrace.memReplayBridge h_present)).rows.Perm
        ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
    have h_perm_target :
        (ziskTrace.memReplayRows h_present).Perm
          ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
      rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]
      exact h_perm
    simpa [AcceptedZiskTrace.memReplayBridge, AcceptedZiskTrace.memReplayRows] using h_perm_target
  refine MemoryBusRowsReplaySafePermutation.of_perm_not_active_write h_perm_rows ?_ ?_
  · intro row h_row
    have h_memReplay : row ∈ ziskTrace.memReplayRows h_present := by
      simpa [AcceptedZiskTrace.memReplayBridge, AcceptedZiskTrace.memReplayRows] using h_row
    exact executionMemoryRowsOfSteps_not_active_write_of_replayNeutralSteps h_steps
      ((h_perm.mem_iff).mp h_memReplay)
  · intro row h_row
    exact executionRows_not_active_write_of_replayNeutralSteps_placement
      h_placement h_steps h_row

/-- Construct the read-soundness input bundle for replay-neutral structural
chunks from ordinary row correspondence plus the explicit initial-memory
bridge. -/
def bootSegmentReadSoundInputs_of_perm_replayNeutralSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i)) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order :=
    bootSegmentReplaySafeOrderCertificate_of_perm_replayNeutralSteps
      h_placement h_perm h_steps

/-- Construct the read-soundness input bundle for replay-neutral scoped
direct-Mem rows from the count-sensitive row-correspondence boundary.

The remaining assumptions are concrete: initial-memory equality, structural
placement/classification, replay-neutrality, and the duplicate-sensitive
count/length facts needed to turn support inclusion into a permutation. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_count_le
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) →
        memoryBusEntryDecidableCount entry
            ((List.range ziskTrace.numInstructions).flatMap rowsOf) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order := by
    have h_perm_rows :=
      ziskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_count_le
        h_present h_placement h_scoped h_count_le h_length
    have h_perm_steps :
        (ziskTrace.memReplayRows h_present).Perm
          (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
      rwa [executionRows_eq_memoryRowsOfSteps_of_placement h_placement] at h_perm_rows
    exact bootSegmentReplaySafeOrderCertificate_of_perm_replayNeutralSteps
      h_placement h_perm_steps h_replayNeutral

/-- Construct the read-soundness input bundle for replay-neutral scoped
direct-Mem rows from structural deduplication plus length equality. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present where
  initialMemory_eq := h_initialMemory
  order := by
    have h_perm_rows :=
      ziskTrace.memReplayRows_perm_executionRows_of_scopedDirect_placement_nodup
        h_present h_placement h_scoped h_nodup h_length
    have h_perm_steps :
        (ziskTrace.memReplayRows h_present).Perm
          (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
      rwa [executionRows_eq_memoryRowsOfSteps_of_placement h_placement] at h_perm_rows
    exact bootSegmentReplaySafeOrderCertificate_of_perm_replayNeutralSteps
      h_placement h_perm_steps h_replayNeutral

/-- Construct the read-soundness input bundle for replay-neutral scoped
direct-Mem rows from per-step duplicate-freedom and pairwise-disjoint step row
lists. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_pairwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j))))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_nodup
    h_initialMemory h_placement h_scoped h_replayNeutral
    (executionRows_nodup_of_pairwise_disjoint_placement
      h_placement h_step_nodup h_pairwise)
    h_length

/-- Construct the read-soundness input bundle for replay-neutral scoped
direct-Mem rows from only pairwise-disjoint step row lists. The step-local
`Nodup` side is discharged by `memoryRowsOfStep_nodup`. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_pairwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j))))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_nodup
    h_initialMemory h_placement h_scoped h_replayNeutral
    (executionRows_nodup_of_pairwise_disjoint_memoryRows_placement
      h_placement h_pairwise)
    h_length

/-- Construct the read-soundness input bundle for replay-neutral scoped
direct-Mem rows from indexwise disjointness between unequal decoded steps. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_indexwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j)))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_pairwise_disjoint_memoryRows
    h_initialMemory h_placement h_scoped h_replayNeutral
    (pairwise_disjoint_memoryRowsOfStep_of_indexwise_disjoint h_disjoint)
    h_length

/-- Assembly wrapper for replay-neutral scoped direct-Mem rows, using
indexwise timestamp separation as the structural duplicate-freedom premise. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_indexwise_disjoint
    h_initialMemory h_placement h_scoped h_replayNeutral
    (indexwise_disjoint_memoryRowsOfStep_of_indexwise_timestamp_disjoint h_timestamp)
    h_length

/-- Assembly wrapper for replay-neutral scoped direct-Mem rows, using the four
concrete load/store timestamp inequalities as the structural duplicate-freedom
premise. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_structural_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_indexwise_timestamp_disjoint
    h_initialMemory h_placement h_scoped h_replayNeutral
    (memoryRowsOfStep_indexwise_timestamp_disjoint_of_structural_timestamp_disjoint
      h_timestamp)
    h_length

/-- Assembly wrapper for replay-neutral scoped direct-Mem rows, using
formula-level Main-step timestamp separation as the structural
duplicate-freedom premise. -/
def bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_present :=
  bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_structural_timestamp_disjoint
    h_initialMemory h_placement h_scoped h_replayNeutral
    (memoryRowsOfStep_structural_timestamp_disjoint_of_mainStep_timestamp_separated
      h_timestamp)
    h_length

/-- Direct read-soundness theorem for the scoped replay-neutral case. The
remaining assumptions are the explicit boot/cross-segment initial-memory bridge
and duplicate-sensitive row correspondence; read-value agreement is still
provided only by accepted Mem replay evidence. -/
theorem readSound_of_perm_replayNeutralSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_present).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i)) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_perm_replayNeutralSteps
      h_initialMemory h_placement h_perm h_steps)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using the count-sensitive row-correspondence boundary. -/
theorem readSound_of_scopedDirect_replayNeutral_count_le
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_count_le :
      ∀ entry,
        entry ∈ ziskTrace.memReplayRows h_present →
        entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) →
        memoryBusEntryDecidableCount entry
            ((List.range ziskTrace.numInstructions).flatMap rowsOf) ≤
          memoryBusEntryDecidableCount entry (ziskTrace.memReplayRows h_present))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_count_le
      h_initialMemory h_placement h_scoped h_replayNeutral h_count_le h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using structural deduplication plus length equality. -/
theorem readSound_of_scopedDirect_replayNeutral_nodup
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_nodup : ((List.range ziskTrace.numInstructions).flatMap rowsOf).Nodup)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_nodup
      h_initialMemory h_placement h_scoped h_replayNeutral h_nodup h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using per-step duplicate-freedom plus pairwise-disjoint step row lists. -/
theorem readSound_of_scopedDirect_replayNeutral_pairwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_step_nodup : ∀ i : Fin ziskTrace.numInstructions,
      (memoryRowsOfStep ziskTrace i (ziskStep i)).Nodup)
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j))))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_pairwise_disjoint
      h_initialMemory h_placement h_scoped h_replayNeutral h_step_nodup h_pairwise h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using only pairwise-disjoint structural step row lists. -/
theorem readSound_of_scopedDirect_replayNeutral_pairwise_disjoint_memoryRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_pairwise :
      (List.finRange ziskTrace.numInstructions).Pairwise
        (fun i j =>
          List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
            (memoryRowsOfStep ziskTrace j (ziskStep j))))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_pairwise_disjoint_memoryRows
      h_initialMemory h_placement h_scoped h_replayNeutral h_pairwise h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using indexwise disjointness between unequal decoded steps. -/
theorem readSound_of_scopedDirect_replayNeutral_indexwise_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_disjoint : ∀ i j : Fin ziskTrace.numInstructions, i ≠ j →
      List.Disjoint (memoryRowsOfStep ziskTrace i (ziskStep i))
        (memoryRowsOfStep ziskTrace j (ziskStep j)))
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_indexwise_disjoint
      h_initialMemory h_placement h_scoped h_replayNeutral h_disjoint h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using indexwise timestamp separation between unequal decoded steps. -/
theorem readSound_of_scopedDirect_replayNeutral_indexwise_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseTimestampDisjoint ziskTrace ziskStep)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_indexwise_timestamp_disjoint
      h_initialMemory h_placement h_scoped h_replayNeutral h_timestamp h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using the four concrete load/store timestamp inequalities. -/
theorem readSound_of_scopedDirect_replayNeutral_structural_timestamp_disjoint
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseStructuralTimestampDisjoint ziskTrace)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_structural_timestamp_disjoint
      h_initialMemory h_placement h_scoped h_replayNeutral h_timestamp h_length)

/-- Direct read-soundness theorem for replay-neutral scoped direct-Mem rows
using formula-level Main-step timestamp separation. -/
theorem readSound_of_scopedDirect_replayNeutral_mainStep_timestamp_separated
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_present : MutableMemPresent ziskTrace.witness}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_present)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_scoped : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    (h_replayNeutral : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i))
    (h_timestamp : MemoryRowsOfStepIndexwiseMainStepTimestampSeparated ziskTrace)
    (h_length :
      (ziskTrace.memReplayRows h_present).length =
        ((List.range ziskTrace.numInstructions).flatMap rowsOf).length) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_scopedDirect_replayNeutral_mainStep_timestamp_separated
      h_initialMemory h_placement h_scoped h_replayNeutral h_timestamp h_length)

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
  have h_executionRows_nonempty :
      ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) ≠ [] := by
    intro h_empty
    rw [h_empty] at h_split
    simp at h_split
  have h_present : MutableMemPresent ziskTrace.witness :=
    seed.memPresent_of_executionRows_nonempty h_executionRows_nonempty
  exact loadEvidence_of_loadMemReplay
    (initialState := binding ⟨0, hpos⟩)
    { initialMemory := seed.memInit
      prefixReadSound := readSound_of_bootSeed seed h_present
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
  have h_executionRows_nonempty :
      ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) ≠ [] := by
    intro h_empty
    rw [h_empty] at h_split
    simp at h_split
  have h_present : MutableMemPresent ziskTrace.witness :=
    seed.memPresent_of_executionRows_nonempty h_executionRows_nonempty
  exact storeEvidence_of_loadMemReplay
    (initialState := binding ⟨0, hpos⟩)
    { initialMemory := seed.memInit
      prefixReadSound := readSound_of_bootSeed seed h_present
      initialAgreement := fun _ => by rw [seed.boot hpos] }
    h_split
    (exec_order_fold_fin binding seed.memInit seed.rowsOf hpos (seed.boot hpos) seed.step i)
    h_bytes

/-- Derive each memory op's residual (`MemoryOpEvidenceFor`) from the one shared seed, via the
    execution-order fold. Non-memory ops and `sd` still have trivial residuals, but their placement
    facts now constrain `rowsOf` for row-correspondence. -/
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
