import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence
import ZiskFv.Compliance.AcceptedZiskTrace.MemProviders
import ZiskFv.Compliance.SharedBundles
import ZiskFv.Compliance.TraceLevelExport.Dispatcher
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding

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

/-- Explicit structural certificate for the remaining sorted-to-execution order
residue in the current #115 surface.

This states that the execution-order memory rows are obtainable from the
accepted Mem replay rows by replay-safe adjacent swaps. It is not a read-value
agreement predicate: final #115 work must either derive this certificate from
row correspondence plus Mem ordering facts, or land it only after explicit
scope approval as a PIL/checkable order certificate. -/
abbrev BootSegmentReplaySafeOrderCertificate
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_nonempty : 0 < ziskTrace.numInstructions) : Prop :=
  MemoryBusRowsReplaySafePermutation
    (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (ziskTrace.memReplayBridge h_nonempty)).rows
    ((List.range ziskTrace.numInstructions).flatMap rowsOf)

/-- Nonsemantic inputs needed to derive execution-order seed read-soundness
from accepted Mem replay evidence.

The accepted trace supplies the guarded Mem replay bridge. `initialMemory_eq` is
the explicit boot/cross-segment memory bridge. `order` is the named structural
order-transfer certificate `BootSegmentReplaySafeOrderCertificate`. -/
structure BootSegmentReadSoundInputs
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (memInit : Std.ExtHashMap Nat (BitVec 8))
    (rowsOf : ℕ → List (MemoryBusEntry FGL))
    (h_nonempty : 0 < ziskTrace.numInstructions) : Type 2 where
  initialMemory_eq :
    memInit =
      (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
        (ziskTrace.memReplayBridge h_nonempty)).initialMemory
  order : BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_nonempty

/-- Assemble the exact seed-level execution-order read-soundness predicate from
accepted Mem replay evidence plus the explicit initial-memory and order-transfer
bridges. -/
theorem readSound_of_bootSegmentReadSoundInputs
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  let acceptedReplay :=
    ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (ziskTrace.memReplayBridge h_nonempty)
  have h_prefix :
      MemoryBusRowsPrefixReadSound
        acceptedReplay.initialMemory
        ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
    memoryBusRowsPrefixReadSound_of_replaySafePermutation
      acceptedReplay.initialMemory inputs.order acceptedReplay.prefixReadSound
  rwa [inputs.initialMemory_eq]

/-- Rows in the accepted Mem replay source occur in the execution-order row list
selected by the seed's replay-safe order certificate. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_memReplayRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_nonempty) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
  have h_source :
      entry ∈
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
      (ziskTrace.memReplayBridge h_nonempty)).rows := by
    simpa [AcceptedZiskTrace.memReplayBridge, AcceptedZiskTrace.memReplayRows] using h_entry
  exact inputs.order.mem_target_of_mem_source h_source

/-- The replay-safe order certificate exposes the bag/permutation equality
between accepted Mem replay rows and execution-order rows. -/
theorem BootSegmentReadSoundInputs.memReplayRows_perm_executionRows
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty) :
    (ziskTrace.memReplayRows h_nonempty).Perm
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty) :
    (ziskTrace.memReplayRows h_nonempty).length =
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
    (entry : MemoryBusEntry FGL) :
    (ziskTrace.memReplayRows h_nonempty).count entry =
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)) :
    entry ∈ ziskTrace.memReplayRows h_nonempty :=
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty h_mainRow h_mainInteraction h_mainEval h_active h_main_mem_op
      h_no_nonmutable h_entry)

/-- Store analogue of
`BootSegmentReadSoundInputs.mem_executionRows_of_activeMainMutableMemProviderEntry`.

The Clean Main interaction is an active pull (`mult = -1`), while the legacy
execution row is a write row (`multiplicity = 1`, `as = 2`). -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_activeMainMutableStoreMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty h_mainRow h_mainInteraction h_mainEval h_active h_main_mem_op
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
      numInstructions ziskTrace.program).rowInputVar

@[reducible] def storeCMemMainMessage
    (ziskTrace : AcceptedZiskTrace numInstructions) :
    ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL) :=
  ZiskFv.AirsClean.Main.cMemMessageExpr
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
      numInstructions ziskTrace.program).rowInputVar

@[reducible] def loadBMemMainMultiplicity
    (ziskTrace : AcceptedZiskTrace numInstructions) : Expression FGL :=
  -((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        numInstructions ziskTrace.program).rowInputVar.rom.b_src_mem
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        numInstructions ziskTrace.program).rowInputVar.rom.b_src_ind
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        numInstructions ziskTrace.program).rowInputVar.rom.b_src_reg)

@[reducible] def storeCMemMainMultiplicity
    (ziskTrace : AcceptedZiskTrace numInstructions) : Expression FGL :=
  -((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        numInstructions ziskTrace.program).rowInputVar.rom.store_mem
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        numInstructions ziskTrace.program).rowInputVar.rom.store_ind
    + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        numInstructions ziskTrace.program).rowInputVar.rom.store_reg)

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
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
      ziskTrace.memReplayRows h_nonempty := by
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
            numInstructions ziskTrace.program).rowInputVar =
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
          numInstructions ziskTrace.program).rowInputVar
    have h_source_sum' :
        Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_reg) =
          (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.b_src_mem
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.b_src_ind
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.b_src_reg := by
      simpa using h_source_sum
    rw [loadBMemMainMultiplicity]
    change
      (-1 : FGL) *
          Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_reg) = -1
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
    h_nonempty h_mainRow h_mainInteraction h_mainEval h_active_interaction h_main_mem_op
    h_no_nonmutable h_entry

/-- Store-`c` analogue of `AcceptedZiskTrace.memReplayRows_of_loadBMemProviderEntry`.

Accepted trace data proves the concrete store write row occurs in accepted Mem
replay rows before the seed-specific order certificate is used. The remaining
residue is the syntactic exclusion of non-mutable provider branches for the
store-shaped Main message. -/
theorem AcceptedZiskTrace.memReplayRows_of_storeCMemProviderEntry
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
      ziskTrace.memReplayRows h_nonempty := by
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
            numInstructions ziskTrace.program).rowInputVar =
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
          numInstructions ziskTrace.program).rowInputVar
    have h_source_sum' :
        Expression.eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.store_reg) =
          (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.store_mem
            + (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.store_ind
            + (eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.store_reg := by
      simpa using h_source_sum
    rw [storeCMemMainMultiplicity]
    change
      (-1 : FGL) *
          Expression.eval (ziskTrace.mainTable.environment (storeCMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.store_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.store_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.store_reg) = -1
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
    h_nonempty h_mainRow h_mainInteraction h_mainEval h_active_interaction h_main_mem_op
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
    (ziskTrace.memReplayRows_of_loadBMemProviderEntry h_nonempty i h_b_src_ind h_active
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
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
      ziskTrace.memReplayRows h_nonempty := by
  have h_row_eval :
      eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            numInstructions ziskTrace.program).rowInputVar =
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
  exact ziskTrace.memReplayRows_of_loadBMemProviderEntry h_nonempty i h_b_src_ind h_active
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign)

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
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
      ∧ (entry ∈ ziskTrace.memReplayRows h_nonempty
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
            numInstructions ziskTrace.program).rowInputVar =
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
          numInstructions ziskTrace.program).rowInputVar
    have h_source_sum' :
        Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_reg) =
          (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.b_src_mem
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.b_src_ind
            + (eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar).rom.b_src_reg := by
      simpa using h_source_sum
    rw [loadBMemMainMultiplicity]
    change
      (-1 : FGL) *
          Expression.eval (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i))
            ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_ind
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                numInstructions ziskTrace.program).rowInputVar.rom.b_src_reg) = -1
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
        (ziskTrace.memReplayBridge h_nonempty)
        (ziskTrace.memReplayBridge_coversMutableMemTables h_nonempty))
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty i h_b_src_ind h_active h_selectedMemAlignPins
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
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
      ∧ (entry ∈ ziskTrace.memReplayRows h_nonempty
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
      h_nonempty i h_b_src_ind h_active h_selectedMemAlignPins
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty i main mab marb ma r_main h_width h_b_src_ind h_active
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
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
        LoadBMemAlignRomValueFacts ziskTrace main r_main entry) :
    ∃ entry : MemoryBusEntry FGL,
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (busLd ziskTrace i (Pilot.execRowOf ziskTrace i)).e1 entry
      ∧ (entry ∈ ziskTrace.memReplayRows h_nonempty
        ∨ ∃ mab' : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL,
          ∃ marb' : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL,
          ∃ ma' : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL,
            ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
              main mab' marb' ma' r_main entry) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_subdoublewordProvider_or_memAlignProvider_of_loadBMemProviderEntry
      h_nonempty i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins
  refine ⟨entry, h_entry, ?_⟩
  rcases h_provider with h_mem | h_marb | h_mab | h_memAlign
  · exact Or.inl h_mem
  · rcases h_marb with ⟨marb', h_provider⟩
    exact Or.inr ⟨mab, marb', ma, h_provider⟩
  · rcases h_mab with ⟨mab', h_provider⟩
    exact Or.inr ⟨mab', marb, ma, h_provider⟩
  · rcases
      exists_subdoublewordLoadProviderWitness_of_memAlignLoadProviderRowMatchSpec
        (main := main) (mab := mab) (marb := marb) (r_main := r_main)
        (h_generalMemAlignRomValues entry h_entry) h_memAlign with
      ⟨ma', h_provider⟩
    exact Or.inr ⟨mab, marb, ma', h_provider⟩

/-- Load `b` provider coverage with every MemAlign-family branch converted to
the legacy subdoubleword provider-witness shape.

The mutable-Mem branch still proves execution-row membership. All MemAlign
branches now return a `SubdoublewordLoadProviderWitness`; the general branch
does so only after the caller supplies the explicit ROM/value residue for the
selected structural provider row. -/
theorem BootSegmentReadSoundInputs.mem_or_subdoublewordProvider_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
        LoadBMemAlignRomValueFacts ziskTrace main r_main entry) :
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
      h_nonempty i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins h_generalMemAlignRomValues
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
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
      ∧ (entry ∈ ziskTrace.memReplayRows h_nonempty
        ∨ Nonempty (ZiskFv.Compliance.MemAlignWitness main r_main entry)) := by
  obtain ⟨entry, h_entry, h_provider⟩ :=
    ziskTrace.memReplayRows_or_subdoublewordProvider_of_loadBMemProviderEntry
      h_nonempty i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins h_generalMemAlignRomValues
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
branch returns the legacy `MemAlignWitness` bundle once the explicit
general-MemAlign ROM/value residue and the MemAlignByte/MemAlignReadByte
core/lookup residue are supplied. -/
theorem BootSegmentReadSoundInputs.mem_or_memAlignWitness_of_loadBMemProviderEntry
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty i main mab marb ma r_main h_width h_b_src_ind h_active
      h_selectedMemAlignPins h_generalMemAlignRomValues h_coreLookup
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

/-- Scoped structural row correspondence for direct mutable-Mem load rows.

For a decoded load step, any row in `memoryRowsOfStep` is the concrete `busLd.e1`
row. Accepted provider coverage plus the remaining syntactic MemAlign-family
exclusion residue place that row in the accepted Mem replay rows before any
seed-specific order transport is used. -/
theorem AcceptedZiskTrace.memReplayRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
    entry ∈ ziskTrace.memReplayRows h_nonempty := by
  cases step <;> simp [ZiskStepLoadMemoryRows, memoryRowsOfStep] at h_load h_entry
  all_goals
    subst entry
    exact ziskTrace.memReplayRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
      h_nonempty i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign

/-- Duplicate-sensitive singleton form of the scoped direct-Mem load
correspondence.

Each structural load step emits exactly one memory row, so membership in the
accepted replay rows is equivalently a subpermutation of that singleton row
list. This is the per-step bag-correspondence shape needed by later list
assembly. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_load_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_nonempty) := by
  cases step <;> simp [ZiskStepLoadMemoryRows, memoryRowsOfStep] at h_load ⊢
  all_goals
    exact ziskTrace.memReplayRows_of_loadBMemProviderEntry_of_no_nonmutableBranches
      h_nonempty i h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign

/-- Scoped structural row correspondence for direct mutable-Mem store rows.

For a decoded store step, any row in `memoryRowsOfStep` is the concrete
`busSt.e2` write row. Accepted provider coverage places that row in accepted
Mem replay rows before any seed-specific order transport is used. -/
theorem AcceptedZiskTrace.memReplayRows_of_storeMemoryRowsOfStep_of_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
    entry ∈ ziskTrace.memReplayRows h_nonempty := by
  cases step <;> simp [ZiskStepStoreMemoryRows, memoryRowsOfStep] at h_store h_entry
  all_goals
    subst entry
    exact ziskTrace.memReplayRows_of_storeCMemProviderEntry
      h_nonempty i h_store_ind h_active h_no_nonmutable

/-- Duplicate-sensitive singleton form of the scoped direct-Mem store
correspondence. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_store_no_nonmutableBranches
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
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
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_nonempty) := by
  cases step <;> simp [ZiskStepStoreMemoryRows, memoryRowsOfStep] at h_store ⊢
  all_goals
    exact ziskTrace.memReplayRows_of_storeCMemProviderEntry
      h_nonempty i h_store_ind h_active h_no_nonmutable

/-- Seed-order transport wrapper for the scoped structural load correspondence.

The accepted trace proves the structural load row occurs in accepted Mem replay
rows; the seed's replay-safe order certificate transports it to the full
execution-order row list. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty i h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign h_entry)

/-- Duplicate-sensitive singleton form after seed order transport. -/
theorem BootSegmentReadSoundInputs.memoryRowsOfStep_subperm_executionRows_of_load_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
      h_nonempty i h_store h_store_ind h_active h_no_nonmutable h_entry)

/-- Duplicate-sensitive singleton form after seed order transport. -/
theorem BootSegmentReadSoundInputs.memoryRowsOfStep_subperm_executionRows_of_store_no_nonmutableBranches
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
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
        h_nonempty i h_store_ind h_active h_no_nonmutable)
    simpa using List.mem_flatMap.mp h_mem

/-- Scoped structural row correspondence for any direct mutable-Mem step. This
packages the direct load and direct store cases without using the seed order
certificate. -/
theorem AcceptedZiskTrace.memReplayRows_of_directMutableMemRowsOfStep
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_nonempty := by
  cases h_direct with
  | load h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign =>
      exact ziskTrace.memReplayRows_of_loadMemoryRowsOfStep_of_no_nonmutableBranches
        h_nonempty i h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign h_entry
  | store h_store h_store_ind h_active h_no_nonmutable =>
      exact ziskTrace.memReplayRows_of_storeMemoryRowsOfStep_of_no_nonmutableBranches
        h_nonempty i h_store h_store_ind h_active h_no_nonmutable h_entry

/-- Duplicate-sensitive singleton form for any direct mutable-Mem step. This is
still step-local; whole-list duplicate accounting needs the later order/count
assembly. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_directMutableMemRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_nonempty) := by
  cases h_direct with
  | load h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign =>
      exact ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_load_no_nonmutableBranches
        h_nonempty i h_load h_b_src_ind h_active h_no_marb h_no_mab h_no_memAlign
  | store h_store h_store_ind h_active h_no_nonmutable =>
      exact ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_store_no_nonmutableBranches
        h_nonempty i h_store h_store_ind h_active h_no_nonmutable

/-- Step-local scoped direct-Mem row correspondence, including no-memory
instructions. -/
theorem AcceptedZiskTrace.memReplayRows_of_scopedDirectMemRowsOfStep
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepScopedDirectMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_nonempty := by
  cases h_step with
  | direct h_direct =>
      exact ziskTrace.memReplayRows_of_directMutableMemRowsOfStep
        h_nonempty i h_direct h_entry
  | noMemory h_empty =>
      simp [h_empty] at h_entry

/-- Step-local subpermutation form for the scoped direct-Mem correspondence,
including no-memory instructions. -/
theorem AcceptedZiskTrace.memoryRowsOfStep_subperm_memReplayRows_of_scopedDirectMemRows
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepScopedDirectMemRows ziskTrace i step) :
    (memoryRowsOfStep ziskTrace i step).Subperm (ziskTrace.memReplayRows h_nonempty) := by
  cases h_step with
  | direct h_direct =>
      exact ziskTrace.memoryRowsOfStep_subperm_memReplayRows_of_directMutableMemRows
        h_nonempty i h_direct
  | noMemory h_empty =>
      simp [h_empty]

/-- Seed-order transport wrapper for the scoped direct mutable-Mem
correspondence. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_directMutableMemRowsOfStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_direct : ZiskStepDirectMutableMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_directMutableMemRowsOfStep
      h_nonempty i h_direct h_entry)

/-- Seed-order transport wrapper for scoped direct/no-memory decoded steps. -/
theorem BootSegmentReadSoundInputs.mem_executionRows_of_scopedDirectMemRowsOfStep
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
    (i : Fin ziskTrace.numInstructions)
    {step : ZiskStep ziskTrace i}
    (h_step : ZiskStepScopedDirectMemRows ziskTrace i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  inputs.mem_executionRows_of_memReplayRows
    (ziskTrace.memReplayRows_of_scopedDirectMemRowsOfStep
      h_nonempty i h_step h_entry)

/-- The full execution-order memory-bus row list obtained directly from the
structural per-step decoder view. -/
noncomputable def executionMemoryRowsOfSteps
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i) :
    List (MemoryBusEntry FGL) :=
  (List.finRange ziskTrace.numInstructions).flatMap
    (fun i => memoryRowsOfStep ziskTrace i (ziskStep i))

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
  /-- Narrow replay/order inputs from which nonempty-segment read-soundness is derived. The guard
      keeps the empty-segment inhabitation witness from fabricating a nonempty Mem replay bridge. -/
  readSoundInputs :
    ∀ (h : 0 < ziskTrace.numInstructions), BootSegmentReadSoundInputs ziskTrace memInit rowsOf h
  /-- Structural placement pinning `rowsOf` to each op's real bus rows (+ narrow-store bytes). -/
  placement : ∀ i : Fin ziskTrace.numInstructions,
    MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i)

/-- Derived memory-bus read-soundness for a nonempty concrete seed. -/
theorem readSound_of_bootSeed
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_nonempty : 0 < ziskTrace.numInstructions) :
    MemoryBusRowsPrefixReadSound
      seed.memInit ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs (seed.readSoundInputs h_nonempty)

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
    (h_nonempty : 0 < ziskTrace.numInstructions) :
    (ziskTrace.memReplayRows h_nonempty).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep) := by
  have h_perm := (seed.readSoundInputs h_nonempty).memReplayRows_perm_executionRows
  rw [BootSegmentMemorySeed.executionRows_eq_memoryRowsOfSteps seed] at h_perm
  exact h_perm

/-- Length consequence for accepted Mem replay rows versus structural per-step
decoder rows. -/
theorem BootSegmentMemorySeed.memReplayRows_length_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_nonempty : 0 < ziskTrace.numInstructions) :
    (ziskTrace.memReplayRows h_nonempty).length =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).length := by
  have h_len := (seed.readSoundInputs h_nonempty).memReplayRows_length_eq_executionRows
  rw [BootSegmentMemorySeed.executionRows_eq_memoryRowsOfSteps seed] at h_len
  exact h_len

/-- Multiplicity consequence for accepted Mem replay rows versus structural
per-step decoder rows. -/
theorem BootSegmentMemorySeed.memReplayRows_count_eq_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    (entry : MemoryBusEntry FGL) :
    (ziskTrace.memReplayRows h_nonempty).count entry =
      (executionMemoryRowsOfSteps ziskTrace ziskStep).count entry := by
  have h_count := (seed.readSoundInputs h_nonempty).memReplayRows_count_eq_executionRows entry
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_nonempty) :
    entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep :=
  (seed.memReplayRows_perm_memoryRowsOfSteps h_nonempty).mem_iff.mp h_entry

/-- Structural per-step decoder rows occur in accepted Mem replay rows when
transported back through the seed's replay-safe order certificate and
placement. -/
theorem BootSegmentMemorySeed.memReplayRows_of_mem_memoryRowsOfSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    {h_nonempty : 0 < ziskTrace.numInstructions}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep) :
    entry ∈ ziskTrace.memReplayRows h_nonempty :=
  (seed.memReplayRows_perm_memoryRowsOfSteps h_nonempty).mem_iff.mpr h_entry

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

/-- Whole-structural-list membership direction for the scoped direct-Mem
correspondence.

Every row emitted by a decoded step classified as direct mutable-Mem or
no-memory occurs in accepted Mem replay rows. This is intentionally a
membership direction, not a full-list `Subperm`: duplicate-sensitive assembly
still needs the order/count work. -/
theorem AcceptedZiskTrace.memReplayRows_of_mem_executionMemoryRowsOfSteps_scopedDirect
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep) :
    entry ∈ ziskTrace.memReplayRows h_nonempty := by
  obtain ⟨i, h_entry_i⟩ :=
    exists_memoryRowsOfStep_of_mem_executionMemoryRowsOfSteps h_entry
  exact ziskTrace.memReplayRows_of_scopedDirectMemRowsOfStep
    h_nonempty i (h_steps i) h_entry_i

/-- Placement transports the scoped direct-Mem membership direction from the
concrete execution-order `rowsOf` flatMap to accepted Mem replay rows. -/
theorem AcceptedZiskTrace.memReplayRows_of_mem_executionRows_scopedDirect_placement
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap rowsOf)) :
    entry ∈ ziskTrace.memReplayRows h_nonempty := by
  have h_structural :
      entry ∈ executionMemoryRowsOfSteps ziskTrace ziskStep := by
    rwa [executionRows_eq_memoryRowsOfSteps_of_placement h_placement] at h_entry
  exact ziskTrace.memReplayRows_of_mem_executionMemoryRowsOfSteps_scopedDirect
    h_nonempty h_steps h_structural

/-- Seed-level wrapper for the scoped direct-Mem membership direction. -/
theorem BootSegmentMemorySeed.memReplayRows_of_mem_executionRows_scopedDirect
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {binding : SailTrace ziskTrace.numInstructions}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    (seed : BootSegmentMemorySeed ziskTrace binding ziskStep)
    (h_nonempty : 0 < ziskTrace.numInstructions)
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepScopedDirectMemRows ziskTrace i (ziskStep i))
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ((List.range ziskTrace.numInstructions).flatMap seed.rowsOf)) :
    entry ∈ ziskTrace.memReplayRows h_nonempty :=
  ziskTrace.memReplayRows_of_mem_executionRows_scopedDirect_placement
    h_nonempty seed.placement h_steps h_entry

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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ ziskTrace.memReplayRows h_nonempty) :
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (i : Fin ziskTrace.numInstructions)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i (ziskStep i)) :
    entry ∈ ziskTrace.memReplayRows h_nonempty :=
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (inputs : BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty)
    (i : Fin ziskTrace.numInstructions)
    (step : ZiskStep ziskTrace i)
    (h_placement : MemoryOpPlacement ziskTrace rowsOf memInit i step)
    {entry : MemoryBusEntry FGL}
    (h_entry : entry ∈ memoryRowsOfStep ziskTrace i step) :
    entry ∈ ziskTrace.memReplayRows h_nonempty :=
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_nonempty).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i)) :
    BootSegmentReplaySafeOrderCertificate ziskTrace rowsOf h_nonempty := by
  have h_perm_rows :
      (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
        (ziskTrace.memReplayBridge h_nonempty)).rows.Perm
        ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
    have h_perm_target :
        (ziskTrace.memReplayRows h_nonempty).Perm
          ((List.range ziskTrace.numInstructions).flatMap rowsOf) := by
      rw [executionRows_eq_memoryRowsOfSteps_of_placement h_placement]
      exact h_perm
    simpa [AcceptedZiskTrace.memReplayBridge, AcceptedZiskTrace.memReplayRows] using h_perm_target
  refine MemoryBusRowsReplaySafePermutation.of_perm_not_active_write h_perm_rows ?_ ?_
  · intro row h_row
    have h_memReplay : row ∈ ziskTrace.memReplayRows h_nonempty := by
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
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_nonempty)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_nonempty).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i)) :
    BootSegmentReadSoundInputs ziskTrace memInit rowsOf h_nonempty where
  initialMemory_eq := h_initialMemory
  order :=
    bootSegmentReplaySafeOrderCertificate_of_perm_replayNeutralSteps
      h_placement h_perm h_steps

/-- Direct read-soundness theorem for the scoped replay-neutral case. The
remaining assumptions are the explicit boot/cross-segment initial-memory bridge
and duplicate-sensitive row correspondence; read-value agreement is still
provided only by accepted Mem replay evidence. -/
theorem readSound_of_perm_replayNeutralSteps
    {ziskTrace : AcceptedZiskTrace numInstructions}
    {memInit : Std.ExtHashMap Nat (BitVec 8)}
    {rowsOf : ℕ → List (MemoryBusEntry FGL)}
    {ziskStep : ∀ i : Fin ziskTrace.numInstructions, ZiskStep ziskTrace i}
    {h_nonempty : 0 < ziskTrace.numInstructions}
    (h_initialMemory :
      memInit =
        (ZiskFv.AirsClean.FullEnsemble.acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_nonempty)).initialMemory)
    (h_placement : ∀ i : Fin ziskTrace.numInstructions,
      MemoryOpPlacement ziskTrace rowsOf memInit i (ziskStep i))
    (h_perm : (ziskTrace.memReplayRows h_nonempty).Perm
      (executionMemoryRowsOfSteps ziskTrace ziskStep))
    (h_steps : ∀ i : Fin ziskTrace.numInstructions,
      ZiskStepReplayNeutralMemoryRows ziskTrace i (ziskStep i)) :
    MemoryBusRowsPrefixReadSound
      memInit ((List.range ziskTrace.numInstructions).flatMap rowsOf) :=
  readSound_of_bootSegmentReadSoundInputs
    (bootSegmentReadSoundInputs_of_perm_replayNeutralSteps
      h_initialMemory h_placement h_perm h_steps)

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
      prefixReadSound := readSound_of_bootSeed seed hpos
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
      prefixReadSound := readSound_of_bootSeed seed hpos
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
