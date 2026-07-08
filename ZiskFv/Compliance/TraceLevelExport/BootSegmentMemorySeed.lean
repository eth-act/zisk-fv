import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence
import ZiskFv.Compliance.AcceptedZiskTrace.MemProviders
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

@[reducible] noncomputable def loadBMemMainRow
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Array FGL :=
  ziskTrace.mainTable.table.get ⟨i.val, ziskTrace.mainTable_index i⟩

@[reducible] def loadBMemMainMessage
    (ziskTrace : AcceptedZiskTrace numInstructions) :
    ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL) :=
  ZiskFv.AirsClean.Main.bMemMessageExpr
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

@[reducible] noncomputable def loadBMemMainInteraction
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Interaction FGL :=
  (((MemBusChannel.emitted (loadBMemMainMultiplicity ziskTrace)
    (loadBMemMainMessage ziskTrace)).toRaw).eval
    (ziskTrace.mainTable.environment (loadBMemMainRow ziskTrace i)))

/-- Load-`b` specialization of the selected general-MemAlign prove-branch
pins. This names the remaining syntactic residue needed to follow a general
MemAlign provider row; byte-provider branches are handled separately. -/
abbrev LoadBSelectedMemAlignPins
    (ziskTrace : AcceptedZiskTrace numInstructions)
    (i : Fin ziskTrace.numInstructions) : Prop :=
  ActiveMainMemAlignSelectedProveBranchPins ziskTrace.witness
    (loadBMemMainInteraction ziskTrace i)

/-- Load-specific wrapper for the accepted mutable-Mem provider path.

The generic theorem still needs an active Main interaction, its evaluated
message equality, and the load `mem_op = 1` fact. For the concrete load b-side
memory row, the interaction membership, evaluated message equality, `mem_op = 1`,
and entry match are derived from accepted Main table structure and the
load-decoder/active-pull facts. The remaining residues are still explicit:
non-mutable provider exclusion. -/
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
  exact inputs.mem_executionRows_of_activeMainMutableMemProviderEntry
    h_mainRow h_mainInteraction h_mainEval h_active_interaction h_main_mem_op
    h_no_nonmutable h_entry

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
  exact inputs.mem_executionRows_of_loadBMemProviderEntry i h_b_src_ind h_active
    (activeMainNonMutableMemProviderRowMatchSpec_of_no_branch
      h_no_marb h_no_mab h_no_memAlign h_no_main h_no_regBoundary)

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
    exact inputs.mem_executionRows_of_memReplayRows
      (activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded_of_main_mem_op_one
        h_mutable h_mainEval h_main_mem_op h_entry
        (mutableActiveMemReplayRowsEmbeddedInTrace_of_fullWitnessMemReplayBridge
          (ziskTrace.memReplayBridge h_nonempty)
          (ziskTrace.memReplayBridge_coversMutableMemTables h_nonempty)))
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
    inputs.mem_or_memAlignProvider_of_loadBMemProviderEntry
      i h_b_src_ind h_active h_selectedMemAlignPins
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
