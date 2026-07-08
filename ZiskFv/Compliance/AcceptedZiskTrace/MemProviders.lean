import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridges

/-!
# Derived memory-bus provider coverage

Accepted traces derive the full memory-bus provider branch split from
`channels_balanced` plus derived `spec_holds`. The mutable-Mem specialization
keeps the remaining phase-1 residue explicit: callers must rule out the named
non-mutable branches (MemAlign family, Main self-provider, RegisterBoundary).
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- The accepted trace exposes the full active-Main memory-bus provider branch
    split. The non-Mem branches remain visible in
    `ActiveMainMemProviderRowMatchSpec`; this theorem only derives the branch
    split from accepted trace data. -/
theorem AcceptedZiskTrace.activeMainMemProviderRowMatchSpec_of_active_main_eval
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL} :
    trace.mainTable.component.Spec (trace.mainTable.environment mainRow)
      ∧ ActiveMainMemProviderRowMatchSpec trace.program trace.witness trace.mainTable
        mainRow mainInteraction mainMsg multiplicity as :=
  ZiskFv.AirsClean.FullEnsemble.activeMainMemProviderRowMatchSpec_of_active_main_eval
    trace.witness trace.channels_balanced trace.spec_holds trace.mainTable_mem
    h_mainRow h_mainInteraction h_mainEval h_active

/-- If the caller supplies the narrow syntactic residue excluding the
    non-mutable provider branches, the accepted trace gives the mutable-Mem
    provider branch for the selected active Main memory-bus interaction. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderRowMatchSpec_of_active_main_eval_no_nonmutable
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg multiplicity as) :
    trace.mainTable.component.Spec (trace.mainTable.environment mainRow)
      ∧ ActiveMainMutableMemProviderRowMatchSpec trace.program trace.witness trace.mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  have h_match :=
    trace.activeMainMemProviderRowMatchSpec_of_active_main_eval
      h_mainRow h_mainInteraction h_mainEval h_active
      (multiplicity := multiplicity) (as := as)
  exact ⟨h_match.1,
    activeMainMutableMemProviderRowMatchSpec_of_no_nonmutable
      h_match.2 h_no_nonmutable⟩

/-- Accepted-trace wrapper exposing the mutable-Mem provider branch as exact
    primary/dual Mem replay-row alternatives for a concrete Main-side memory
    entry.

This is still a row-correspondence step, not a read-soundness assumption: it
only combines accepted channel balance with the explicit non-mutable-branch
exclusion and a caller-supplied match between the concrete execution entry and
the selected Main memory-bus message. Primary `wr = 0` remains visible
downstream. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderReplayBranchCases_of_active_main_eval_no_nonmutable
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {entry : Interaction.MemoryBusEntry FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (trace.mainTable.environment mainRow) mainMsg) (-1) 2)) :
    (∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component.Spec (providerTable.environment providerRow)
          ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
          ∧ (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1
          ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry entry
              (memPrimaryReadReplayEntryOfRow
                (eval (providerTable.environment providerRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)))
    ∨
    (∃ providerTable ∈ trace.witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component.Spec (providerTable.environment providerRow)
          ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
          ∧ (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1
          ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry entry
              (memDualReadReplayEntryOfRow
                (eval (providerTable.environment providerRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) := by
  have h_mutable :=
    (trace.activeMainMutableMemProviderRowMatchSpec_of_active_main_eval_no_nonmutable
      h_mainRow h_mainInteraction h_mainEval h_active h_no_nonmutable).2
  exact activeMainMutableMemProviderRowMatchSpec_replay_branch_cases h_mutable h_entry

/-- Accepted-trace wrapper placing a concrete active Main memory entry in the
    accepted chronological row list through the mutable-Mem provider branch.

This remains conditional on two narrow residues: active mutable-Mem replay rows
are embedded in the chronological row list, and primary selected provider
matches are known to be reads (`wr = 0`). -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderEntryMemOfActiveReplayEmbedded_of_active_main_eval_no_nonmutable
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (trace.mainTable.environment mainRow) mainMsg) (-1) 2))
    (h_embedded :
      MutableActiveMemReplayRowsEmbeddedInTrace trace.witness rows)
    (h_primary_read :
      ∀ providerTable providerRow,
        providerTable ∈ trace.witness.allTables →
        providerRow ∈ providerTable.table →
        providerTable.component.Spec (providerTable.environment providerRow) →
        providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1 →
        ZiskFv.Airs.MemoryBus.matches_memory_entry entry
          (memPrimaryReadReplayEntryOfRow
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) →
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    entry ∈ rows := by
  have h_mutable :=
    (trace.activeMainMutableMemProviderRowMatchSpec_of_active_main_eval_no_nonmutable
      h_mainRow h_mainInteraction h_mainEval h_active h_no_nonmutable).2
  exact activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded
    h_mutable h_entry h_embedded h_primary_read

/-- Accepted-trace wrapper for selected Main loads whose PIL memory opcode is
    syntactically `mem_op = 1`.

The primary Mem `wr = 0` fact is derived from Clean message equality instead
of being supplied by the caller. The remaining residue is the active
mutable-Mem replay embedding into the chronological row list. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderEntryMemOfActiveReplayEmbedded_of_main_mem_op_one
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_mem_op :
      (eval (trace.mainTable.environment mainRow) mainMsg).mem_op = 1)
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (trace.mainTable.environment mainRow) mainMsg) (-1) 2))
    (h_embedded :
      MutableActiveMemReplayRowsEmbeddedInTrace trace.witness rows) :
    entry ∈ rows := by
  have h_mutable :=
    (trace.activeMainMutableMemProviderRowMatchSpec_of_active_main_eval_no_nonmutable
      h_mainRow h_mainInteraction h_mainEval h_active h_no_nonmutable).2
  exact activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded_of_main_mem_op_one
    h_mutable h_mainEval h_main_mem_op h_entry h_embedded

/-- Accepted-trace wrapper for selected Main stores whose PIL memory opcode is
    syntactically `mem_op = 2`.

The Clean Main interaction is still an active pull (`mult = -1`), while the
legacy execution row being matched is a write row (`multiplicity = 1`,
`as = 2`). The primary Mem `wr = 1` fact and impossible dual branch are
derived from Clean message equality. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderEntryMemOfActiveReplayEmbedded_of_main_mem_op_two
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_mem_op :
      (eval (trace.mainTable.environment mainRow) mainMsg).mem_op = 2)
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg 1 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (trace.mainTable.environment mainRow) mainMsg) 1 2))
    (h_embedded :
      MutableActiveMemReplayRowsEmbeddedInTrace trace.witness rows) :
    entry ∈ rows := by
  have h_mutable :=
    (trace.activeMainMutableMemProviderRowMatchSpec_of_active_main_eval_no_nonmutable
      h_mainRow h_mainInteraction h_mainEval h_active h_no_nonmutable).2
  exact activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded_of_main_mem_op_two
    h_mutable h_mainEval h_main_mem_op h_entry h_embedded

/-- The accepted trace's source-correlation certificate gives the replay-bridge
    coverage predicate used by Mem replay embedding lemmas. -/
theorem AcceptedZiskTrace.memReplayBridge_coversMutableMemTables
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions) :
    FullWitnessMemReplayBridgeCoversMutableMemTables
      (trace.memReplayBridge h_nonempty) := by
  intro table h_table h_component
  have h_eq := trace.mem_replay_source_covers h_nonempty table h_table h_component
  simpa [AcceptedZiskTrace.memReplayBridge, AcceptedZiskTrace.memReplayRows,
    AcceptedZiskTrace.memReplaySource, FullWitnessMemAirSource.replayBridge,
    fullWitnessMemReplayBridge_of_memAirSource,
    fullWitnessMemReplayBridge_of_memTable_fixedL1_airFacts,
    fullWitnessMemReplayBridge_of_memTable_fixedL1,
    fullWitnessMemReplayBridge_of_memTable] using h_eq

/-- Accepted-trace wrapper using the trace-selected Mem replay bridge as the
    chronological row list.

The source-correlation residue is now the accepted trace's guarded structural
coverage certificate, not a seed-side hypothesis. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderEntryMemOfReplayBridge_of_main_mem_op_one
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_mem_op :
      (eval (trace.mainTable.environment mainRow) mainMsg).mem_op = 1)
    {entry : Interaction.MemoryBusEntry FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (trace.mainTable.environment mainRow) mainMsg) (-1) 2)) :
    entry ∈ trace.memReplayRows h_nonempty := by
  exact trace.activeMainMutableMemProviderEntryMemOfActiveReplayEmbedded_of_main_mem_op_one
    h_mainRow h_mainInteraction h_mainEval h_active h_main_mem_op h_no_nonmutable h_entry
    (mutableActiveMemReplayRowsEmbeddedInTrace_of_fullWitnessMemReplayBridge
      (trace.memReplayBridge h_nonempty)
      (trace.memReplayBridge_coversMutableMemTables h_nonempty))

/-- Accepted-trace replay-bridge wrapper for selected Main stores whose PIL
    memory opcode is syntactically `mem_op = 2`. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderEntryMemOfReplayBridge_of_main_mem_op_two
    {n : Nat} (trace : AcceptedZiskTrace n)
    (h_nonempty : 0 < trace.numInstructions)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    (h_main_mem_op :
      (eval (trace.mainTable.environment mainRow) mainMsg).mem_op = 2)
    {entry : Interaction.MemoryBusEntry FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg 1 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (trace.mainTable.environment mainRow) mainMsg) 1 2)) :
    entry ∈ trace.memReplayRows h_nonempty := by
  exact trace.activeMainMutableMemProviderEntryMemOfActiveReplayEmbedded_of_main_mem_op_two
    h_mainRow h_mainInteraction h_mainEval h_active h_main_mem_op h_no_nonmutable h_entry
    (mutableActiveMemReplayRowsEmbeddedInTrace_of_fullWitnessMemReplayBridge
      (trace.memReplayBridge h_nonempty)
      (trace.memReplayBridge_coversMutableMemTables h_nonempty))

end ZiskFv.Compliance
