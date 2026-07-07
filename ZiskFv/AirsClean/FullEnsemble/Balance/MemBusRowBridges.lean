import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction
import ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridges
import ZiskFv.AirsClean.FullEnsemble.Balance.MemRowReplayProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.TableProjections
import ZiskFv.AirsClean.FullEnsemble.Balance.SidecarColumns
import ZiskFv.AirsClean.FullEnsemble.Balance.RowsBridgeFacts
import ZiskFv.AirsClean.FullEnsemble.Balance.TimelineEvidence
import ZiskFv.AirsClean.FullEnsemble.Balance.EmbeddedInTrace

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-! ## Full-ensemble memory-bus row bridges -/

/-- Compose a selected Main `b` memory pull from the full ensemble with a
    selected Mem provider row.

Clean balance supplies equality of the raw PIL memory-bus messages, while
the load witness carries a legacy-entry match for the Main pull.  This
adapter translates those facts into the payload-only provider match needed
by the Mem row bridge; multiplicity polarity is intentionally not part of
the conclusion. -/
theorem mem_provider_payload_match_of_main_b_match_and_msg_eq
    {mainRow : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRow : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRow)) (-1) 2)) :
    ZiskFv.Airs.MemoryBus.matches_memory_payload entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Mem.memBusMessage (eval memEnv memRow)) 1 2) := by
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval mainEnv (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow))
          (-1) 2) := by
    simpa [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] using h_main_match
  have h_raw :
      (((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv).msg =
        (((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_payload :=
    ZiskFv.Airs.MemoryBus.matches_memory_payload_of_left_match_eval_emitted_provider_msg_eq
      (mainMsg := ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)
      (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)
      (mainMult := mainMult)
      (providerMult := providerMult)
      (mainEnv := mainEnv)
      (providerEnv := memEnv)
      (entry := entry)
      (mainMultiplicity := (-1 : FGL))
      (providerMultiplicity := (1 : FGL))
      (as := (2 : FGL))
      h_entry h_raw
  simpa [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] using h_payload

/-- Compose a selected Main `b` memory pull with a selected primary Mem
    provider row, viewed as the read-replay row used by chronological memory
    replay.

Unlike the provider-side Clean interaction, the replay projection uses legacy
read multiplicity `-1`, so this theorem returns full `matches_memory_entry`
for `memPrimaryReadReplayEntryOfRow`. -/
theorem mem_primary_read_replay_entry_match_of_main_b_match_and_msg_eq
    {mainRow : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL}
    {memRow : Var ZiskFv.AirsClean.Mem.MemRow FGL}
    {mainEnv memEnv : Environment FGL}
    {mainMult providerMult : Expression FGL}
    {mainInteraction providerInteraction : Interaction FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv)
    (h_providerEval :
      providerInteraction =
        ((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv)
    (h_msg : providerInteraction.msg = mainInteraction.msg)
    (h_main_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.bMemMessage (eval mainEnv mainRow)) (-1) 2)) :
    ZiskFv.Airs.MemoryBus.matches_memory_entry entry
      (memPrimaryReadReplayEntryOfRow (eval memEnv memRow)) := by
  have h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval mainEnv (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow))
          (-1) 2) := by
    simpa [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] using h_main_match
  have h_raw :
      (((MemBusChannel.emitted providerMult
          (ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)).toRaw).eval
          memEnv).msg =
        (((MemBusChannel.emitted mainMult
          (ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)).toRaw).eval
          mainEnv).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_of_left_match_eval_emitted_provider_msg_eq
      (mainMsg := ZiskFv.AirsClean.Main.bMemMessageExpr mainRow)
      (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr memRow)
      (mainMult := mainMult)
      (providerMult := providerMult)
      (mainEnv := mainEnv)
      (providerEnv := memEnv)
      (entry := entry)
      (multiplicity := (-1 : FGL))
      (as := (2 : FGL))
      h_entry h_raw
  simpa [memPrimaryReadReplayEntryOfRow,
    ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] using h_provider

/-- A unified-Main provider-row interaction, paired with the payload match
    induced by Clean message equality. This is the match-carrying counterpart
    of `MainMemBusRowInteractionEval`. -/
@[reducible]
def MainMemBusRowInteractionMatchEval
    {length : ℕ} (program : Program length)
    (providerTable : Table FGL) (providerRow : Array FGL)
    (providerInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (mainEnv : Environment FGL) (multiplicity as : FGL) : Prop :=
  (providerInteraction =
      ((MemBusChannel.emitted
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.rom.a_src_reg
        (ZiskFv.AirsClean.Main.aRegPreMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)
    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval mainEnv mainMsg) multiplicity as)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.aRegPreMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar))
        multiplicity as))
  ∨ (providerInteraction =
      ((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg))
        (ZiskFv.AirsClean.Main.aMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)
    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval mainEnv mainMsg) multiplicity as)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.aMemMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar))
        multiplicity as))
  ∨ (providerInteraction =
      ((MemBusChannel.emitted
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.rom.b_src_reg
        (ZiskFv.AirsClean.Main.bRegPreMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)
    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval mainEnv mainMsg) multiplicity as)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.bRegPreMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar))
        multiplicity as))
  ∨ (providerInteraction =
      ((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg))
        (ZiskFv.AirsClean.Main.bMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)
    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval mainEnv mainMsg) multiplicity as)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.bMemMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar))
        multiplicity as))
  ∨ (providerInteraction =
      ((MemBusChannel.emitted
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.rom.store_reg
        (ZiskFv.AirsClean.Main.cRegPreMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)
    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval mainEnv mainMsg) multiplicity as)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.cRegPreMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar))
        multiplicity as))
  ∨ (providerInteraction =
      ((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg))
        (ZiskFv.AirsClean.Main.cMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)
    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval mainEnv mainMsg) multiplicity as)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.cMemMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar))
        multiplicity as))

/-- Row-native full-ensemble memory projection: an active unified-Main
    memory-bus interaction has a balanced same-message counterpart on a
    concrete full-ensemble table row.

The provider side keeps the unified Main branch explicit. This mirrors
    `exists_matching_mem_component_of_active_main_interaction`: excluding
    Main memory self-matches still needs selector legality that is not yet
    available from Clean Main row soundness. -/
theorem exists_mem_provider_row_msg_eq_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      MainMemBusRowInteractionEval program mainTable mainRow mainInteraction
      ∧ ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
        providerInteraction.msg = mainInteraction.msg
          ∧ providerInteraction.mult ≠ -1
          ∧ providerInteraction.mult ≠ 0
          ∧ ∃ providerTable ∈ witness.allTables,
            providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
              ∧
              ((∃ providerRow ∈ providerTable.table,
                  providerTable.component =
                    ZiskFv.AirsClean.MemAlignReadByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.MemAlign.component
                    ∧ providerInteraction =
                      ((MemBusChannel.emitted
                        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                    ∧
                      (providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                            (ZiskFv.AirsClean.Mem.memBusMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∨ providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                            (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component =
                    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                    ∧ MainMemBusRowInteractionEval
                      program providerTable providerRow providerInteraction)
                -- Register boundary provider (register `mem_op=3` boot/reload emission).
                -- Carried structurally; excluded for data-memory (`mem_op∈{1,2}`) mains downstream
                -- by `mem_op` disjointness (`registerBoundary` msgs have `mem_op=3`).
                ∨ providerTable.component =
                    ZiskFv.AirsClean.RegisterBoundary.component) := by
  have h_main_mem_witness :
      mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_mem_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_mem_component_of_active_main_interaction
      witness h_balanced h_main_mem_witness h_active
  refine ⟨mainRow, h_mainRow, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable, h_providerTable,
    h_providerInteraction, ?_⟩
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main | h_regBoundary
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignReadByte_row_eval_of_interaction_mem
        h_marb h_providerInteraction
    left
    exact ⟨providerRow, h_providerRow, h_marb, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem h_mab h_providerInteraction
    right
    left
    exact ⟨providerRow, h_providerRow, h_mab, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlign_row_eval_of_interaction_mem h_memAlign h_providerInteraction
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_memAlign, h_providerEval⟩
  · rcases exists_mem_dual_row_eval_of_interaction_mem
        h_mem h_providerInteraction with h_primary | h_dual
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_primary
      right
      right
      right
      left
      exact ⟨providerRow, h_providerRow, h_mem, Or.inl h_providerEval⟩
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_dual
      right
      right
      right
      left
      exact ⟨providerRow, h_providerRow, h_mem, Or.inr h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_main_mem_row_eval_of_interaction_mem h_main h_providerInteraction
    right
    right
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_main, h_providerEval⟩
  · -- RegisterBoundary provider: carried structurally (register mem_op=3 emission).
    right
    right
    right
    right
    right
    exact h_regBoundary

/-- Spec-carrying variant of
    `exists_mem_provider_row_msg_eq_of_active_main_table_interaction`.

This is structural unpacking only: `witness.Spec` already states per-row
specification for every table in the full ensemble, and this lemma threads it
to the concrete Main/provider rows selected by balance. -/
theorem exists_mem_provider_row_msg_eq_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧
        MainMemBusRowInteractionEval program mainTable mainRow mainInteraction
        ∧ ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.MemAlignReadByte.component
                      ∧ providerInteraction =
                        ((MemBusChannel.pushed
                          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                      ∧ providerInteraction =
                        ((MemBusChannel.pushed
                          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                      ∧ providerInteraction =
                        ((MemBusChannel.emitted
                          (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                            - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                              ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                      ∧
                        (providerInteraction =
                            ((MemBusChannel.emitted
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                              (ZiskFv.AirsClean.Mem.memBusMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                              (providerTable.environment providerRow)
                          ∨ providerInteraction =
                            ((MemBusChannel.emitted
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                              (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                              (providerTable.environment providerRow)))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                      ∧ MainMemBusRowInteractionEval
                        program providerTable providerRow providerInteraction)
                  -- Register boundary provider (register `mem_op=3` emission), carried structurally.
                  ∨ providerTable.component =
                      ZiskFv.AirsClean.RegisterBoundary.component) := by
  obtain ⟨mainRow, h_mainRow, h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable, h_providerTable,
      h_providerInteraction, h_providerComponent⟩ :=
    exists_mem_provider_row_msg_eq_of_active_main_table_interaction
      witness h_balanced h_mainTable h_mainComponent h_mainInteraction h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main | h_regBoundary
  · rcases h_marb with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_mab with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_memAlign with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_mem with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · rcases h_main with ⟨providerRow, h_providerRow, h_component, h_eval⟩
    right
    right
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩
  · -- RegisterBoundary provider: carried structurally (register mem_op=3 emission).
    right
    right
    right
    right
    right
    exact h_regBoundary

/-- Selected-branch legacy-entry view of the full-ensemble memory-bus bridge.

    Callers that have already selected a concrete Main memory interaction can
    use this theorem to carry Clean balance through the full memory ensemble
    and obtain the legacy `matches_memory_entry` facts expected by the
    existing load/store bridge layer. The unified Main provider branch stays
    explicit; ruling it out still requires selector legality rather than a
    caller promise. -/
theorem exists_mem_provider_row_matches_entry_spec_of_active_main_eval
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL} :
    mainTable.component.Spec (mainTable.environment mainRow)
      ∧ ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
        providerInteraction.msg = mainInteraction.msg
          ∧ providerInteraction.mult ≠ -1
          ∧ providerInteraction.mult ≠ 0
          ∧ ∃ providerTable ∈ witness.allTables,
            providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
              ∧
              ((∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component =
                      ZiskFv.AirsClean.MemAlignReadByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                        multiplicity as))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                    ∧ providerInteraction =
                      ((MemBusChannel.pushed
                        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                        multiplicity as))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                    ∧ providerInteraction =
                      ((MemBusChannel.emitted
                        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                            ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                        multiplicity as))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                    ∧
                      ((providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                            (ZiskFv.AirsClean.Mem.memBusMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (mainTable.environment mainRow) mainMsg)
                            multiplicity as)
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (providerTable.environment providerRow)
                              (ZiskFv.AirsClean.Mem.memBusMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                            multiplicity as))
                      ∨ (providerInteraction =
                          ((MemBusChannel.emitted
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                            (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (mainTable.environment mainRow) mainMsg)
                            multiplicity as)
                          (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                            (eval (providerTable.environment providerRow)
                              (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                                ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                            multiplicity as))))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component.Spec (providerTable.environment providerRow)
                    ∧ providerTable.component =
                      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                    ∧ MainMemBusRowInteractionMatchEval
                      program providerTable providerRow providerInteraction mainMsg
                      (mainTable.environment mainRow) multiplicity as)
                -- Register boundary provider (register `mem_op=3` emission), carried structurally.
                ∨ providerTable.component =
                    ZiskFv.AirsClean.RegisterBoundary.component) := by
  have h_main_mem_witness :
      mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_mem_component_of_active_main_interaction
      witness h_balanced h_main_mem_witness h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨h_mainSpec, providerInteraction, h_provider_witness, h_msg,
    h_nonpull, h_nonzero, providerTable, h_providerTable,
    h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main | h_regBoundary
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignReadByte_row_eval_of_interaction_mem
        h_marb h_providerInteraction
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_marb, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem h_mab h_providerInteraction
    right
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_mab, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlign_row_eval_of_interaction_mem h_memAlign h_providerInteraction
    right
    right
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_memAlign, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · rcases exists_mem_dual_row_eval_of_interaction_mem
        h_mem h_providerInteraction with h_primary | h_dual
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_primary
      right
      right
      right
      left
      refine ⟨providerRow, h_providerRow,
        h_providerSpecs providerRow h_providerRow, h_mem, ?_⟩
      left
      refine ⟨h_providerEval, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
    · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ := h_dual
      right
      right
      right
      left
      refine ⟨providerRow, h_providerRow,
        h_providerSpecs providerRow h_providerRow, h_mem, ?_⟩
      right
      refine ⟨h_providerEval, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_main_mem_row_eval_of_interaction_mem h_main h_providerInteraction
    right
    right
    right
    right
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_main, ?_⟩
    rcases h_providerEval with h_a_prev | h_a | h_b_prev | h_b | h_c_prev | h_c
    · left
      refine ⟨h_a_prev, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_a_prev, ← h_mainEval]
      exact h_msg
    · right
      left
      refine ⟨h_a, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_a, ← h_mainEval]
      exact h_msg
    · right
      right
      left
      refine ⟨h_b_prev, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_b_prev, ← h_mainEval]
      exact h_msg
    · right
      right
      right
      left
      refine ⟨h_b, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_b, ← h_mainEval]
      exact h_msg
    · right
      right
      right
      right
      left
      refine ⟨h_c_prev, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_c_prev, ← h_mainEval]
      exact h_msg
    · right
      right
      right
      right
      right
      refine ⟨h_c, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_c, ← h_mainEval]
      exact h_msg
  · -- RegisterBoundary provider: carried structurally (register mem_op=3 emission).
    right
    right
    right
    right
    right
    exact h_regBoundary

/-- Named provider-row coverage produced by a balanced active Main memory-bus
    interaction.

This is the reusable form of
`exists_mem_provider_row_matches_entry_spec_of_active_main_eval`'s provider
side.  The mutable-Mem branch is still only one alternative: the alignment
tables and unified-Main branch remain visible because the current balance proof
does not rule them out. -/
def ActiveMainMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧
          ((∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.MemAlignReadByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                ∧ providerInteraction =
                  ((MemBusChannel.emitted
                    (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                      - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                    (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
                ∧
                  ((providerInteraction =
                      ((MemBusChannel.emitted
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                        (ZiskFv.AirsClean.Mem.memBusMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.Mem.memBusMessageExpr
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                        multiplicity as))
                  ∨ (providerInteraction =
                      ((MemBusChannel.emitted
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                        (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow)
                    ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (mainTable.environment mainRow) mainMsg)
                        multiplicity as)
                      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                        multiplicity as))))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                ∧ MainMemBusRowInteractionMatchEval
                  program providerTable providerRow providerInteraction mainMsg
                  (mainTable.environment mainRow) multiplicity as)
            -- Register boundary provider (register `mem_op=3` emission), carried structurally.
            ∨ providerTable.component =
                ZiskFv.AirsClean.RegisterBoundary.component)

/-- Mutable-Mem branch of `ActiveMainMemProviderRowMatchSpec`.

This is the direct provider branch needed to identify a selected load with a
row of the witness-selected mutable Mem table. Direct full-width loads should
aim to prove this branch from the named balance coverage plus route/selector
facts. -/
def ActiveMainMutableMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
              ∧
                ((providerInteraction =
                    ((MemBusChannel.emitted
                      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
                      (ZiskFv.AirsClean.Mem.memBusMessageExpr
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Mem.memBusMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                      multiplicity as))
                ∨ (providerInteraction =
                    ((MemBusChannel.emitted
                      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
                      (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
                      (providerTable.environment providerRow)
                  ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))
                      multiplicity as)))

/-- Normalize the mutable-Mem provider branch to the replay-row alternatives
    used by chronological memory replay.

This deliberately stops before primary read/write polarity: callers still have
to prove `wr = 0` for primary read rows before using the active read/write
replay surface. -/
theorem activeMainMutableMemProviderRowMatchSpec_replay_branch_cases
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_mutable :
      ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) (-1) 2)) :
    (∃ providerTable ∈ witness.allTables,
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
    (∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component.Spec (providerTable.environment providerRow)
          ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
          ∧ (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1
          ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry entry
              (memDualReadReplayEntryOfRow
                (eval (providerTable.environment providerRow)
                  ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) := by
  rcases h_mutable with
    ⟨providerInteraction, _h_providerInteraction_mem, _h_msg, _h_provider_non_pull,
      h_provider_nonzero, providerTable, h_providerTable_mem, _h_providerInteraction_table,
      providerRow, h_providerRow_mem, h_providerSpec, h_providerComponent,
      h_branch⟩
  let component := ZiskFv.AirsClean.Mem.componentWithDualMemBus
  let providerEnv := providerTable.environment providerRow
  have h_mem_component_spec : component.Spec providerEnv := by
    simpa [component, providerEnv, h_providerComponent] using h_providerSpec
  have h_input_eq :
      eval providerEnv component.rowInputVar = component.rowInput providerEnv := by
    simpa only [component, Air.Flat.Component.rowInput,
      Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 providerEnv)
  have h_memSpec :
      ZiskFv.AirsClean.Mem.Spec (eval providerEnv component.rowInputVar) := by
    have h_spec :=
      ZiskFv.AirsClean.Mem.spec_of_componentWithDualMemBus_spec
        providerEnv h_mem_component_spec
    rw [← h_input_eq] at h_spec
    exact h_spec
  rcases h_branch with h_primary | h_dual
  · rcases h_primary with ⟨h_eval, h_provider_match⟩
    have h_match :
        ZiskFv.Airs.MemoryBus.matches_memory_entry entry
          (memPrimaryReadReplayEntryOfRow
            (eval providerEnv
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) := by
      have h_trans :=
        ZiskFv.Airs.MemoryBus.matches_memory_entry_trans h_entry h_provider_match
      simpa [providerEnv, memPrimaryReadReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.eval_memBusMessageExpr] using h_trans
    have h_mult_expr :
        providerInteraction.mult =
          Expression.eval providerEnv component.rowInputVar.sel := by
      simpa [component, providerEnv, Channel.emitted, emitted,
        ChannelInteraction.toRaw, AbstractInteraction.eval] using
          congrArg Interaction.mult h_eval
    have h_mult :
        providerInteraction.mult =
          (eval providerEnv component.rowInputVar).sel :=
      h_mult_expr.trans (ZiskFv.AirsClean.Mem.eval_memRow_sel providerEnv component.rowInputVar)
    have h_sel_ne_zero :
        (eval providerEnv component.rowInputVar).sel ≠ 0 := by
      intro h_zero
      exact h_provider_nonzero (by simp [h_mult, h_zero])
    have h_sel :
        (eval providerEnv component.rowInputVar).sel = 1 := by
      rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec
          (eval providerEnv component.rowInputVar) h_memSpec with h_zero | h_one
      · exact False.elim (h_sel_ne_zero h_zero)
      · exact h_one
    exact Or.inl
      ⟨providerTable, h_providerTable_mem, providerRow, h_providerRow_mem,
        h_providerSpec, h_providerComponent, by simpa [component, providerEnv] using h_sel,
        by simpa [providerEnv] using h_match⟩
  · rcases h_dual with ⟨h_eval, h_provider_match⟩
    have h_match :
        ZiskFv.Airs.MemoryBus.matches_memory_entry entry
          (memDualReadReplayEntryOfRow
            (eval providerEnv
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) := by
      have h_trans :=
        ZiskFv.Airs.MemoryBus.matches_memory_entry_trans h_entry h_provider_match
      simpa [providerEnv, memDualReadReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr] using h_trans
    have h_mult_expr :
        providerInteraction.mult =
          Expression.eval providerEnv component.rowInputVar.sel_dual := by
      simpa [component, providerEnv, Channel.emitted, emitted,
        ChannelInteraction.toRaw, AbstractInteraction.eval] using
          congrArg Interaction.mult h_eval
    have h_mult :
        providerInteraction.mult =
          (eval providerEnv component.rowInputVar).sel_dual :=
      h_mult_expr.trans
        (ZiskFv.AirsClean.Mem.eval_memRow_sel_dual providerEnv component.rowInputVar)
    have h_sel_dual_ne_zero :
        (eval providerEnv component.rowInputVar).sel_dual ≠ 0 := by
      intro h_zero
      exact h_provider_nonzero (by simp [h_mult, h_zero])
    have h_sel_dual :
        (eval providerEnv component.rowInputVar).sel_dual = 1 := by
      rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec
          (eval providerEnv component.rowInputVar) h_memSpec with h_zero | h_one
      · exact False.elim (h_sel_dual_ne_zero h_zero)
      · exact h_one
    exact Or.inr
      ⟨providerTable, h_providerTable_mem, providerRow, h_providerRow_mem,
        h_providerSpec, h_providerComponent, by simpa [component, providerEnv] using h_sel_dual,
        by simpa [providerEnv] using h_match⟩

/-- Active mutable-Mem provider coverage places the concrete Main-side entry
    in the accepted chronological row trace, once callers supply the active
    mutable-Mem replay embedding and the narrow primary-read polarity fact.

The primary `wr = 0` hypothesis is intentionally separate: active replay
embedding proves row presence, while read/write polarity still has to come
from the selected Mem message facts or a narrow syntactic certificate. -/
theorem activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_mutable :
      ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg (-1) 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) (-1) 2))
    (h_embedded :
      MutableActiveMemReplayRowsEmbeddedInTrace witness rows)
    (h_primary_read :
      ∀ providerTable providerRow,
        providerTable ∈ witness.allTables →
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
  rcases activeMainMutableMemProviderRowMatchSpec_replay_branch_cases h_mutable h_entry with
    h_primary | h_dual
  · rcases h_primary with
      ⟨providerTable, h_providerTable_mem, providerRow, h_providerRow_mem,
        h_providerSpec, h_providerComponent, h_sel, h_match⟩
    exact mem_primary_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
      (h_embedded providerTable h_providerTable_mem h_providerComponent)
      h_providerRow_mem h_sel
      (h_primary_read providerTable providerRow h_providerTable_mem h_providerRow_mem
        h_providerSpec h_providerComponent h_sel h_match)
      h_match
  · rcases h_dual with
      ⟨providerTable, h_providerTable_mem, providerRow, h_providerRow_mem,
        _h_providerSpec, h_providerComponent, h_sel_dual, h_match⟩
    exact mem_dual_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
      (h_embedded providerTable h_providerTable_mem h_providerComponent)
      h_providerRow_mem h_sel_dual h_match

/-- Non-mutable provider branches of `ActiveMainMemProviderRowMatchSpec`.

For subword loads, some MemAlign branches are legitimate intermediate routes
and must be followed to mutable Mem rather than discarded. For direct loads,
this predicate is the exact branch family to rule out before extracting a
mutable-Mem selected row. -/
def ActiveMainNonMutableMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧
          ((∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.MemAlignReadByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
                ∧ providerInteraction =
                  ((MemBusChannel.pushed
                    (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
                ∧ providerInteraction =
                  ((MemBusChannel.emitted
                    (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                      - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                    (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                    (providerTable.environment providerRow)
                ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                    multiplicity as))
            ∨ (∃ providerRow ∈ providerTable.table,
              providerTable.component.Spec (providerTable.environment providerRow)
                ∧ providerTable.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
                ∧ MainMemBusRowInteractionMatchEval
                  program providerTable providerRow providerInteraction mainMsg
                  (mainTable.environment mainRow) multiplicity as)
            -- Register boundary provider (register `mem_op=3` emission), carried structurally.
            ∨ providerTable.component =
                ZiskFv.AirsClean.RegisterBoundary.component)

/-- MemAlignReadByte branch of
    `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainMemAlignReadByteProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component =
                ZiskFv.AirsClean.MemAlignReadByte.component
              ∧ providerInteraction =
                ((MemBusChannel.pushed
                  (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (mainTable.environment mainRow) mainMsg)
                  multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
                  multiplicity as)

/-- MemAlignByte branch of
    `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainMemAlignByteProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
              ∧ providerInteraction =
                ((MemBusChannel.pushed
                  (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (mainTable.environment mainRow) mainMsg)
                  multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
                  multiplicity as)

/-- MemAlign branch of `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainMemAlignProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
              ∧ providerInteraction =
                ((MemBusChannel.emitted
                  (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                    - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                  (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ZiskFv.Airs.MemoryBus.matches_memory_entry
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (mainTable.environment mainRow) mainMsg)
                  multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                  multiplicity as)

/-- Main self-provider branch of
    `ActiveMainNonMutableMemProviderRowMatchSpec`. -/
def ActiveMainSelfMemProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mainTable : Table FGL)
    (mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (multiplicity as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component =
                ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
              ∧ MainMemBusRowInteractionMatchEval
                program providerTable providerRow providerInteraction mainMsg
                (mainTable.environment mainRow) multiplicity as

/-- Register-boundary provider branch of `ActiveMainNonMutableMemProviderRowMatchSpec`.

The register `mem_op=3` boot/reload emission carried structurally: it records only that the
same-message counterpart lives in a RegisterBoundary table.  For data-memory (`mem_op∈{1,2}`) mains
this branch is unreachable by `mem_op` disjointness, but this repackaging layer stays general. -/
def ActiveMainRegisterBoundaryProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (_mainTable : Table FGL)
    (_mainRow : Array FGL)
    (mainInteraction : Interaction FGL)
    (_mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (_multiplicity _as : FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.msg = mainInteraction.msg
      ∧ providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ providerTable.component = ZiskFv.AirsClean.RegisterBoundary.component

/-- Branch split for the non-mutable active-Main provider family. -/
theorem activeMainNonMutableMemProviderRowMatchSpec_branch_cases
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_nonmutable :
      ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as) :
    ActiveMainMemAlignReadByteProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainMemAlignByteProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainMemAlignProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainSelfMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as
      ∨ ActiveMainRegisterBoundaryProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  rcases h_nonmutable with
    ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_branch⟩
  rcases h_branch with h_marb | h_mab | h_memAlign | h_main | h_regBoundary
  · left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_marb⟩
  · right; left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_mab⟩
  · right; right; left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_memAlign⟩
  · right; right; right; left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_main⟩
  · right; right; right; right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_regBoundary⟩

/-- Ruling out each named non-mutable branch rules out the aggregate
    non-mutable provider family. -/
theorem activeMainNonMutableMemProviderRowMatchSpec_of_no_branch
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_no_marb :
      ¬ ActiveMainMemAlignReadByteProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_mab :
      ¬ ActiveMainMemAlignByteProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_memAlign :
      ¬ ActiveMainMemAlignProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_main :
      ¬ ActiveMainSelfMemProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as)
    (h_no_regBoundary :
      ¬ ActiveMainRegisterBoundaryProviderRowMatchSpec program witness
        mainTable mainRow mainInteraction mainMsg multiplicity as) :
    ¬ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
      mainRow mainInteraction mainMsg multiplicity as := by
  intro h_nonmutable
  rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases
      h_nonmutable with h_marb | h_mab | h_memAlign | h_main | h_regBoundary
  · exact h_no_marb h_marb
  · exact h_no_mab h_mab
  · exact h_no_memAlign h_memAlign
  · exact h_no_main h_main
  · exact h_no_regBoundary h_regBoundary

/-- Split named active-Main provider coverage into mutable-Mem and
    non-mutable branches. -/
theorem activeMainMemProviderRowMatchSpec_mutable_or_nonmutable
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_match :
      ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as) :
    ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as
      ∨ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  rcases h_match with
    ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_branch⟩
  rcases h_branch with h_marb | h_mab | h_memAlign | h_mem | h_main | h_regBoundary
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inl h_marb⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inl h_mab)⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inr (Or.inl h_memAlign))⟩
  · left
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_mem⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inr (Or.inr (Or.inl h_main)))⟩
  · right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      Or.inr (Or.inr (Or.inr (Or.inr h_regBoundary)))⟩

/-- Direct-load route target: if non-mutable branches are ruled out, the named
    active-Main provider coverage yields the mutable-Mem provider branch. -/
theorem activeMainMutableMemProviderRowMatchSpec_of_no_nonmutable
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_match :
      ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as)
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as) :
    ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
      mainInteraction mainMsg multiplicity as := by
  rcases activeMainMemProviderRowMatchSpec_mutable_or_nonmutable h_match with
    h_mutable | h_nonmutable
  · exact h_mutable
  · exact False.elim (h_no_nonmutable h_nonmutable)

/-- Named version of
    `exists_mem_provider_row_matches_entry_spec_of_active_main_eval`.

This is intentionally only a repackaging theorem.  It gives later memory-trace
integration a stable hook while preserving the unresolved provider-branch
disjunction. -/
theorem activeMainMemProviderRowMatchSpec_of_active_main_eval
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL} :
    mainTable.component.Spec (mainTable.environment mainRow)
      ∧ ActiveMainMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as := by
  simpa [ActiveMainMemProviderRowMatchSpec] using
    exists_mem_provider_row_matches_entry_spec_of_active_main_eval
      witness h_balanced h_specs h_mainTable h_mainRow h_mainInteraction
      h_mainEval h_active (multiplicity := multiplicity) (as := as)


end ZiskFv.AirsClean.FullEnsemble
