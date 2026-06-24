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
      (mainInteraction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg))
            (ZiskFv.AirsClean.Main.aMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (mainTable.environment mainRow)
        ∨ mainInteraction =
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
            (mainTable.environment mainRow)
        ∨ mainInteraction =
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
            (mainTable.environment mainRow))
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
                    ∧
                    (providerInteraction =
                        ((MemBusChannel.emitted
                          (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.a_src_mem
                            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar.rom.a_src_reg))
                          (ZiskFv.AirsClean.Main.aMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow)
                      ∨ providerInteraction =
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
                      ∨ providerInteraction =
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
                          (providerTable.environment providerRow)))) := by
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
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main
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
    exact ⟨providerRow, h_providerRow, h_main, h_providerEval⟩

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
        (mainInteraction =
            ((MemBusChannel.emitted
              (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.a_src_mem
                + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar.rom.a_src_reg))
              (ZiskFv.AirsClean.Main.aMemMessageExpr
                (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                  length program).rowInputVar)).toRaw).eval
              (mainTable.environment mainRow)
          ∨ mainInteraction =
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
              (mainTable.environment mainRow)
          ∨ mainInteraction =
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
              (mainTable.environment mainRow))
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
                      ∧
                      (providerInteraction =
                          ((MemBusChannel.emitted
                            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.a_src_mem
                              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.rom.a_src_reg))
                            (ZiskFv.AirsClean.Main.aMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar)).toRaw).eval
                            (providerTable.environment providerRow)
                        ∨ providerInteraction =
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
                        ∨ providerInteraction =
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
                            (providerTable.environment providerRow)))) := by
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
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main
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
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_component, h_eval⟩

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
                    ∧
                    ((providerInteraction =
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
                          (eval (mainTable.environment mainRow) mainMsg)
                          multiplicity as)
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Main.aMemMessageExpr
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
                          (eval (mainTable.environment mainRow) mainMsg)
                          multiplicity as)
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Main.bMemMessageExpr
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
                          (eval (mainTable.environment mainRow) mainMsg)
                          multiplicity as)
                        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Main.cMemMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar))
                          multiplicity as))))) := by
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
  rcases h_providerComponent with h_marb | h_mab | h_memAlign | h_mem | h_main
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
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_main, ?_⟩
    rcases h_providerEval with h_a | h_b | h_c
    · left
      refine ⟨h_a, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_a, ← h_mainEval]
      exact h_msg
    · right
      left
      refine ⟨h_b, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_b, ← h_mainEval]
      exact h_msg
    · right
      right
      refine ⟨h_c, ?_⟩
      apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_emitted_provider_msg_eq
      rw [← h_c, ← h_mainEval]
      exact h_msg

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
                ∧
                ((providerInteraction =
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
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.aMemMessageExpr
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
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.bMemMessageExpr
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
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                        (eval (providerTable.environment providerRow)
                          (ZiskFv.AirsClean.Main.cMemMessageExpr
                            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                              length program).rowInputVar))
                      multiplicity as)))))

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
                ∧
                ((providerInteraction =
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
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.aMemMessageExpr
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
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.bMemMessageExpr
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
                      (eval (mainTable.environment mainRow) mainMsg)
                      multiplicity as)
                    (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Main.cMemMessageExpr
                          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                            length program).rowInputVar))
                      multiplicity as)))))

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
              ∧
              ((providerInteraction =
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
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.Main.aMemMessageExpr
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
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.Main.bMemMessageExpr
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
                    (eval (mainTable.environment mainRow) mainMsg)
                    multiplicity as)
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.Main.cMemMessageExpr
                        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                          length program).rowInputVar))
                    multiplicity as)))

/-- Main memory-bus interactions in the full ensemble are only active pulls
    or inactive zero-multiplicity rows.

    This is the missing source-legality invariant needed to rule out the
    Main self-provider branch for direct loads. It is deliberately stated as
    an explicit witness-level obligation: the current Main `Spec` only exposes
    core Main constraints, while the needed fact depends on ROM/source flag
    legality for every unified-Main row. -/
def MainMemBusMultiplicitySound
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    Prop :=
  ∀ table ∈ witness.allTables,
    table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program →
      ∀ interaction ∈ table.interactionsWith MemBusChannel.toRaw,
        interaction.mult = -1 ∨ interaction.mult = 0

/-- Row-local ROM/source selector legality needed to make unified-Main
    memory-bus multiplicities pull-or-zero.

    The sums are stated after table evaluation because this is the exact
    proof surface consumed by `MainMemBusMultiplicitySound`: Main emits the
    three memory-bus interactions with multiplicities `-aSum`, `-bSum`, and
    `-storeSum`. -/
def MainMemBusSourceMultiplicitySound
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    Prop :=
  ∀ table ∈ witness.allTables,
    table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program →
      ∀ row ∈ table.table,
        let env := table.environment row
        (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_reg) = 1
          ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.a_src_reg) = 0)
        ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_reg) = 1
          ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.b_src_reg) = 0)
        ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_reg) = 1
          ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.rom.store_reg) = 0)

/-- Concrete source selector legality for one unified-Main row. -/
def MainRomRowSourceMultiplicitySound
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL) : Prop :=
  (row.rom.a_src_mem + row.rom.a_src_reg = 1
    ∨ row.rom.a_src_mem + row.rom.a_src_reg = 0)
  ∧ (row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg = 1
    ∨ row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg = 0)
  ∧ (row.rom.store_mem + row.rom.store_ind + row.rom.store_reg = 1
    ∨ row.rom.store_mem + row.rom.store_ind + row.rom.store_reg = 0)

/-- Row-indexed source selector legality for every concrete program ROM row.

    This is closer to the production/provenance boundary than
    `MainProgramRomSourceMultiplicitySound`: for each `program i`, any concrete
    unified-Main row with that ROM message has source-selector sums `1` or `0`.
    The remaining extraction work should prove this from row-shape provenance /
    lowered instruction facts. -/
def MainProgramRomRowsSourceMultiplicitySound
    {length : ℕ} (program : Program length) : Prop :=
  ∀ i : Fin length,
    ∀ row : ZiskFv.AirsClean.Main.MainRowWithRom FGL,
      ZiskFv.AirsClean.Main.romMessage row = program i →
        MainRomRowSourceMultiplicitySound row

/-- Program-ROM source selector legality for unified-Main rows.

    This is the program-indexed source-legality burden exposed by the ROM
    lookup split: accepted row constraints prove that a unified-Main row's ROM
    message is in the program ROM, while this predicate says every such ROM row
    has the source-selector sums needed by the memory-bus proof. -/
def MainProgramRomSourceMultiplicitySound
    {length : ℕ} (program : Program length) : Prop :=
  ∀ env : Environment FGL,
    (ZiskFv.AirsClean.ZiskInstructionRom.romStaticTable length program).Spec
      (eval env
        (ZiskFv.AirsClean.Main.romMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)) →
      (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg) = 1
        ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg) = 0)
      ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg) = 1
        ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg) = 0)
      ∧ (env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg) = 1
        ∨ env ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg) = 0)

/-- Row-indexed program ROM source legality implies the env-shaped program-ROM
    source burden consumed by the full-ensemble split. -/
theorem mainProgramRomSourceMultiplicitySound_of_programRowsSourceMultiplicitySound
    {length : ℕ} {program : Program length}
    (h_rows : MainProgramRomRowsSourceMultiplicitySound program) :
    MainProgramRomSourceMultiplicitySound program := by
  intro env h_rom
  rcases h_rom with ⟨i, h_msg⟩
  let component := ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
  let row : ZiskFv.AirsClean.Main.MainRowWithRom FGL := component.rowInput env
  have h_eval_row : eval env component.rowInputVar = row := by
    simpa only [row, component, Air.Flat.Component.rowInput,
      Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env)
  have h_row_msg : ZiskFv.AirsClean.Main.romMessage row = program i := by
    have h_msg' :
        ZiskFv.AirsClean.Main.romMessage (eval env component.rowInputVar) =
          program i := by
      simpa only [component, ZiskFv.AirsClean.Main.eval_romMessageExpr] using h_msg
    simpa only [h_eval_row] using h_msg'
  have h_row_source := h_rows i row h_row_msg
  rcases h_row_source with ⟨h_a, h_b, h_c⟩
  have h_a_sum :
      env (component.rowInputVar.rom.a_src_mem
          + component.rowInputVar.rom.a_src_reg) =
        row.rom.a_src_mem + row.rom.a_src_reg := by
    calc
      env (component.rowInputVar.rom.a_src_mem
          + component.rowInputVar.rom.a_src_reg)
          = (eval env component.rowInputVar).rom.a_src_mem
              + (eval env component.rowInputVar).rom.a_src_reg := by
            exact ZiskFv.AirsClean.Main.eval_aSourceSumExpr env component.rowInputVar
      _ = row.rom.a_src_mem + row.rom.a_src_reg := by
            exact congrArg
              (fun r : ZiskFv.AirsClean.Main.MainRowWithRom FGL =>
                r.rom.a_src_mem + r.rom.a_src_reg) h_eval_row
  have h_b_sum :
      env (component.rowInputVar.rom.b_src_mem
          + component.rowInputVar.rom.b_src_ind
          + component.rowInputVar.rom.b_src_reg) =
        row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg := by
    calc
      env (component.rowInputVar.rom.b_src_mem
          + component.rowInputVar.rom.b_src_ind
          + component.rowInputVar.rom.b_src_reg)
          = (eval env component.rowInputVar).rom.b_src_mem
              + (eval env component.rowInputVar).rom.b_src_ind
              + (eval env component.rowInputVar).rom.b_src_reg := by
            exact ZiskFv.AirsClean.Main.eval_bSourceSumExpr env component.rowInputVar
      _ = row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg := by
            exact congrArg
              (fun r : ZiskFv.AirsClean.Main.MainRowWithRom FGL =>
                r.rom.b_src_mem + r.rom.b_src_ind + r.rom.b_src_reg) h_eval_row
  have h_c_sum :
      env (component.rowInputVar.rom.store_mem
          + component.rowInputVar.rom.store_ind
          + component.rowInputVar.rom.store_reg) =
        row.rom.store_mem + row.rom.store_ind + row.rom.store_reg := by
    calc
      env (component.rowInputVar.rom.store_mem
          + component.rowInputVar.rom.store_ind
          + component.rowInputVar.rom.store_reg)
          = (eval env component.rowInputVar).rom.store_mem
              + (eval env component.rowInputVar).rom.store_ind
              + (eval env component.rowInputVar).rom.store_reg := by
            exact ZiskFv.AirsClean.Main.eval_cSourceSumExpr env component.rowInputVar
      _ = row.rom.store_mem + row.rom.store_ind + row.rom.store_reg := by
            exact congrArg
              (fun r : ZiskFv.AirsClean.Main.MainRowWithRom FGL =>
                r.rom.store_mem + r.rom.store_ind + r.rom.store_reg) h_eval_row
  exact ⟨ by simpa only [component, h_a_sum] using h_a
        , by simpa only [component, h_b_sum] using h_b
        , by simpa only [component, h_c_sum] using h_c ⟩

/-- Accepted row constraints plus program-ROM source legality discharge the
    row-local unified-Main source-multiplicity invariant. -/
theorem mainMemBusSourceMultiplicitySound_of_constraints_and_programRomSourceMultiplicitySound
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_constraints : witness.Constraints)
    (h_program : MainProgramRomSourceMultiplicitySound program) :
    MainMemBusSourceMultiplicitySound program witness := by
  intro table h_table h_component row h_row
  have h_row_constraints :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).operations.ConstraintsHold (table.environment row) := by
    simpa [h_component] using h_constraints table h_table row h_row
  exact h_program (table.environment row)
    (ZiskFv.AirsClean.Main.romSpec_of_componentWithRomMemAndOpBus_constraints
      length program (table.environment row) h_row_constraints)

/-- Source selector legality discharges the coarser unified-Main memory-bus
    multiplicity invariant used to rule out Main self-provider routes. -/
theorem mainMemBusMultiplicitySound_of_sourceMultiplicitySound
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_source : MainMemBusSourceMultiplicitySound program witness) :
    MainMemBusMultiplicitySound program witness := by
  intro table h_table h_component interaction h_interaction
  obtain ⟨row, h_row, h_eval⟩ :=
    exists_main_mem_row_eval_of_interaction_mem h_component h_interaction
  have h_row_source := h_source table h_table h_component row h_row
  dsimp only at h_row_source
  rcases h_row_source with ⟨h_a, h_b, h_store⟩
  rcases h_eval with h_eval | h_eval | h_eval
  · rcases h_a with h_one | h_zero
    · left
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg) = -1
      rw [h_one]
      ring
    · right
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg) = 0
      rw [h_zero]
      ring
  · rcases h_b with h_one | h_zero
    · left
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg) = -1
      rw [h_one]
      ring
    · right
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.b_src_reg) = 0
      rw [h_zero]
      ring
  · rcases h_store with h_one | h_zero
    · left
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg) = -1
      rw [h_one]
      ring
    · right
      rw [h_eval]
      change
        (-1 : FGL) * Expression.eval (table.environment row)
          ((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_mem
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_ind
            + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.store_reg) = 0
      rw [h_zero]
      ring

/-- Main self-provider memory routes are impossible once unified-Main
    memory-bus multiplicities are known to be pull-or-zero only. -/
theorem no_activeMainSelfMemProviderRowMatchSpec_of_mainMemBusMultiplicitySound
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainMem : MainMemBusMultiplicitySound program witness) :
    ¬ ActiveMainSelfMemProviderRowMatchSpec program witness mainTable mainRow
      mainInteraction mainMsg multiplicity as := by
  intro h_self
  rcases h_self with
    ⟨providerInteraction, _h_provider_witness, _h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      providerRow, _h_providerRow, _h_providerSpec, h_component, _h_branch⟩
  have h_mult :=
    h_mainMem providerTable h_providerTable h_component providerInteraction
      h_providerInteraction
  rcases h_mult with h_pull | h_zero
  · exact h_nonpull h_pull
  · exact h_nonzero h_zero

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
        mainRow mainInteraction mainMsg multiplicity as := by
  rcases h_nonmutable with
    ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_branch⟩
  rcases h_branch with h_marb | h_mab | h_memAlign | h_main
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
  · right; right; right
    exact ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      h_main⟩

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
        mainTable mainRow mainInteraction mainMsg multiplicity as) :
    ¬ ActiveMainNonMutableMemProviderRowMatchSpec program witness mainTable
      mainRow mainInteraction mainMsg multiplicity as := by
  intro h_nonmutable
  rcases activeMainNonMutableMemProviderRowMatchSpec_branch_cases
      h_nonmutable with h_marb | h_mab | h_memAlign | h_main
  · exact h_no_marb h_marb
  · exact h_no_mab h_mab
  · exact h_no_memAlign h_memAlign
  · exact h_no_main h_main

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
  rcases h_branch with h_marb | h_mab | h_memAlign | h_mem | h_main
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
      Or.inr (Or.inr (Or.inr h_main))⟩

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
