import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.Airs.MemoryBus.MemAlignBridge
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
import ZiskFv.AirsClean.FullEnsemble.Balance.MemAlignSkippableProve

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-! ## Full-ensemble memory-bus row bridges -/

/-- Project `mem_op` equality out of an evaluated Clean memory-bus message
    equality. The raw interaction stores messages as arrays; this restores the
    typed `MemBusMessage` view for the opcode slot. -/
theorem memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
    {mainMsg providerMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {mainMult providerMult : Expression FGL}
    {mainEnv providerEnv : Environment FGL}
    (h_msg :
      (((MemBusChannel.emitted providerMult providerMsg).toRaw).eval
          providerEnv).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          mainEnv).msg) :
    (eval providerEnv providerMsg).mem_op = (eval mainEnv mainMsg).mem_op := by
  have h_vec :
      Vector.map (Expression.eval providerEnv) (toElements providerMsg) =
        Vector.map (Expression.eval mainEnv) (toElements mainMsg) := by
    apply Vector.toArray_injective
    simpa [ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_eval : eval providerEnv providerMsg = eval mainEnv mainMsg := by
    have h_from := congrArg
      (fun xs => (fromElements xs :
        ZiskFv.Channels.MemoryBus.MemBusMessage FGL)) h_vec
    simpa [ProvableType.fromElements_eval_toElements] using h_from
  exact congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.mem_op h_eval

/-- Project `mem_op` equality out of a pushed-provider memory-bus message
    equality. This is the `MemAlignByte` / `MemAlignReadByte` analogue of
    `memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq`. -/
theorem memBusMessage_mem_op_eq_of_eval_pushed_provider_msg_eq
    {mainMsg providerMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {mainMult : Expression FGL}
    {mainEnv providerEnv : Environment FGL}
    (h_msg :
      (((MemBusChannel.pushed providerMsg).toRaw).eval providerEnv).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval mainEnv).msg) :
    (eval providerEnv providerMsg).mem_op = (eval mainEnv mainMsg).mem_op := by
  have h_vec :
      Vector.map (Expression.eval providerEnv) (toElements providerMsg) =
        Vector.map (Expression.eval mainEnv) (toElements mainMsg) := by
    apply Vector.toArray_injective
    simpa [ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_eval : eval providerEnv providerMsg = eval mainEnv mainMsg := by
    have h_from := congrArg
      (fun xs => (fromElements xs :
        ZiskFv.Channels.MemoryBus.MemBusMessage FGL)) h_vec
    simpa [ProvableType.fromElements_eval_toElements] using h_from
  exact congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.mem_op h_eval

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
    `exists_matching_mem_component_of_active_main_interaction`; load-specific
    wrappers below discharge the Main self-matches from accepted row
    constraints and the Main-side `mem_op = 1` fact. -/
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
        h_marb h_providerInteraction h_nonpull
    left
    exact ⟨providerRow, h_providerRow, h_marb, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem h_mab h_providerInteraction h_nonpull
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
        h_marb h_providerInteraction h_nonpull
    left
    refine ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_marb, h_providerEval, ?_⟩
    apply ZiskFv.Airs.MemoryBus.matches_memory_entry_of_eval_pushed_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_memAlignByte_row_eval_of_interaction_mem h_mab h_providerInteraction h_nonpull
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

/-- Active mutable-Mem provider coverage places a concrete Main-side load
    entry in the accepted chronological row trace.

Compared with
`activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded`,
this theorem derives the primary `wr = 0` polarity fact from the full Clean
PIL message equality and a Main-side `mem_op = 1` hypothesis. The remaining
input is the active mutable-Mem replay embedding. -/
theorem activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded_of_main_mem_op_one
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_mutable :
      ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg (-1) 2)
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) (-1) 2))
    (h_embedded :
      MutableActiveMemReplayRowsEmbeddedInTrace witness rows) :
    entry ∈ rows := by
  rcases h_mutable with
    ⟨providerInteraction, _h_providerInteraction_mem, h_msg, _h_provider_non_pull,
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
    have h_raw_msg :
        (((MemBusChannel.emitted component.rowInputVar.sel
            (ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)).toRaw).eval
            providerEnv).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_eval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval providerEnv
          (ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)).mem_op =
            (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
        (mainMsg := mainMsg)
        (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)
        (mainMult := mainMult)
        (providerMult := component.rowInputVar.sel)
        (mainEnv := mainTable.environment mainRow)
        (providerEnv := providerEnv)
        h_raw_msg
    have h_wr_add_one :
        (eval providerEnv component.rowInputVar).wr + 1 = 1 := by
      calc
        (eval providerEnv component.rowInputVar).wr + 1 =
            (eval providerEnv
              (ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)).mem_op := by
              simp [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr,
                ZiskFv.AirsClean.Mem.memBusMessage]
        _ = (eval (mainTable.environment mainRow) mainMsg).mem_op := h_provider_mem_op
        _ = 1 := h_main_mem_op
    have h_wr :
        (eval providerEnv component.rowInputVar).wr = 0 := by
      have h_sub := congrArg (fun x => x - 1) h_wr_add_one
      simpa using h_sub
    exact mem_primary_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
      (h_embedded providerTable h_providerTable_mem h_providerComponent)
      h_providerRow_mem (by simpa [component, providerEnv] using h_sel)
      (by simpa [component, providerEnv] using h_wr)
      (by simpa [providerEnv] using h_match)
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
    exact mem_dual_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
      (h_embedded providerTable h_providerTable_mem h_providerComponent)
      h_providerRow_mem
      (by simpa [component, providerEnv] using h_sel_dual)
      (by simpa [providerEnv] using h_match)

/-- Active mutable-Mem provider coverage places a concrete Main-side store
    entry in the accepted chronological row trace.

The primary Mem `wr = 1` fact is derived from the Clean message equality and a
Main-side `mem_op = 2` hypothesis. The dual branch is impossible for stores:
dual Mem emissions are read-shaped (`mem_op = 1`). -/
theorem activeMainMutableMemProviderRowMatchSpec_entry_mem_of_active_replay_embedded_of_main_mem_op_two
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {entry : Interaction.MemoryBusEntry FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_mutable :
      ActiveMainMutableMemProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg 1 2)
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 2)
    (h_entry :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) 1 2))
    (h_embedded :
      MutableActiveMemReplayRowsEmbeddedInTrace witness rows) :
    entry ∈ rows := by
  rcases h_mutable with
    ⟨providerInteraction, _h_providerInteraction_mem, h_msg, _h_provider_non_pull,
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
    have h_raw_msg :
        (((MemBusChannel.emitted component.rowInputVar.sel
            (ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)).toRaw).eval
            providerEnv).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_eval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval providerEnv
          (ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)).mem_op =
            (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
        (mainMsg := mainMsg)
        (providerMsg := ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)
        (mainMult := mainMult)
        (providerMult := component.rowInputVar.sel)
        (mainEnv := mainTable.environment mainRow)
        (providerEnv := providerEnv)
        h_raw_msg
    have h_wr_add_one :
        (eval providerEnv component.rowInputVar).wr + 1 = 2 := by
      calc
        (eval providerEnv component.rowInputVar).wr + 1 =
            (eval providerEnv
              (ZiskFv.AirsClean.Mem.memBusMessageExpr component.rowInputVar)).mem_op := by
              simp [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr,
                ZiskFv.AirsClean.Mem.memBusMessage]
        _ = (eval (mainTable.environment mainRow) mainMsg).mem_op := h_provider_mem_op
        _ = 2 := h_main_mem_op
    have h_wr :
        (eval providerEnv component.rowInputVar).wr = 1 := by
      have h_sub := congrArg (fun x => x - 1) h_wr_add_one
      simpa using h_sub
    have h_match :
        ZiskFv.Airs.MemoryBus.matches_memory_entry entry
          (memPrimaryReplayEntryOfRow
            (eval providerEnv
              ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) := by
      have h_trans :=
        ZiskFv.Airs.MemoryBus.matches_memory_entry_trans h_entry h_provider_match
      simpa [providerEnv, component, memPrimaryReplayEntryOfRow,
        ZiskFv.AirsClean.Mem.eval_memBusMessageExpr, h_wr] using h_trans
    exact mem_primary_replay_entry_mem_of_active_replay_embedded_trace_row_match
      (h_embedded providerTable h_providerTable_mem h_providerComponent)
      h_providerRow_mem (by simpa [component, providerEnv] using h_sel)
      (by simpa [providerEnv, h_wr] using h_match)
  · rcases h_dual with ⟨h_eval, _h_provider_match⟩
    have h_raw_msg :
        (((MemBusChannel.emitted component.rowInputVar.sel_dual
            (ZiskFv.AirsClean.Mem.memBusDualMessageExpr component.rowInputVar)).toRaw).eval
            providerEnv).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_eval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval providerEnv
          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr component.rowInputVar)).mem_op =
            (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
        (mainMsg := mainMsg)
        (providerMsg := ZiskFv.AirsClean.Mem.memBusDualMessageExpr component.rowInputVar)
        (mainMult := mainMult)
        (providerMult := component.rowInputVar.sel_dual)
        (mainEnv := mainTable.environment mainRow)
        (providerEnv := providerEnv)
        h_raw_msg
    have h_bad := h_provider_mem_op
    simp [providerEnv, component, ZiskFv.AirsClean.Mem.eval_memBusDualMessageExpr,
      ZiskFv.AirsClean.Mem.memBusDualMessage, h_main_mem_op] at h_bad

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

/-- Structural load-provider row selected from a MemAlignReadByte branch. -/
def MemAlignReadByteLoadProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∃ providerTable ∈ witness.allTables,
    ∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component = ZiskFv.AirsClean.MemAlignReadByte.component
        ∧ ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_read_byte_row_matches_load_entry
          (ZiskFv.AirsClean.MemAlignReadByte.validOfRow
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
          0 entry

/-- Structural load-provider row selected from a MemAlignByte branch. -/
def MemAlignByteLoadProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∃ providerTable ∈ witness.allTables,
    ∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component = ZiskFv.AirsClean.MemAlignByte.component
        ∧ ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_byte_row_matches_load_entry
          (ZiskFv.AirsClean.MemAlignByte.validOfRow
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
          0 entry

/-- Structural load-provider row selected from a general MemAlign branch.

This predicate records the prove-side load branch only. The ROM/value facts
needed by `SubdoublewordLoadProviderWitness` remain separate because they are
not row-local consequences of memory-bus balance. -/
def MemAlignLoadProviderRowMatchSpec
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∃ providerTable ∈ witness.allTables,
    ∃ providerRow ∈ providerTable.table,
      providerTable.component.Spec (providerTable.environment providerRow)
        ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
        ∧ ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_row_matches_load_entry
          (ZiskFv.AirsClean.MemAlign.validOfRow
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.MemAlign.component.rowInputVar))
          0 entry

/-- A structural MemAlignReadByte load-provider row supplies the corresponding
    branch of the legacy subdoubleword provider witness, once the Main row's
    load width is pinned to one byte.

The selected row's byte range comes directly from the Clean component `Spec`:
that is the source-faithful static-lookup conclusion carried by the accepted
table, not a whole-table validator premise. -/
set_option maxHeartbeats 1000000 in
theorem exists_subdoublewordLoadProviderWitness_of_memAlignReadByteLoadProviderRowMatchSpec
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    {mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL}
    {ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL}
    {r_main : ℕ} {entry : Interaction.MemoryBusEntry FGL}
    (h_width : main.ind_width r_main = 1)
    (h_provider : MemAlignReadByteLoadProviderRowMatchSpec program witness entry) :
    ∃ marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL,
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        main mab marb ma r_main entry := by
  rcases h_provider with
    ⟨providerTable, _h_providerTable, providerRow, _h_providerRow,
      h_spec, h_component, h_match⟩
  have h_row_spec : ZiskFv.AirsClean.MemAlignReadByte.Spec
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar) := by
    rw [h_component] at h_spec
    simpa only [ZiskFv.AirsClean.MemAlignReadByte.component_spec] using h_spec
  refine ⟨
    ZiskFv.AirsClean.MemAlignReadByte.validOfRow
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar),
    ?_⟩
  exact
    { provider := Or.inr (Or.inl ⟨0, h_match, h_width, h_row_spec.2⟩) }

/-- A structural MemAlignByte load-provider row supplies the corresponding
    branch of the legacy subdoubleword provider witness, once the Main row's
    load width is pinned to one byte.

As above, the selected row's range is derived from the table's in-circuit
static lookup through its Clean component `Spec`. -/
set_option maxHeartbeats 1000000 in
theorem exists_subdoublewordLoadProviderWitness_of_memAlignByteLoadProviderRowMatchSpec
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    {marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL}
    {ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL}
    {r_main : ℕ} {entry : Interaction.MemoryBusEntry FGL}
    (h_width : main.ind_width r_main = 1)
    (h_provider : MemAlignByteLoadProviderRowMatchSpec program witness entry) :
    ∃ mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL,
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        main mab marb ma r_main entry := by
  rcases h_provider with
    ⟨providerTable, _h_providerTable, providerRow, _h_providerRow,
      h_spec, h_component, h_match⟩
  have h_row_spec : ZiskFv.AirsClean.MemAlignByte.Spec
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar) := by
    rw [h_component] at h_spec
    simpa only [ZiskFv.AirsClean.MemAlignByte.component_spec] using h_spec
  refine ⟨
    ZiskFv.AirsClean.MemAlignByte.validOfRow
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar),
    ?_⟩
  exact
    { provider := Or.inl ⟨0, h_match, h_width, h_row_spec.2.2.2.2.2.1⟩ }

/-- ROM/range residue for the selected general MemAlign load-provider row.

The row-local memory-bus match gives the provider row and the payload equality,
but the legacy subdoubleword witness also needs the MemAlignRom-mediated width
and low-value range facts. The high-value-zero fact is deliberately absent: it
is a ZisK v0.17.0 defect boundary, discharged only from the trace-level
narrow-load exclusion in `Compliance.Defects`. -/
def MemAlignLoadProviderRomValueFacts
    {length : ℕ} (program : Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∀ providerTable providerRow,
    providerTable ∈ witness.allTables →
    providerRow ∈ providerTable.table →
    providerTable.component.Spec (providerTable.environment providerRow) →
    providerTable.component = ZiskFv.AirsClean.MemAlign.component →
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_row_matches_load_entry
      (ZiskFv.AirsClean.MemAlign.validOfRow
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar))
      0 entry →
    let ma :=
      ZiskFv.AirsClean.MemAlign.validOfRow
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)
    ma.width 0 = main.ind_width r_main
      ∧ (ma.width 0 = 1 → (ma.value_0 0).val < 256)
      ∧ (ma.width 0 = 2 → (ma.value_0 0).val < 65536)

/-- A structural general-MemAlign load-provider row supplies the corresponding
    branch of the legacy subdoubleword provider witness once the explicit
    ROM/range residue and its separately discharged high-lane equality are
    available. -/
theorem exists_subdoublewordLoadProviderWitness_of_memAlignLoadProviderRowMatchSpec
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {main : ZiskFv.Airs.Main.Valid_Main FGL FGL}
    {mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL}
    {marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL}
    {r_main : ℕ} {entry : Interaction.MemoryBusEntry FGL}
    (h_rom :
      MemAlignLoadProviderRomValueFacts program witness main r_main entry)
    (h_value_1_zero : ∀ providerTable providerRow,
      providerTable ∈ witness.allTables →
      providerRow ∈ providerTable.table →
      providerTable.component.Spec (providerTable.environment providerRow) →
      providerTable.component = ZiskFv.AirsClean.MemAlign.component →
      ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_row_matches_load_entry
        (ZiskFv.AirsClean.MemAlign.validOfRow
          (eval (providerTable.environment providerRow)
            ZiskFv.AirsClean.MemAlign.component.rowInputVar))
        0 entry →
      (ZiskFv.AirsClean.MemAlign.validOfRow
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).value_1 0 = 0)
    (h_provider : MemAlignLoadProviderRowMatchSpec program witness entry) :
    ∃ ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL,
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        main mab marb ma r_main entry := by
  rcases h_provider with
    ⟨providerTable, h_providerTable, providerRow, h_providerRow,
      h_spec, h_component, h_match⟩
  let ma :=
    ZiskFv.AirsClean.MemAlign.validOfRow
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlign.component.rowInputVar)
  obtain ⟨h_width, h_v0_lt_1, h_v0_lt_2⟩ :=
    h_rom providerTable providerRow h_providerTable h_providerRow h_spec h_component h_match
  have h_value_1_zero :=
    h_value_1_zero providerTable providerRow h_providerTable h_providerRow h_spec h_component h_match
  refine ⟨ma, ?_⟩
  exact
    { provider := Or.inr (Or.inr
        ⟨0, h_match, h_width, h_value_1_zero, h_v0_lt_1, h_v0_lt_2⟩) }

/-- Follow an active Main -> MemAlignReadByte provider branch to the concrete
    structural load-row predicate consumed by the subdoubleword MemAlign bridge. -/
theorem memAlignReadByteLoadProviderRowMatchSpec_of_activeMain_branch
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL} {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_as : as = 2)
    (h_branch :
      ActiveMainMemAlignReadByteProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as) :
    MemAlignReadByteLoadProviderRowMatchSpec program witness
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (mainTable.environment mainRow) mainMsg) multiplicity as) := by
  subst as
  rcases h_branch with
    ⟨_providerInteraction, _h_provider_mem, _h_msg, _h_mult_not_read, _h_mult_not_zero,
      providerTable, h_providerTable, _h_provider_table_mem,
      providerRow, h_providerRow, h_spec, h_component, _h_provider_eval, h_entry⟩
  refine ⟨providerTable, h_providerTable, providerRow, h_providerRow, h_spec, h_component, ?_⟩
  have h_entry' :
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) multiplicity 2)
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessage
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
          multiplicity 2) := by
    simpa [ZiskFv.AirsClean.MemAlignReadByte.eval_memBusMessageExpr] using h_entry
  exact
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_read_byte_row_matches_load_entry_of_message_match_valid_with_multiplicity
        (ZiskFv.AirsClean.MemAlignReadByte.validOfRow
          (eval (providerTable.environment providerRow)
            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar))
        0
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) multiplicity 2)
        multiplicity rfl h_entry'

/-- Follow an active Main -> MemAlignByte provider branch to the concrete
    structural load-row predicate consumed by the subdoubleword MemAlign bridge.
    The load-side `mem_op = 1` fact pins `is_write = 0`. -/
theorem memAlignByteLoadProviderRowMatchSpec_of_activeMain_branch
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL} {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {mainMult : Expression FGL}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op : (eval (mainTable.environment mainRow) mainMsg).mem_op = 1)
    (h_as : as = 2)
    (h_branch :
      ActiveMainMemAlignByteProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as) :
    MemAlignByteLoadProviderRowMatchSpec program witness
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (mainTable.environment mainRow) mainMsg) multiplicity as) := by
  subst as
  rcases h_branch with
    ⟨providerInteraction, _h_provider_mem, h_msg, _h_mult_not_read, _h_mult_not_zero,
      providerTable, h_providerTable, _h_provider_table_mem,
      providerRow, h_providerRow, h_spec, h_component, h_provider_eval, h_entry⟩
  refine ⟨providerTable, h_providerTable, providerRow, h_providerRow, h_spec, h_component, ?_⟩
  have h_raw :
      (((MemBusChannel.pushed
        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_provider_eval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op_one :
      (eval (providerTable.environment providerRow)
        (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).mem_op = 1 := by
    exact (memBusMessage_mem_op_eq_of_eval_pushed_provider_msg_eq (h_msg := h_raw)).trans
      h_main_mem_op
  have h_provider_mem_op_one' :
      (ZiskFv.AirsClean.MemAlignByte.memBusMessage
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).mem_op = 1 := by
    rw [ZiskFv.AirsClean.MemAlignByte.eval_memBusMessageExpr] at h_provider_mem_op_one
    exact h_provider_mem_op_one
  have h_is_write_eq :
      1 + (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar).is_write = 1 := by
    simpa [ZiskFv.AirsClean.MemAlignByte.memBusMessage] using h_provider_mem_op_one'
  have h_is_write :
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlignByte.component.rowInputVar).is_write = 0 := by
    linear_combination h_is_write_eq
  have h_entry' :
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) multiplicity 2)
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.MemAlignByte.memBusMessage
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
          multiplicity 2) := by
    simpa [ZiskFv.AirsClean.MemAlignByte.eval_memBusMessageExpr] using h_entry
  exact
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_byte_row_matches_load_entry_of_message_match_valid_with_multiplicity
        (ZiskFv.AirsClean.MemAlignByte.validOfRow
          (eval (providerTable.environment providerRow)
            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar))
        0
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) multiplicity 2)
        multiplicity rfl (by simpa [ZiskFv.AirsClean.MemAlignByte.validOfRow] using h_is_write)
        h_entry'

/-- Follow an active Main -> general MemAlign provider branch to the concrete
    structural load-row predicate consumed by the subdoubleword MemAlign bridge.

The load-side `mem_op = 1` fact pins `wr = 0`. The prove-branch selector facts
are supplied by the trace-local #1142 exclusion, not by a caller premise:
balance and row-local MemAlign `Spec` alone do not select the prove branch. -/
theorem memAlignLoadProviderRowMatchSpec_of_activeMain_branch
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL} {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {mainMult : Expression FGL}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op : (eval (mainTable.environment mainRow) mainMsg).mem_op = 1)
    (h_as : as = 2)
    (h_branch :
      ActiveMainMemAlignProviderRowMatchSpec program witness mainTable mainRow
        mainInteraction mainMsg multiplicity as)
    (h_not_skippable_prove :
      ¬ MemAlignSkippableProveForge program witness
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) multiplicity as)) :
    MemAlignLoadProviderRowMatchSpec program witness
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (mainTable.environment mainRow) mainMsg) multiplicity as) := by
  subst as
  rcases h_branch with
    ⟨providerInteraction, h_provider_mem, h_msg, h_mult_not_read, h_mult_not_zero,
      providerTable, h_providerTable, h_provider_table_mem,
      providerRow, h_providerRow, h_spec, h_component, h_provider_eval, h_entry⟩
  refine ⟨providerTable, h_providerTable, providerRow, h_providerRow, h_spec, h_component, ?_⟩
  obtain ⟨h_sel_prove, h_sel_up_to_down, h_sel_down_to_up⟩ :=
    memAlign_selected_prove_pins_of_not_skippable_prove_forge
      h_not_skippable_prove h_provider_mem h_mult_not_read h_mult_not_zero h_providerTable
      h_provider_table_mem h_providerRow h_spec h_component h_provider_eval h_entry
  have h_raw :
      (((MemBusChannel.emitted
        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_provider_eval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op_one :
      (eval (providerTable.environment providerRow)
        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).mem_op = 1 := by
    exact (memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)).trans
      h_main_mem_op
  have h_provider_mem_op_one' :
      (ZiskFv.AirsClean.MemAlign.memBusMessage
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).mem_op = 1 := by
    rw [ZiskFv.AirsClean.MemAlign.eval_memBusMessageExpr] at h_provider_mem_op_one
    exact h_provider_mem_op_one
  have h_wr_eq :
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlign.component.rowInputVar).wr + 1 = 1 := by
    simpa [ZiskFv.AirsClean.MemAlign.memBusMessage] using h_provider_mem_op_one'
  have h_wr :
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlign.component.rowInputVar).wr = 0 := by
    linear_combination h_wr_eq
  have h_entry' :
      ZiskFv.Airs.MemoryBus.matches_memory_entry
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (eval (mainTable.environment mainRow) mainMsg) multiplicity 2)
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.MemAlign.memBusMessage
            (eval (providerTable.environment providerRow)
              ZiskFv.AirsClean.MemAlign.component.rowInputVar))
          multiplicity 2) := by
    simpa [ZiskFv.AirsClean.MemAlign.eval_memBusMessageExpr] using h_entry
  exact
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_row_matches_load_entry_of_message_match_valid_with_multiplicity
      (ZiskFv.AirsClean.MemAlign.validOfRow
        (eval (providerTable.environment providerRow)
          ZiskFv.AirsClean.MemAlign.component.rowInputVar))
      0
      (eval (providerTable.environment providerRow)
        ZiskFv.AirsClean.MemAlign.component.rowInputVar)
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (eval (mainTable.environment mainRow) mainMsg) multiplicity 2)
      multiplicity rfl
      (by simpa [ZiskFv.AirsClean.MemAlign.validOfRow] using
        h_sel_prove)
      (by simpa [ZiskFv.AirsClean.MemAlign.validOfRow] using
        h_sel_up_to_down)
      (by simpa [ZiskFv.AirsClean.MemAlign.validOfRow] using
        h_sel_down_to_up)
      (by simpa [ZiskFv.AirsClean.MemAlign.validOfRow] using h_wr)
      h_entry'

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

/-- Main self-provider a-current memory branch of
    `ActiveMainSelfMemProviderRowMatchSpec`. -/
def ActiveMainSelfAMemProviderRowMatchSpec
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
              ∧ providerInteraction =
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
                  (eval (mainTable.environment mainRow) mainMsg) multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.Main.aMemMessageExpr
                      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar))
                  multiplicity as)

/-- Main self-provider b-current memory branch of
    `ActiveMainSelfMemProviderRowMatchSpec`. -/
def ActiveMainSelfBMemProviderRowMatchSpec
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
              ∧ providerInteraction =
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
                  (eval (mainTable.environment mainRow) mainMsg) multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.Main.bMemMessageExpr
                      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar))
                  multiplicity as)

/-- Main self-provider c-current memory branch of
    `ActiveMainSelfMemProviderRowMatchSpec`. -/
def ActiveMainSelfCMemProviderRowMatchSpec
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
              ∧ providerInteraction =
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
                  (eval (mainTable.environment mainRow) mainMsg) multiplicity as)
                (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                  (eval (providerTable.environment providerRow)
                    (ZiskFv.AirsClean.Main.cMemMessageExpr
                      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                        length program).rowInputVar))
                  multiplicity as)

private lemma bool_of_booleanity {col : FGL} (h : col * (1 - col) = 0) :
    ∃ d : Bool, col = ZiskFv.AirsClean.boolF d := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨false, by simpa [ZiskFv.AirsClean.boolF] using h0⟩
  · have h' : col - 1 = 0 := by
      have hneg := congrArg Neg.neg h1
      simpa [sub_eq_add_neg] using hneg
    exact ⟨true, by simpa [ZiskFv.AirsClean.boolF] using eq_of_sub_eq_zero h'⟩

private lemma main_mem_selector_booleanities_of_component_constraints
    {length : ℕ} {program : Program length} {env : Environment FGL}
    (h_constraints :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).operations.ConstraintsHold env) :
    let row := eval env
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar
    row.rom.a_src_mem * (1 - row.rom.a_src_mem) = 0
  ∧ row.rom.a_src_reg * (1 - row.rom.a_src_reg) = 0
  ∧ row.rom.b_src_mem * (1 - row.rom.b_src_mem) = 0
  ∧ row.rom.b_src_ind * (1 - row.rom.b_src_ind) = 0
  ∧ row.rom.b_src_reg * (1 - row.rom.b_src_reg) = 0
  ∧ row.rom.store_mem * (1 - row.rom.store_mem) = 0
  ∧ row.rom.store_ind * (1 - row.rom.store_ind) = 0
  ∧ row.rom.store_reg * (1 - row.rom.store_reg) = 0 := by
  intro row
  obtain ⟨_, _, _, _, h_a_src_mem, _, _, h_b_src_mem, h_store_mem,
    h_store_ind, h_b_src_ind, h_a_src_reg, h_b_src_reg, h_store_reg⟩ :=
    ZiskFv.AirsClean.Main.romBoolSpec_of_componentWithRomMemAndOpBus_constraints
      length program env h_constraints
  obtain ⟨_, _, _, _, _, b_a_src_mem, _, _, b_b_src_mem, b_store_mem,
    b_store_ind, b_b_src_ind, b_a_src_reg, b_b_src_reg, b_store_reg⟩ :=
    ZiskFv.AirsClean.Main.eval_flagBool_bridge env
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar
  exact ⟨b_a_src_mem ▸ h_a_src_mem, b_a_src_reg ▸ h_a_src_reg,
    b_b_src_mem ▸ h_b_src_mem, b_b_src_ind ▸ h_b_src_ind,
    b_b_src_reg ▸ h_b_src_reg, b_store_mem ▸ h_store_mem,
    b_store_ind ▸ h_store_ind, b_store_reg ▸ h_store_reg⟩

private lemma main_a_mem_current_mult_neg_one_of_mem_op_one
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_a_mem : row.rom.a_src_mem * (1 - row.rom.a_src_mem) = 0)
    (h_a_reg : row.rom.a_src_reg * (1 - row.rom.a_src_reg) = 0)
    (h_op : (ZiskFv.AirsClean.Main.aMemMessage row).mem_op = 1) :
    -(row.rom.a_src_mem + row.rom.a_src_reg) = (-1 : FGL) := by
  obtain ⟨d_mem, h_mem⟩ := bool_of_booleanity h_a_mem
  obtain ⟨d_reg, h_reg⟩ := bool_of_booleanity h_a_reg
  cases d_mem <;> cases d_reg <;>
    simp [ZiskFv.AirsClean.boolF, h_mem, h_reg] at h_op ⊢

private lemma main_b_mem_current_mult_neg_one_of_mem_op_one
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_b_mem : row.rom.b_src_mem * (1 - row.rom.b_src_mem) = 0)
    (h_b_ind : row.rom.b_src_ind * (1 - row.rom.b_src_ind) = 0)
    (h_b_reg : row.rom.b_src_reg * (1 - row.rom.b_src_reg) = 0)
    (h_op : (ZiskFv.AirsClean.Main.bMemMessage row).mem_op = 1) :
    -(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg) = (-1 : FGL) := by
  obtain ⟨d_mem, h_mem⟩ := bool_of_booleanity h_b_mem
  obtain ⟨d_ind, h_ind⟩ := bool_of_booleanity h_b_ind
  obtain ⟨d_reg, h_reg⟩ := bool_of_booleanity h_b_reg
  cases d_mem <;> cases d_ind <;> cases d_reg <;>
    simp [ZiskFv.AirsClean.boolF, h_mem, h_ind, h_reg] at h_op ⊢

private lemma false_of_main_c_mem_op_one
    (row : ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_store_mem : row.rom.store_mem * (1 - row.rom.store_mem) = 0)
    (h_store_ind : row.rom.store_ind * (1 - row.rom.store_ind) = 0)
    (h_store_reg : row.rom.store_reg * (1 - row.rom.store_reg) = 0)
    (h_op : (ZiskFv.AirsClean.Main.cMemMessage row).mem_op = 1) :
    False := by
  obtain ⟨d_mem, h_mem⟩ := bool_of_booleanity h_store_mem
  obtain ⟨d_ind, h_ind⟩ := bool_of_booleanity h_store_ind
  obtain ⟨d_reg, h_reg⟩ := bool_of_booleanity h_store_reg
  cases d_mem <;> cases d_ind <;> cases d_reg <;>
    simp [ZiskFv.AirsClean.boolF, h_mem, h_ind, h_reg] at h_op

private lemma main_a_mem_current_eval_mult_eq_neg_one
    (env : Environment FGL) (row : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_mult :
      -((eval env row).rom.a_src_mem + (eval env row).rom.a_src_reg) = (-1 : FGL)) :
    (((MemBusChannel.emitted
      (-(row.rom.a_src_mem + row.rom.a_src_reg))
      (ZiskFv.AirsClean.Main.aMemMessageExpr row)).toRaw).eval env).mult = -1 := by
  change env (-(row.rom.a_src_mem + row.rom.a_src_reg)) = -1
  have h_bridge :
      env (-(row.rom.a_src_mem + row.rom.a_src_reg)) =
        -((eval env row).rom.a_src_mem + (eval env row).rom.a_src_reg) := by
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field, Expression.eval]
    ring
  rw [h_bridge]
  exact h_mult

private lemma main_b_mem_current_eval_mult_eq_neg_one
    (env : Environment FGL) (row : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL)
    (h_mult :
      -((eval env row).rom.b_src_mem + (eval env row).rom.b_src_ind
        + (eval env row).rom.b_src_reg) = (-1 : FGL)) :
    (((MemBusChannel.emitted
      (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
      (ZiskFv.AirsClean.Main.bMemMessageExpr row)).toRaw).eval env).mult = -1 := by
  change env (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg)) = -1
  have h_bridge :
      env (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg)) =
        -((eval env row).rom.b_src_mem + (eval env row).rom.b_src_ind
          + (eval env row).rom.b_src_reg) := by
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go,
      ProvableType.eval_field, Expression.eval]
    ring
  rw [h_bridge]
  exact h_mult

/-- A Main-side load message (`mem_op = 1`) cannot be matched by the
    current-access Main self-provider `a` branch. Booleanity of the provider
    row's ROM selectors makes that branch's multiplicity a pull (`-1`), which
    contradicts the provider-side non-pull premise. -/
theorem not_activeMainSelfAMemProviderRowMatchSpec_of_main_mem_op_one
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_constraints : witness.Constraints)
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1) :
    ¬ ActiveMainSelfAMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_self
  rcases h_self with
    ⟨providerInteraction, _h_provider_witness, h_msg, h_nonpull, _h_nonzero,
      providerTable, h_providerTable, _h_providerInteraction,
      providerRow, h_providerRow, _h_providerSpec, h_providerComponent,
      h_providerEval, _h_match⟩
  have h_raw :
      (((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg))
        (ZiskFv.AirsClean.Main.aMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op :
      (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.aMemMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar)).mem_op =
        (eval (mainTable.environment mainRow) mainMsg).mem_op :=
    memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
  rw [ZiskFv.AirsClean.Main.eval_aMemMessageExpr] at h_provider_mem_op
  have h_provider_mem_op_one :
      (ZiskFv.AirsClean.Main.aMemMessage
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).mem_op = 1 := by
    simpa [h_main_mem_op] using h_provider_mem_op
  have h_providerConstraints :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).operations.ConstraintsHold
        (providerTable.environment providerRow) := by
    have h_rowConstraints := h_constraints providerTable h_providerTable providerRow h_providerRow
    rw [h_providerComponent] at h_rowConstraints
    exact h_rowConstraints
  obtain ⟨h_a_src_mem, h_a_src_reg, _, _, _, _, _, _⟩ :=
    main_mem_selector_booleanities_of_component_constraints h_providerConstraints
  have h_mult_row :
      -((eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).rom.a_src_mem
        + (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).rom.a_src_reg) = (-1 : FGL) :=
    main_a_mem_current_mult_neg_one_of_mem_op_one _ h_a_src_mem h_a_src_reg
      h_provider_mem_op_one
  have h_eval_mult :
      (((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg))
        (ZiskFv.AirsClean.Main.aMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).mult = -1 :=
    main_a_mem_current_eval_mult_eq_neg_one
      (providerTable.environment providerRow)
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar h_mult_row
  have h_provider_mult : providerInteraction.mult = -1 := by
    rw [h_providerEval]
    exact h_eval_mult
  exact h_nonpull h_provider_mult

/-- A Main-side load message (`mem_op = 1`) cannot be matched by the
    current-access Main self-provider `b` branch. -/
theorem not_activeMainSelfBMemProviderRowMatchSpec_of_main_mem_op_one
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_constraints : witness.Constraints)
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1) :
    ¬ ActiveMainSelfBMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_self
  rcases h_self with
    ⟨providerInteraction, _h_provider_witness, h_msg, h_nonpull, _h_nonzero,
      providerTable, h_providerTable, _h_providerInteraction,
      providerRow, h_providerRow, _h_providerSpec, h_providerComponent,
      h_providerEval, _h_match⟩
  have h_raw :
      (((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg))
        (ZiskFv.AirsClean.Main.bMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op :
      (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.bMemMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar)).mem_op =
        (eval (mainTable.environment mainRow) mainMsg).mem_op :=
    memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
  rw [ZiskFv.AirsClean.Main.eval_bMemMessageExpr] at h_provider_mem_op
  have h_provider_mem_op_one :
      (ZiskFv.AirsClean.Main.bMemMessage
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).mem_op = 1 := by
    simpa [h_main_mem_op] using h_provider_mem_op
  have h_providerConstraints :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).operations.ConstraintsHold
        (providerTable.environment providerRow) := by
    have h_rowConstraints := h_constraints providerTable h_providerTable providerRow h_providerRow
    rw [h_providerComponent] at h_rowConstraints
    exact h_rowConstraints
  obtain ⟨_, _, h_b_src_mem, h_b_src_ind, h_b_src_reg, _, _, _⟩ :=
    main_mem_selector_booleanities_of_component_constraints h_providerConstraints
  have h_mult_row :
      -((eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).rom.b_src_mem
        + (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).rom.b_src_ind
        + (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).rom.b_src_reg) = (-1 : FGL) :=
    main_b_mem_current_mult_neg_one_of_mem_op_one _ h_b_src_mem h_b_src_ind
      h_b_src_reg h_provider_mem_op_one
  have h_eval_mult :
      (((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg))
        (ZiskFv.AirsClean.Main.bMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).mult = -1 :=
    main_b_mem_current_eval_mult_eq_neg_one
      (providerTable.environment providerRow)
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar h_mult_row
  have h_provider_mult : providerInteraction.mult = -1 := by
    rw [h_providerEval]
    exact h_eval_mult
  exact h_nonpull h_provider_mult

/-- A Main-side load message (`mem_op = 1`) cannot be matched by the
    current-access Main self-provider `c` branch. Store/current Main emissions
    have opcode `2*(store_mem + store_ind) + 3*store_reg`, never `1` for
    Boolean selectors. -/
theorem not_activeMainSelfCMemProviderRowMatchSpec_of_main_mem_op_one
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_constraints : witness.Constraints)
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1) :
    ¬ ActiveMainSelfCMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_self
  rcases h_self with
    ⟨_providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, h_providerTable, _h_providerInteraction,
      providerRow, h_providerRow, _h_providerSpec, h_providerComponent,
      h_providerEval, _h_match⟩
  have h_raw :
      (((MemBusChannel.emitted
        (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_mem
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_ind
          + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg))
        (ZiskFv.AirsClean.Main.cMemMessageExpr
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).toRaw).eval
        (providerTable.environment providerRow)).msg =
        (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow)).msg := by
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  have h_provider_mem_op :
      (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.cMemMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar)).mem_op =
        (eval (mainTable.environment mainRow) mainMsg).mem_op :=
    memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
  rw [ZiskFv.AirsClean.Main.eval_cMemMessageExpr] at h_provider_mem_op
  have h_provider_mem_op_one :
      (ZiskFv.AirsClean.Main.cMemMessage
        (eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar)).mem_op = 1 := by
    simpa [h_main_mem_op] using h_provider_mem_op
  have h_providerConstraints :
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).operations.ConstraintsHold
        (providerTable.environment providerRow) := by
    have h_rowConstraints := h_constraints providerTable h_providerTable providerRow h_providerRow
    rw [h_providerComponent] at h_rowConstraints
    exact h_rowConstraints
  obtain ⟨_, _, _, _, _, h_store_mem, h_store_ind, h_store_reg⟩ :=
    main_mem_selector_booleanities_of_component_constraints h_providerConstraints
  exact false_of_main_c_mem_op_one _ h_store_mem h_store_ind h_store_reg
    h_provider_mem_op_one

/-- For a Main-side load message (`mem_op = 1`), the register-pre Main-self
branches are impossible (`mem_op = 3`). Ruling out the three current-access
Main memory branches rules out the aggregate Main-self branch. -/
theorem not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one_no_memory_branches
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1)
    (h_no_a_mem :
      ¬ ActiveMainSelfAMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as)
    (h_no_b_mem :
      ¬ ActiveMainSelfBMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as)
    (h_no_c_mem :
      ¬ ActiveMainSelfCMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as) :
    ¬ ActiveMainSelfMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_self
  rcases h_self with
    ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction,
      providerRow, h_providerRow, h_providerSpec, h_providerComponent, h_match⟩
  rcases h_match with h_a_reg | h_a_mem | h_b_reg | h_b_mem | h_c_reg | h_c_mem
  · have h_raw :
        (((MemBusChannel.emitted
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.a_src_reg
          (ZiskFv.AirsClean.Main.aRegPreMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_a_reg.1, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Main.aRegPreMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.Main.eval_aRegPreMessageExpr] at h_provider_mem_op
    simp [h_main_mem_op] at h_provider_mem_op
  · exact h_no_a_mem ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      providerRow, h_providerRow, h_providerSpec, h_providerComponent, h_a_mem⟩
  · have h_raw :
        (((MemBusChannel.emitted
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.b_src_reg
          (ZiskFv.AirsClean.Main.bRegPreMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_b_reg.1, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Main.bRegPreMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.Main.eval_bRegPreMessageExpr] at h_provider_mem_op
    simp [h_main_mem_op] at h_provider_mem_op
  · exact h_no_b_mem ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      providerRow, h_providerRow, h_providerSpec, h_providerComponent, h_b_mem⟩
  · have h_raw :
        (((MemBusChannel.emitted
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.rom.store_reg
          (ZiskFv.AirsClean.Main.cRegPreMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_c_reg.1, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.Main.cRegPreMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.Main.eval_cRegPreMessageExpr] at h_provider_mem_op
    simp [h_main_mem_op] at h_provider_mem_op
  · exact h_no_c_mem ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
      h_nonzero, providerTable, h_providerTable, h_providerInteraction,
      providerRow, h_providerRow, h_providerSpec, h_providerComponent, h_c_mem⟩

/-- A Main-side load message (`mem_op = 1`) cannot be matched by any Main
    self-provider branch. Register-pre branches have `mem_op = 3`, while the
    current-access branches are ruled out by ROM-selector Booleanity from
    `witness.Constraints`. -/
theorem not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_constraints : witness.Constraints)
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1) :
    ¬ ActiveMainSelfMemProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as :=
  not_activeMainSelfMemProviderRowMatchSpec_of_main_mem_op_one_no_memory_branches
    h_mainEval h_main_mem_op
    (not_activeMainSelfAMemProviderRowMatchSpec_of_main_mem_op_one
      h_constraints h_mainEval h_main_mem_op)
    (not_activeMainSelfBMemProviderRowMatchSpec_of_main_mem_op_one
      h_constraints h_mainEval h_main_mem_op)
    (not_activeMainSelfCMemProviderRowMatchSpec_of_main_mem_op_one
      h_constraints h_mainEval h_main_mem_op)

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

/-- A data-memory Main pull (`mem_op = 1`) cannot be matched by RegisterBoundary.

RegisterBoundary emits only register-memory (`mem_op = 3`) boot/reload messages. This derives the
load-side RegisterBoundary exclusion from message equality rather than carrying it as a caller
residue. -/
theorem not_activeMainRegisterBoundaryProviderRowMatchSpec_of_main_mem_op_one
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mainTable : Table FGL}
    {mainRow : Array FGL}
    {mainInteraction : Interaction FGL}
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    {multiplicity as : FGL}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (mainTable.environment mainRow))
    (h_main_mem_op :
      (eval (mainTable.environment mainRow) mainMsg).mem_op = 1) :
    ¬ ActiveMainRegisterBoundaryProviderRowMatchSpec program witness mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  intro h_regBoundary
  rcases h_regBoundary with
    ⟨providerInteraction, _h_provider_witness, h_msg, _h_nonpull, _h_nonzero,
      providerTable, _h_providerTable, h_providerInteraction, h_providerComponent⟩
  rcases exists_registerBoundary_mem_row_eval_of_interaction_mem
      h_providerComponent h_providerInteraction with h_boot | h_reload
  · rcases h_boot with ⟨providerRow, _h_providerRow, h_providerEval⟩
    have h_raw :
        (((MemBusChannel.emitted (-1)
          (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.RegisterBoundary.bootMessageExpr
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_bootMessageExpr] at h_provider_mem_op
    simp [h_main_mem_op] at h_provider_mem_op
  · rcases h_reload with ⟨providerRow, _h_providerRow, h_providerEval⟩
    have h_raw :
        (((MemBusChannel.emitted 1
          (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr
            ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).toRaw).eval
          (providerTable.environment providerRow)).msg =
          (((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
            (mainTable.environment mainRow)).msg := by
      rw [← h_providerEval, ← h_mainEval]
      exact h_msg
    have h_provider_mem_op :
        (eval (providerTable.environment providerRow)
            (ZiskFv.AirsClean.RegisterBoundary.reloadMessageExpr
              ZiskFv.AirsClean.RegisterBoundary.component.rowInputVar)).mem_op =
          (eval (mainTable.environment mainRow) mainMsg).mem_op :=
      memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq (h_msg := h_raw)
    rw [ZiskFv.AirsClean.RegisterBoundary.eval_reloadMessageExpr] at h_provider_mem_op
    simp [h_main_mem_op] at h_provider_mem_op

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
