import ZiskFv.AirsClean.FullEnsemble

/-!
# Full Clean ensemble balance projections

T7 needs canonical proofs to consume the full Clean ensemble directly,
rather than family-local ensembles.  This module exposes the first reusable
structural facts from `FullEnsemble.fullRv64imEnsemble`: the concrete table
classification and the balanced operation/memory channel projections.

## Trust note

No axioms.  These lemmas only unpack `EnsembleWitness.BalancedChannels` and
the `fullRv64imEnsemble` table list.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- Concrete component classification for the row-coherent full Clean
    ensemble. Components appear newest-first after the empty verifier table,
    matching Clean's `SoundEnsemble.addTable` list discipline. -/
theorem component_mem_fullRv64im_cases
    {length : ℕ} {program : Program length}
    {component : Component FGL}
    (h_mem : component ∈ (fullRv64imEnsemble length program).ensemble.allTables) :
    component = (fullRv64imEnsemble length program).ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.MemAlignReadByte.component
      ∨ component = ZiskFv.AirsClean.MemAlignByte.component
      ∨ component = ZiskFv.AirsClean.MemAlign.component
      ∨ component = ZiskFv.AirsClean.Mem.componentWithMemBus
      ∨ component = ZiskFv.AirsClean.ArithDiv.component
      ∨ component = ZiskFv.AirsClean.ArithMul.component
      ∨ component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.Binary.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
    at h_mem
  rcases h_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inl h_marb)
  · exact Or.inr (Or.inr (Or.inl h_mab))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_memAlign)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_mem))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithDiv)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_arithMul))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binExt)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binary))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_binaryAdd)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_main)))))))))
  · cases h_empty

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute operation-bus interactions. -/
theorem verifierTable_interactionsWith_opBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      OpBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- The full ensemble verifier table is the empty verifier component, so it
    cannot contribute memory-bus interactions. -/
theorem verifierTable_interactionsWith_memBus_nil
    (length : ℕ) (program : Program length) :
    (fullRv64imEnsemble length program).ensemble.verifierTable.operations.interactionsWith
      MemBusChannel.toRaw = [] := by
  simp [fullRv64imEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- Project the full ensemble's `BalancedChannels` hypothesis to the
    concrete operation-bus interaction list. -/
theorem opBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith OpBusChannel.toRaw) := by
  have h := h_balanced OpBusChannel.toRaw (by
    change OpBusChannel.toRaw ∈ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Project the full ensemble's `BalancedChannels` hypothesis to the
    concrete memory-bus interaction list. -/
theorem memBus_balanced_of_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith MemBusChannel.toRaw) := by
  have h := h_balanced MemBusChannel.toRaw (by
    change MemBusChannel.toRaw ∈ [MemBusChannel.toRaw, OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-! ## Empty operation-bus surfaces inside the full ensemble -/

/-- A table whose component is MemAlignReadByte has no operation-bus
    interactions. -/
theorem memAlignReadByte_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.MemAlignReadByte.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignReadByte.component,
      ZiskFv.AirsClean.MemAlignReadByte.circuit,
      ZiskFv.AirsClean.MemAlignReadByte.memAlignReadByteElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is MemAlignByte has no operation-bus
    interactions. -/
theorem memAlignByte_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.MemAlignByte.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlignByte.component,
      ZiskFv.AirsClean.MemAlignByte.circuit,
      ZiskFv.AirsClean.MemAlignByte.memAlignByteElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is MemAlign has no operation-bus interactions. -/
theorem memAlign_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.MemAlign.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.MemAlign.component,
      ZiskFv.AirsClean.MemAlign.circuit,
      ZiskFv.AirsClean.MemAlign.memAlignWithMemBusElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is Mem has no operation-bus interactions. -/
theorem mem_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithMemBus) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.Mem.componentWithMemBus.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithMemBus,
      ZiskFv.AirsClean.Mem.circuitWithMemBus,
      ZiskFv.AirsClean.Mem.memWithMemBusElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is the current ArithDiv carry-chain component has
    no operation-bus interactions. DIV/REM op-bus surfaces are still bridged
    by the dedicated primary/secondary components outside the full ensemble. -/
theorem arithDiv_table_interactionsWith_opBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithDiv.component) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.ArithDiv.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.ArithDiv.component,
      ZiskFv.AirsClean.ArithDiv.circuit,
      ZiskFv.AirsClean.ArithDiv.arithDivElaborated,
      OpBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-! ## Empty memory-bus surfaces inside the full ensemble -/

/-- A table whose component is BinaryAdd has no memory-bus interactions. -/
theorem binaryAdd_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.BinaryAdd.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.BinaryAdd.component,
      ZiskFv.AirsClean.BinaryAdd.circuit,
      ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is lookup-aware Binary has no memory-bus
    interactions. -/
theorem staticBinary_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Binary.staticLookupComponent) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Binary.staticLookupComponent,
      ZiskFv.AirsClean.Binary.staticLookupCircuit,
      ZiskFv.AirsClean.Binary.binaryWithStaticBinaryTableElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is lookup-aware BinaryExtension has no memory-bus
    interactions. -/
theorem staticBinaryExtension_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.BinaryExtension.staticLookupComponent) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.circuit.channels := by
    simp [circuit_norm,
      ZiskFv.AirsClean.BinaryExtension.staticLookupComponent,
      ZiskFv.AirsClean.BinaryExtension.staticLookupCircuit,
      ZiskFv.AirsClean.BinaryExtension.binaryExtensionWithStaticTableElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is ArithMul has no memory-bus interactions. -/
theorem arithMul_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithMul.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.ArithMul.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.ArithMul.component,
      ZiskFv.AirsClean.ArithMul.circuit,
      ZiskFv.AirsClean.ArithMul.arithMulElaborated,
      OpBusChannel, MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-- A table whose component is the current ArithDiv carry-chain component has
    no memory-bus interactions. -/
theorem arithDiv_table_interactionsWith_memBus_nil
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithDiv.component) :
    table.interactionsWith MemBusChannel.toRaw = [] := by
  have h_not :
      MemBusChannel.toRaw ∉
        ZiskFv.AirsClean.ArithDiv.component.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.ArithDiv.component,
      ZiskFv.AirsClean.ArithDiv.circuit,
      ZiskFv.AirsClean.ArithDiv.arithDivElaborated,
      MemBusChannel]
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [h_component]
  exact h_not

/-! ## Full-ensemble op-bus counterpart classification -/

/-- Clean balance replacement shape for the full ensemble: an active Main
    operation-bus interaction has a same-message counterpart whose
    multiplicity is neither another pull nor zero. -/
theorem exists_matching_nonzero_nonpull_of_active_main_op_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith OpBusChannel.toRaw)
    (opBus_balanced_of_witness witness h_balanced)
    mainInteraction h_mem h_active

/-- A constrained unified Main table can only contribute operation-bus
    interactions with multiplicity `-1` (active row) or `0` (inactive row). -/
theorem main_table_opBus_mult_neg_one_or_zero_of_constraints
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_constraints : table.Constraints)
    (h_main :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) :
    ∀ {interaction : Interaction FGL},
      interaction ∈ table.interactionsWith OpBusChannel.toRaw →
      interaction.mult = -1 ∨ interaction.mult = 0 := by
  intro interaction h_interaction
  refine ((Table.forall_interactionsWith_iff table OpBusChannel.toRaw
    (fun interaction => interaction.mult = -1 ∨ interaction.mult = 0)).mpr ?_)
    interaction h_interaction
  intro row h_row abstractInteraction h_abs h_channel
  have h_abs_with :
      abstractInteraction ∈ table.component.operations.interactionsWith
        OpBusChannel.toRaw := by
    simp [Operations.interactionsWith, h_abs, h_channel]
  have h_main_interactions :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw)] := by
    simpa [h_main] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  have h_abs_eq :
      abstractInteraction =
        ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw) := by
    simpa [h_main_interactions] using h_abs_with
  subst abstractInteraction
  have h_bool :=
    ZiskFv.AirsClean.Main.is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints
      length program (table.environment row)
      (by simpa [h_main] using h_constraints row h_row)
  let x := (table.environment row)
    (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
      length program).rowInputVar.core.is_external_op
  have h_mul_raw : x * (1 + -1 * x) = 0 := by
    simpa [Expression.eval, x] using h_bool
  have h_mul : x * (1 - x) = 0 := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h_mul_raw
  rcases mul_eq_zero.mp h_mul with h_zero | h_one_sub
  · right
    change Expression.eval (table.environment row)
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar.core.is_external_op) = 0
    simp [Expression.eval, x, h_zero]
  · left
    have h_one : x = 1 := (sub_eq_zero.mp h_one_sub).symm
    change Expression.eval (table.environment row)
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar.core.is_external_op) = -1
    simp [Expression.eval, x, h_one]

/-- Classify the balanced same-message operation-bus counterpart in the full
    ensemble after excluding verifier and components that expose no op-bus
    interactions.

The unified Main case is intentionally left explicit. Excluding it requires
    the row-local Main multiplicity lemma in a cheap full-ensemble form; this
    theorem avoids hiding that remaining proof obligation. -/
theorem exists_matching_op_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith OpBusChannel.toRaw
            ∧ (table.component = ZiskFv.AirsClean.ArithMul.component
              ∨ table.component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.Binary.staticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.BinaryAdd.component
              ∨ table.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_op_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_component_mem :
      table.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith OpBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_opBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact memAlignReadByte_table_interactionsWith_opBus_nil h_marb
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact memAlignByte_table_interactionsWith_opBus_nil h_mab
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact memAlign_table_interactionsWith_opBus_nil h_memAlign
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact mem_table_interactionsWith_opBus_nil h_mem
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith OpBusChannel.toRaw = [] := by
      exact arithDiv_table_interactionsWith_opBus_nil h_arithDiv
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inl h_arithMul⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inl h_binExt)⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inl h_binary))⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inl h_binaryAdd)))⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inr h_main)))⟩

/-- Classify the balanced same-message operation-bus counterpart as a
    provider table in the full ensemble. The unified Main self-provider case
    is ruled out from `witness.Constraints`, using the row-local
    `is_external_op` boolean assertion from the unified Main component. -/
theorem exists_matching_provider_op_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith OpBusChannel.toRaw
            ∧ (table.component = ZiskFv.AirsClean.ArithMul.component
              ∨ table.component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.Binary.staticLookupComponent
              ∨ table.component = ZiskFv.AirsClean.BinaryAdd.component) := by
  obtain ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, h_component⟩ :=
    exists_matching_op_component_of_active_main_interaction
      witness h_balanced h_mem h_active
  rcases h_component with h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inl h_arithMul⟩
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inl h_binExt)⟩
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inr (Or.inl h_binary))⟩
  · exact ⟨providerInteraction, h_provider_mem, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inr (Or.inr h_binaryAdd))⟩
  · have h_mult := main_table_opBus_mult_neg_one_or_zero_of_constraints
      (h_constraints table h_table) h_main h_mem_table
    rcases h_mult with h_neg | h_zero
    · exact False.elim (h_nonpull h_neg)
    · exact False.elim (h_nonzero h_zero)

/-! ## Full-ensemble memory-bus counterpart classification -/

/-- Clean balance replacement shape for full-ensemble memory interactions:
    an active Main memory-bus interaction has a same-message counterpart
    whose multiplicity is neither another pull nor zero. -/
theorem exists_matching_nonzero_nonpull_of_active_main_mem_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith MemBusChannel.toRaw)
    (memBus_balanced_of_witness witness h_balanced)
    mainInteraction h_mem h_active

/-- Classify the balanced same-message memory-bus counterpart in the full
    ensemble after excluding verifier and components that expose no
    memory-bus interactions.

The unified Main case is intentionally explicit, matching the Mem-family
    bridge: excluding it requires selector legality beyond the current
    Main row soundness, and keeping it visible avoids laundering that missing
    proof into a provider theorem. -/
theorem exists_matching_mem_component_of_active_main_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0
        ∧ ∃ table ∈ witness.allTables,
          providerInteraction ∈ table.interactionsWith MemBusChannel.toRaw
            ∧ (table.component = ZiskFv.AirsClean.MemAlignReadByte.component
              ∨ table.component = ZiskFv.AirsClean.MemAlignByte.component
              ∨ table.component = ZiskFv.AirsClean.MemAlign.component
              ∨ table.component = ZiskFv.AirsClean.Mem.componentWithMemBus
              ∨ table.component =
                  ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_mem_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_component_mem :
      table.component ∈ (fullRv64imEnsemble length program).ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_fullRv64im_cases h_component_mem with
    h_verifier | h_marb | h_mab | h_memAlign | h_mem | h_arithDiv |
    h_arithMul | h_binExt | h_binary | h_binaryAdd | h_main
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith MemBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_memBus_nil length program
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inl h_marb⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inl h_mab)⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inl h_memAlign))⟩
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inl h_mem)))⟩
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact arithDiv_table_interactionsWith_memBus_nil h_arithDiv
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact arithMul_table_interactionsWith_memBus_nil h_arithMul
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact staticBinaryExtension_table_interactionsWith_memBus_nil h_binExt
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact staticBinary_table_interactionsWith_memBus_nil h_binary
    simp [h_nil] at h_mem_table
  · have h_nil : table.interactionsWith MemBusChannel.toRaw = [] := by
      exact binaryAdd_table_interactionsWith_memBus_nil h_binaryAdd
    simp [h_nil] at h_mem_table
  · exact ⟨providerInteraction, by
        rw [EnsembleWitness.mem_interactionsWith]
        exact ⟨table, h_table, h_mem_table⟩,
      h_msg, h_nonpull, h_nonzero, table, h_table, h_mem_table,
      Or.inr (Or.inr (Or.inr (Or.inr h_main)))⟩

/-! ## Row extraction from full-ensemble channel interactions -/

/-- If a table's operation-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_opBus_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- If a table's memory-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_memBus_row_eval_of_singleton_interactionsWith
    {table : Table FGL} {abstractInteraction : AbstractInteraction FGL}
    (h_singleton :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [abstractInteraction])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction = abstractInteraction.eval (table.environment row) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_singleton] at h_mem
  exact h_mem

/-- Row extraction for the unified Main operation-bus interaction in the full
    ensemble. The extracted row is a `MainRowWithRom`; its `.core` is the same
    row that emits Main's memory-bus interactions. -/
theorem exists_main_op_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.emitted
          (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus
        length program
  · exact h_mem

/-- Row extraction for the unified Main memory-bus interactions in the full
    ensemble. Main exposes three memory interactions (`a`, `b`, and
    `c/store`), so the result keeps that side disjunction explicit. -/
theorem exists_main_mem_row_eval_of_interaction_mem
    {length : ℕ} {program : Program length}
    {table : Table FGL}
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
          ((MemBusChannel.emitted
            (-((ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_mem
              + (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.rom.a_src_reg))
            (ZiskFv.AirsClean.Main.aMemMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar)).toRaw).eval
            (table.environment row)
        ∨ interaction =
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
            (table.environment row)
        ∨ interaction =
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
            (table.environment row) := by
  have h_interactions :=
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_memBus
      length program
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_component, h_interactions] at h_mem
  rcases h_mem with ⟨row, h_row, h_eq | h_eq | h_eq⟩
  · exact ⟨row, h_row, Or.inl h_eq⟩
  · exact ⟨row, h_row, Or.inr (Or.inl h_eq)⟩
  · exact ⟨row, h_row, Or.inr (Or.inr h_eq)⟩

/-- Row extraction for a BinaryAdd operation-bus provider interaction in the
    full ensemble. -/
theorem exists_binaryAdd_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryAdd.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a lookup-aware Binary operation-bus provider
    interaction in the full ensemble. -/
theorem exists_staticBinary_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.Binary.opBusMessageExpr
            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Binary.staticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a lookup-aware BinaryExtension operation-bus provider
    interaction in the full ensemble. -/
theorem exists_staticBinaryExtension_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryExtension.staticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for an ArithMul operation-bus provider interaction in the
    full ensemble. -/
theorem exists_arithMul_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.ArithMul.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
            ZiskFv.AirsClean.ArithMul.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_opBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.ArithMul.component_interactionsWith_opBus
  · exact h_mem

/-! ## Full-ensemble operation-bus row bridges -/

/-- Spec-carrying full-ensemble operation-bus projection: an active
    unified-Main operation-bus interaction has a balanced same-message
    provider counterpart, and the Binary-family provider branches are
    resolved to concrete table rows carrying `witness.Spec`.
    The ArithMul provider branch is also resolved to a concrete row. -/
theorem exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧ mainInteraction =
          ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw).eval
            (mainTable.environment mainRow)
        ∧ ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.ArithMul.component
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                            ZiskFv.AirsClean.ArithMul.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                            ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Binary.staticLookupComponent
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.Binary.opBusMessageExpr
                            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                      ∧ providerInteraction =
                        ((OpBusChannel.pushed
                          (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                            ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))) := by
  have h_main_witness :
      mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_op_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_provider_op_component_of_active_main_interaction
      witness h_constraints h_balanced h_main_witness h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  have h_providerSpecs : providerTable.Spec :=
    h_specs providerTable h_providerTable
  rcases h_providerComponent with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_arithMul_row_eval_of_interaction_mem
        h_arithMul h_providerInteraction
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_arithMul, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinaryExtension_row_eval_of_interaction_mem
        h_binExt h_providerInteraction
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binExt, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinary_row_eval_of_interaction_mem
        h_binary h_providerInteraction
    right
    right
    left
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binary, h_providerEval⟩
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binaryAdd_row_eval_of_interaction_mem
        h_binaryAdd h_providerInteraction
    right
    right
    right
    exact ⟨providerRow, h_providerRow,
      h_providerSpecs providerRow h_providerRow, h_binaryAdd, h_providerEval⟩

/-- Legacy-entry view of the full-ensemble operation-bus bridge.

    Clean balance proves equality of raw operation-bus message arrays.  This
    adapter keeps the full-ensemble provider row/spec information while
    translating each provider branch into the `OperationBus.matches_entry`
    shape consumed by the existing opcode proofs. -/
theorem exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      mainTable.component.Spec (mainTable.environment mainRow)
        ∧ mainInteraction =
          ((OpBusChannel.emitted
            (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                length program).rowInputVar.core)).toRaw).eval
            (mainTable.environment mainRow)
        ∧ ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
          providerInteraction.msg = mainInteraction.msg
            ∧ providerInteraction.mult ≠ -1
            ∧ providerInteraction.mult ≠ 0
            ∧ ∃ providerTable ∈ witness.allTables,
              providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
                ∧
                ((∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.ArithMul.component
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                              ZiskFv.AirsClean.ArithMul.component.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component =
                        ZiskFv.AirsClean.Binary.staticLookupComponent
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Binary.opBusMessageExpr
                              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
                  ∨ (∃ providerRow ∈ providerTable.table,
                    providerTable.component.Spec (providerTable.environment providerRow)
                      ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                      ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
                                length program).rowInputVar.core)) 1)
                        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))) := by
  obtain ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
      h_providerTable, h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_msg_eq_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  refine ⟨mainRow, h_mainRow, h_mainSpec, h_mainEval, providerInteraction,
    h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
    h_providerTable, h_providerInteraction, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_arithMul
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binExt
    right
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binary
    right
    right
    left
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_providerEval⟩ := h_binaryAdd
    right
    right
    right
    refine ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg

/-- Row extraction for a Mem memory-bus provider interaction in the full
    ensemble. -/
theorem exists_mem_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithMemBus_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlign memory-bus interaction in the full ensemble. -/
theorem exists_memAlign_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
            - ZiskFv.AirsClean.MemAlign.selAssumeExpr
              ZiskFv.AirsClean.MemAlign.component.rowInputVar)
          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlign.component_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlignByte memory-bus provider interaction in the
    full ensemble. -/
theorem exists_memAlignByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignByte.component_interactionsWith_memBus
  · exact h_mem

/-- Row extraction for a MemAlignReadByte memory-bus provider interaction in
    the full ensemble. -/
theorem exists_memAlignReadByte_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.MemAlignReadByte.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.pushed
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessageExpr
            ZiskFv.AirsClean.MemAlignReadByte.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_memBus_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.MemAlignReadByte.component_interactionsWith_memBus
  · exact h_mem

/-! ## Full-ensemble memory-bus row bridges -/

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
      ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
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
                  providerTable.component = ZiskFv.AirsClean.Mem.componentWithMemBus
                    ∧ providerInteraction =
                      ((MemBusChannel.emitted
                        ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar.sel
                        (ZiskFv.AirsClean.Mem.memBusMessageExpr
                          ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar)).toRaw).eval
                        (providerTable.environment providerRow))
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
  obtain ⟨mainRow, h_mainRow, _h_mainEval⟩ :=
    exists_main_mem_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_mem_component_of_active_main_interaction
      witness h_balanced h_main_mem_witness h_active
  refine ⟨mainRow, h_mainRow, providerInteraction, h_provider_witness, h_msg,
    h_nonpull, h_nonzero, providerTable, h_providerTable,
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
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_mem_row_eval_of_interaction_mem h_mem h_providerInteraction
    right
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_mem, h_providerEval⟩
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
                      ∧ providerTable.component = ZiskFv.AirsClean.Mem.componentWithMemBus
                      ∧ providerInteraction =
                        ((MemBusChannel.emitted
                          ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar.sel
                          (ZiskFv.AirsClean.Mem.memBusMessageExpr
                            ZiskFv.AirsClean.Mem.componentWithMemBus.rowInputVar)).toRaw).eval
                          (providerTable.environment providerRow))
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
  obtain ⟨mainRow, h_mainRow, providerInteraction, h_provider_witness, h_msg,
      h_nonpull, h_nonzero, providerTable, h_providerTable,
      h_providerInteraction, h_providerComponent⟩ :=
    exists_mem_provider_row_msg_eq_of_active_main_table_interaction
      witness h_balanced h_mainTable h_mainComponent h_mainInteraction h_active
  have h_mainSpec :
      mainTable.component.Spec (mainTable.environment mainRow) :=
    h_specs mainTable h_mainTable mainRow h_mainRow
  refine ⟨mainRow, h_mainRow, h_mainSpec, providerInteraction,
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

end ZiskFv.AirsClean.FullEnsemble
