import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec

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
      ∨ component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
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

/-- Every concrete witness for the full RV64IM ensemble contains a table for
    the dual-aware mutable Mem component. This is only table selection: it
    does not assert chronological embedding of that table's projected rows
    into an accepted memory trace. -/
theorem exists_mem_table_of_fullRv64im_witness
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble) :
    ∃ table ∈ witness.allTables,
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus := by
  have h_component_mem :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ∈
        (fullRv64imEnsemble length program).ensemble.allTables := by
    simp [fullRv64imEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
      SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables]
  have h_in_map :
      ZiskFv.AirsClean.Mem.componentWithDualMemBus ∈
        witness.allTables.map (·.component) := by
    rw [witness.allTables_map_component]
    exact h_component_mem
  rcases List.mem_map.mp h_in_map with ⟨table, h_table, h_component⟩
  exact ⟨table, h_table, h_component⟩

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
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.interactionsWith OpBusChannel.toRaw = [] := by
  have h_not :
      OpBusChannel.toRaw ∉
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.circuit.channels := by
    simp [circuit_norm, ZiskFv.AirsClean.Mem.componentWithDualMemBus,
      ZiskFv.AirsClean.Mem.circuitWithDualMemBus,
      ZiskFv.AirsClean.Mem.memWithDualMemBusElaborated,
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
              ∨ table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
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

/-- If a table's memory-bus abstract interactions are exactly two entries,
    any concrete table-level interaction on that channel is one of those two
    entries evaluated at some row. -/
theorem exists_memBus_row_eval_of_pair_interactionsWith
    {table : Table FGL} {left right : AbstractInteraction FGL}
    (h_pair :
      table.component.operations.interactionsWith MemBusChannel.toRaw =
        [left, right])
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    (∃ row ∈ table.table,
      interaction = left.eval (table.environment row))
    ∨ (∃ row ∈ table.table,
      interaction = right.eval (table.environment row)) := by
  simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map,
    h_pair] at h_mem
  obtain ⟨row, h_row, h_eval⟩ := h_mem
  rcases h_eval with h_left | h_right
  · exact Or.inl ⟨row, h_row, h_left⟩
  · exact Or.inr ⟨row, h_row, h_right⟩

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

/-- Legacy-Main view of the full-ensemble operation-bus bridge.

    This specializes the selected unified Clean Main row back to the existing
    `Valid_Main` row used by opcode proofs.  It deliberately preserves all
    full-ensemble provider alternatives: later opcode-specific adapters may
    rule out branches only from provider-local facts, not by caller promise. -/
theorem exists_op_provider_row_matches_legacy_main_spec_of_active_main_table_interaction
    {length : ℕ} {program : Program length}
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    (h_specs : witness.Spec)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent :
      mainTable.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_main_row :
      ∀ mainRow ∈ mainTable.table,
        eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar.core =
          ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
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
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessageExpr
                          ZiskFv.AirsClean.ArithMul.component.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component =
                    ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                          ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component =
                    ZiskFv.AirsClean.Binary.staticLookupComponent
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.Binary.opBusMessageExpr
                          ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
              ∨ (∃ providerRow ∈ providerTable.table,
                providerTable.component.Spec (providerTable.environment providerRow)
                  ∧ providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                  ∧ ZiskFv.Airs.OperationBus.matches_entry
                    (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
                    (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
                      (eval (providerTable.environment providerRow)
                        (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                          ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))) := by
  obtain ⟨mainRow, h_mainRow, _h_mainSpec, _h_mainEval, providerInteraction,
      h_provider_witness, h_msg, h_nonpull, h_nonzero, providerTable,
      h_providerTable, h_providerInteraction, h_providerBranch⟩ :=
    exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction
      witness h_constraints h_balanced h_specs h_mainTable h_mainComponent
      h_mainInteraction h_active
  have h_main_entry :
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar.core)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.eval_opBusMessageExpr]
    rw [h_main_row mainRow h_mainRow]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  refine ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull,
    h_nonzero, providerTable, h_providerTable, h_providerInteraction, ?_⟩
  rcases h_providerBranch with h_arithMul | h_binExt | h_binary | h_binaryAdd
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_arithMul
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binExt
    right
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binary
    right
    right
    left
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩
  · obtain ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      h_match⟩ := h_binaryAdd
    right
    right
    right
    exact ⟨providerRow, h_providerRow, h_providerSpec, h_providerComponent,
      by
        rw [← h_main_entry]
        exact h_match⟩

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

/-- Row extraction for a dual-aware Mem memory-bus provider interaction in
    the full ensemble. The selected interaction is either the primary Mem
    provider emission or the pinned `dual_mem = 1` read emission. -/
theorem exists_mem_dual_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith MemBusChannel.toRaw) :
    (∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel
          (ZiskFv.AirsClean.Mem.memBusMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (table.environment row))
    ∨ (∃ row ∈ table.table,
      interaction =
        ((MemBusChannel.emitted
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar.sel_dual
          (ZiskFv.AirsClean.Mem.memBusDualMessageExpr
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)).toRaw).eval
          (table.environment row)) := by
  apply exists_memBus_row_eval_of_pair_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus
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

/-! ## Full-ensemble Mem read-replay row projections -/

/-- Public replay-row view of a primary Mem provider row when it is selected
    as a read. The Clean provider interaction carries selector multiplicity,
    but chronological memory replay uses legacy read multiplicity `-1`. -/
@[reducible]
def memPrimaryReadReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusMessage row) (-1) 2

/-- Public replay-row view of a dual Mem provider row. Dual Mem emissions are
    pinned reads, so the replay multiplicity is the legacy read `-1`. -/
@[reducible]
def memDualReadReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusDualMessage row) (-1) 2

/-- Public replay-row view of a primary Mem provider row, preserving the
    read/write polarity carried by `wr`. For boolean `wr`, this maps
    `wr = 0` to legacy read multiplicity `-1` and `wr = 1` to write
    multiplicity `1`. -/
@[reducible]
def memPrimaryReplayEntryOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
    (ZiskFv.AirsClean.Mem.memBusMessage row) (2 * row.wr - 1) 2

/-- Read-replay events contributed by one dual-aware Mem provider row, in
    provider emission order. -/
@[reducible]
def memReadReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row]

/-- Read/write replay events contributed by one dual-aware Mem provider row,
    in provider emission order. The primary event preserves `wr`, while the
    dual event is a pinned read. -/
@[reducible]
def memReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row]

/-- Active read-replay events contributed by one dual-aware Mem provider row.
    Inactive primary/dual emissions do not contribute chronological memory
    replay events. -/
@[reducible]
def activeMemReadReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  (if row.sel = 1 then [memPrimaryReadReplayEntryOfRow row] else [])
    ++
  (if row.sel_dual = 1 then [memDualReadReplayEntryOfRow row] else [])

/-- Active read/write replay events contributed by one dual-aware Mem
    provider row. The primary event preserves `wr`, while the dual event is a
    pinned read. -/
@[reducible]
def activeMemReplayEntriesOfRow
    (row : ZiskFv.AirsClean.Mem.MemRow FGL) :
    List (Interaction.MemoryBusEntry FGL) :=
  (if row.sel = 1 then [memPrimaryReplayEntryOfRow row] else [])
    ++
  (if row.sel_dual = 1 then [memDualReadReplayEntryOfRow row] else [])

/-- If neither selector is active, a Mem row contributes no active read-replay
    entries. -/
theorem activeMemReadReplayEntriesOfRow_eq_nil_of_inactive
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReadReplayEntriesOfRow row = [] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- If neither selector is active, a Mem row contributes no active
    read/write replay entries. -/
theorem activeMemReplayEntriesOfRow_eq_nil_of_inactive
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReplayEntriesOfRow row = [] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A primary-only selected row contributes exactly its primary read entry to
    the active read-replay surface. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A primary-only selected row contributes exactly its primary
    polarity-preserving entry to the active read/write replay surface. -/
theorem activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual ≠ 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A dual-only selected row contributes exactly its dual read entry to the
    active read-replay surface. -/
theorem activeMemReadReplayEntriesOfRow_eq_dual_of_not_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memDualReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- A dual-only selected row contributes exactly its dual read entry to the
    active read/write replay surface. -/
theorem activeMemReplayEntriesOfRow_eq_dual_of_not_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel ≠ 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memDualReadReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- When both selectors are active, active read-replay emission is primary
    first and then dual. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  simp [activeMemReadReplayEntriesOfRow, h_sel, h_sel_dual]

/-- When both selectors are active, active read/write replay emission is
    primary first and then dual. -/
theorem activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  simp [activeMemReplayEntriesOfRow, h_sel, h_sel_dual]

/-- Under the generated per-row Mem spec, selecting the dual read emission
    forces the primary selector too, so active read-replay emission is
    primary first and then the pinned dual read. -/
theorem activeMemReadReplayEntriesOfRow_eq_primary_dual_of_spec_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReadReplayEntriesOfRow row =
      [memPrimaryReadReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  exact activeMemReadReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual

/-- Under the generated per-row Mem spec, selecting the dual read emission
    forces the primary selector too, so active read/write replay emission is
    primary first and then the pinned dual read. -/
theorem activeMemReplayEntriesOfRow_eq_primary_dual_of_spec_of_sel_dual
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1) :
    activeMemReplayEntriesOfRow row =
      [memPrimaryReplayEntryOfRow row, memDualReadReplayEntryOfRow row] := by
  exact activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual

/-- A selected primary+dual row is chronologically ordered when the primary
    timestamp is no later than the pinned dual-read timestamp. -/
theorem activeMemReplayEntriesOfRow_chronological_of_sel_of_sel_dual_of_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_le : row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    h_sel h_sel_dual]
  simpa [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological,
    memPrimaryReplayEntryOfRow, memDualReadReplayEntryOfRow,
    ZiskFv.AirsClean.Mem.memBusMessage,
    ZiskFv.AirsClean.Mem.memBusDualMessage] using h_step_le

/-- Under the generated per-row Mem spec, a selected dual row is locally
    chronological when the generated dual-step range check supplies
    `step <= step_dual`. -/
theorem activeMemReplayEntriesOfRow_chronological_of_spec_of_sel_dual_of_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_le : row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  exact activeMemReplayEntriesOfRow_chronological_of_sel_of_sel_dual_of_step_le
    (ZiskFv.AirsClean.Mem.sel_of_sel_dual_one_of_spec row h_spec h_sel_dual)
    h_sel_dual h_step_le

/-- Under the generated per-row Mem spec, local active replay emissions are
    chronological once any selected dual emission is known to have
    `step <= step_dual`. Rows with no selected dual emit zero or one active
    replay entry, so they are chronological without a timestamp comparison. -/
theorem activeMemReplayEntriesOfRow_chronological_of_spec_of_dual_step_le
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_spec : ZiskFv.AirsClean.Mem.Spec row)
    (h_step_le_of_dual :
      row.sel_dual = 1 → row.step.val ≤ row.step_dual.val) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow row) := by
  rcases ZiskFv.AirsClean.Mem.sel_dual_boolean_of_spec row h_spec with
    h_sel_dual_zero | h_sel_dual_one
  · rcases ZiskFv.AirsClean.Mem.sel_boolean_of_spec row h_spec with
      h_sel_zero | h_sel_one
    · have h_sel_ne : row.sel ≠ 1 := by
        simp [h_sel_zero]
      have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_nil_of_inactive
        h_sel_ne h_sel_dual_ne]
      simp [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological]
    · have h_sel_dual_ne : row.sel_dual ≠ 1 := by
        simp [h_sel_dual_zero]
      rw [activeMemReplayEntriesOfRow_eq_primary_of_sel_of_not_sel_dual
        h_sel_one h_sel_dual_ne]
      simp [ZiskFv.AirsClean.Mem.MemoryBusRowsChronological]
  · exact activeMemReplayEntriesOfRow_chronological_of_spec_of_sel_dual_of_step_le
      h_spec h_sel_dual_one (h_step_le_of_dual h_sel_dual_one)

/-- A selected primary+dual row has no duplicate replay entries when its
    primary and dual timestamps are distinct. PIL allows equality for
    read-read dual rows, so this lemma intentionally records the extra
    condition rather than hiding it. -/
theorem activeMemReplayEntriesOfRow_nodup_of_sel_of_sel_dual_of_step_ne
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_sel : row.sel = 1)
    (h_sel_dual : row.sel_dual = 1)
    (h_step_ne : row.step ≠ row.step_dual) :
    (activeMemReplayEntriesOfRow row).Nodup := by
  rw [activeMemReplayEntriesOfRow_eq_primary_dual_of_sel_of_sel_dual
    h_sel h_sel_dual]
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false,
    not_false_eq_true]
  constructor
  · intro h_eq
    have h_ts :
        (memPrimaryReplayEntryOfRow row).timestamp =
          (memDualReadReplayEntryOfRow row).timestamp := by
      rw [h_eq]
    simp at h_ts
    exact h_step_ne h_ts
  · simp

/-- Primary-read replay rows projected from every row of a Mem table. -/
@[reducible]
def memPrimaryReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Dual-read replay rows projected from every row of a Mem table. -/
@[reducible]
def memDualReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Read-replay row surface exposed by a dual-aware Mem table.

    Unlike the legacy compatibility projections above, this list is shaped in
    provider emission order: for each concrete Mem table row, primary comes
    before dual. Chronological ordering and read/write soundness remain
    separate global trace obligations. -/
@[reducible]
def memReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    memReadReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Primary replay rows projected from every Mem table row, preserving
    read/write polarity. -/
@[reducible]
def memPrimaryReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.map fun providerRow =>
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Full replay-row surface exposed by a dual-aware Mem table.

    Events are projected in provider emission order: primary first, preserving
    read/write polarity, then the pinned dual read for the same provider row. -/
@[reducible]
def memReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    memReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Active read-replay rows projected from selected emissions of a Mem table.
    This is the replay surface accepted-trace extraction should use when
    proving chronological memory soundness from concrete Mem rows. -/
@[reducible]
def activeMemReadReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    activeMemReadReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Active read/write replay rows projected from selected emissions of a Mem
    table. Inactive rows are omitted instead of replayed as spurious memory
    events. -/
@[reducible]
def activeMemReplayRowsOfTable
    (table : Table FGL) : List (Interaction.MemoryBusEntry FGL) :=
  table.table.flatMap fun providerRow =>
    activeMemReplayEntriesOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)

/-- Explicit row-index bridge from a concrete Clean Mem table to the
    row-indexed generated `Valid_Mem` surface.

    `Table.Constraints` is membership-based (`∀ row ∈ table.table`) and does
    not identify a row's list position with the index consumed by
    `Valid_Mem`/`generated_every_row`. This structure names that missing
    connection without turning it into an anonymous replay-soundness field:
    each concrete table position must evaluate to `rowAt mem idx`, and the
    generated Mem constraints must hold at the same index.

    The generated constraint field cites the complete extracted Mem surface:
    `generated_every_row = segment_every_row ∧ permutation_every_row`, whose
    constituent lemmas mirror the cited `mem.pil` constraints. -/
structure MemTableGeneratedRowsBridge
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop where
  component :
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
  length_eq : table.table.length = rowCount
  rowAt_eq :
    ∀ idx : Fin table.table.length,
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val
  generatedAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val

/-- Concrete range facts for the indexed Mem table rows.

    These facts name the non-field AIR range-check surface used when turning
    generated field equations into Nat timestamp order:

    * `incrementChunks` mirrors `mem.pil:384-385`.
    * `stepColumns` mirrors the `bits(MEM_STEP_BITS)` witness declarations at
      `mem.pil:110` and `mem.pil:122`, with `MEM_STEP_BITS = 40` in the pinned
      RV64IM configuration.
    * `dualStepDelta` mirrors the selector-gated range check
      `mem.pil:397`; it is intentionally conditional on `sel_dual = 1`.

    Keeping this separate from `MemTableGeneratedRowsBridge` avoids silently
    treating selector-gated range checks as unconditional replay soundness. -/
structure MemTableGeneratedRangeFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) : Prop where
  incrementChunks :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.increment_chunks_in_range mem idx.val
  stepColumns :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.step_columns_in_range mem idx.val
  dualStepDelta :
    ∀ idx : Fin table.table.length,
      mem.sel_dual idx.val = 1 →
        ZiskFv.Airs.Mem.dual_step_delta_in_range mem idx.val

/-- The indexed table bridge projects the generated row range required by
    the Mem trace spec. -/
theorem generatedMemRows_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount) :
    ZiskFv.AirsClean.Mem.GeneratedMemRows mem segment permutation rowCount := by
  intro row h_row
  have h_len : row < table.table.length := by
    rw [h_bridge.length_eq]
    exact h_row
  exact h_bridge.generatedAt ⟨row, h_len⟩

/-- Full-ensemble witness obligation for the concrete mutable Mem table:
    one witness table must be the dual-aware Mem component and must satisfy the
    indexed `Valid_Mem` bridge above. -/
def FullWitnessMemTableGeneratedRowsBridge
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop :=
  ∃ table ∈ witness.allTables,
    MemTableGeneratedRowsBridge table mem segment permutation rowCount

/-- The full-witness bridge projects the generated row range required by the
    Mem trace spec. -/
theorem generatedMemRows_of_fullWitnessMemTableGeneratedRowsBridge
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge :
      FullWitnessMemTableGeneratedRowsBridge
        witness mem segment permutation rowCount) :
    ZiskFv.AirsClean.Mem.GeneratedMemRows mem segment permutation rowCount := by
  rcases h_bridge with ⟨table, _h_table, h_table_bridge⟩
  exact generatedMemRows_of_memTableGeneratedRowsBridge h_table_bridge

/-- Project the generated Mem row fact at one concrete Clean table position. -/
theorem generated_every_row_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val :=
  h_bridge.generatedAt idx

/-- Project the local Clean bridge constraints at one concrete table
    position, via the generated Mem row surface. -/
theorem constraints_at_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.constraints_at mem idx.val :=
  ZiskFv.AirsClean.Mem.constraints_at_of_generated_every_row
    mem segment permutation idx.val (h_bridge.generatedAt idx)

/-- The indexed table bridge projects the Clean Mem row `Spec` at one
    `Valid_Mem` row. -/
theorem rowAt_spec_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.Spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) := by
  have h_constraints :=
    constraints_at_of_memTableGeneratedRowsBridge h_bridge idx
  simpa [ZiskFv.AirsClean.Mem.Spec, ZiskFv.AirsClean.Mem.constraints_at,
    ZiskFv.AirsClean.Mem.rowAt] using h_constraints

/-- The indexed table bridge projects the Clean Mem row `Spec` for the
    concrete evaluated table row at a list position. -/
theorem tableRow_spec_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.Spec
      (eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rw [h_bridge.rowAt_eq idx]
  exact h_spec

/-- A bridged generated Mem table position has a boolean current-row write
    flag at the Nat-value level. -/
theorem wr_val_lt_two_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length) :
    (mem.wr idx.val).val < 2 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  rcases ZiskFv.AirsClean.Mem.wr_boolean_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec with
    h_wr_zero | h_wr_one
  · have h_wr_zero_mem : mem.wr idx.val = 0 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_zero
    rw [h_wr_zero_mem]
    norm_num
  · have h_wr_one_mem : mem.wr idx.val = 1 := by
      simpa [ZiskFv.AirsClean.Mem.rowAt] using h_wr_one
    rw [h_wr_one_mem]
    norm_num

/-- The indexed table bridge lifts the generated non-boundary same-address
    address-carry constraint to a concrete Mem table position. -/
theorem addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.addr idx.val = mem.addr (idx.val - 1) := by
  exact
    ZiskFv.Airs.Mem.addr_eq_previous_of_same_addr_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary

/-- On a bridged concrete Mem table row, the Clean row-spec identity
    `read_same_addr = (1 - addr_changes) * (1 - wr)` turns a read at the same
    address into the generated `read_same_addr = 1` witness. -/
theorem read_same_addr_eq_one_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0) :
    mem.read_same_addr idx.val = 1 := by
  have h_spec := rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_read_same_addr :=
    ZiskFv.AirsClean.Mem.read_same_addr_eq_of_spec
      (ZiskFv.AirsClean.Mem.rowAt mem idx.val) h_spec
  simpa [ZiskFv.AirsClean.Mem.rowAt, h_same_addr, h_read] using h_read_same_addr

/-- The indexed table bridge lifts the generated non-boundary same-address read
    value-carry constraints to a concrete Mem table position. -/
theorem values_eq_previous_of_read_same_addr_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_read_same_addr : mem.read_same_addr idx.val = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.value_0 idx.val = mem.value_0 (idx.val - 1)
      ∧ mem.value_1 idx.val = mem.value_1 (idx.val - 1) := by
  exact
    ZiskFv.Airs.Mem.values_eq_previous_of_read_same_addr_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_read_same_addr h_not_boundary

/-- Same-address reads at non-boundary bridged Mem table rows carry both value
    chunks from the previous row. This is the table-level form needed by the
    per-address prefix-read proof. -/
theorem values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    mem.value_0 idx.val = mem.value_0 (idx.val - 1)
      ∧ mem.value_1 idx.val = mem.value_1 (idx.val - 1) := by
  exact values_eq_previous_of_read_same_addr_memTableGeneratedRowsBridge
    h_bridge idx
    (read_same_addr_eq_one_of_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read)
    h_not_boundary

/-- A bridged non-boundary same-address read is byte-for-byte justified by
    replaying the previous primary row when that previous row is a write.

    This is the adjacent write→read replay step behind the per-address
    `MemoryBusRowsPrefixReadSound` induction. -/
theorem readEventReplayAgreement_after_previous_primary_write_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_read : mem.wr idx.val = 0)
    (h_previous_write : mem.wr (idx.val - 1) = 1)
    (h_not_boundary : segment.segment_l1 idx.val = 0) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memPrimaryReplayEntryOfRow
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val))) := by
  have h_addr :=
    addr_eq_previous_of_same_addr_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_not_boundary
  have h_values :=
    values_eq_previous_of_read_same_addr_row_memTableGeneratedRowsBridge
      h_bridge idx h_same_addr h_read h_not_boundary
  let writeEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem (idx.val - 1))
  let readEntry :=
    memPrimaryReplayEntryOfRow (ZiskFv.AirsClean.Mem.rowAt mem idx.val)
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    dsimp [readEntry, writeEntry]
    simp [h_addr]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.1
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    dsimp [readEntry, writeEntry]
    simpa [memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Mem.rowAt] using h_values.2
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry initialMemory writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      initialMemory h_ptr h_value_0 h_value_1
  simpa [writeEntry, readEntry, ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage,
    ZiskFv.AirsClean.Mem.rowAt, h_previous_write,
    ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent_storeEventOfEntry] using h_replay

/-- Replaying a primary write from one Mem row justifies the pinned dual read
    emitted by the same row, because the dual message has the same pointer and
    value chunks and appears after the primary emission. -/
theorem readEventReplayAgreement_after_primary_write_dual_read_of_row
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (row : ZiskFv.AirsClean.Mem.MemRow FGL)
    (h_write : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
      (ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow initialMemory
        (memPrimaryReplayEntryOfRow row))
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry
        (memDualReadReplayEntryOfRow row)) := by
  let writeEntry := memPrimaryReplayEntryOfRow row
  let readEntry := memDualReadReplayEntryOfRow row
  have h_ptr : readEntry.ptr = writeEntry.ptr := by
    simp [readEntry, writeEntry]
  have h_value_0 : readEntry.value_0 = writeEntry.value_0 := by
    simp [readEntry, writeEntry]
  have h_value_1 : readEntry.value_1 = writeEntry.value_1 := by
    simp [readEntry, writeEntry]
  have h_replay :
      ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
        (ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry initialMemory writeEntry)
        (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry readEntry) :=
    ZiskFv.ZiskCircuit.MemTrace.readEventReplayAgreement_of_writeMemoryOfEntry_same
      initialMemory h_ptr h_value_0 h_value_1
  simpa [writeEntry, readEntry, ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, ZiskFv.AirsClean.Mem.memBusMessage, h_write,
    ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent_storeEventOfEntry] using h_replay

/-- The indexed table bridge and range facts prove local chronological order
    for the active replay emissions projected from one concrete table row.

    This discharges the primary-before-dual part of the chronological proof
    from the generated Mem row and `mem.pil:397` range check. It does not claim
    full table-level `Pairwise` order across different provider rows. -/
theorem activeMemReplayEntriesOfTableRow_chronological_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayEntriesOfRow
        (eval (table.environment (table.table.get idx))
          ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)) := by
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  have h_rowAt : row = ZiskFv.AirsClean.Mem.rowAt mem idx.val := by
    dsimp [row]
    exact h_bridge.rowAt_eq idx
  have h_spec_rowAt :
      ZiskFv.AirsClean.Mem.Spec
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val) :=
    rowAt_spec_of_memTableGeneratedRowsBridge h_bridge idx
  have h_spec_row : ZiskFv.AirsClean.Mem.Spec row := by
    simpa [h_rowAt] using h_spec_rowAt
  have h_step_le_of_dual :
      row.sel_dual = 1 → row.step.val ≤ row.step_dual.val := by
    intro h_sel_dual
    have h_sel_dual_mem : mem.sel_dual idx.val = 1 := by
      simpa [h_rowAt, ZiskFv.AirsClean.Mem.rowAt] using h_sel_dual
    have h_wr_lt := wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx
    have h_step_le_rowAt :
        (ZiskFv.AirsClean.Mem.rowAt mem idx.val).step.val ≤
          (ZiskFv.AirsClean.Mem.rowAt mem idx.val).step_dual.val :=
      ZiskFv.AirsClean.Mem.rowAt_step_le_step_dual_of_dual_step_delta_range
        mem idx.val (h_ranges.stepColumns idx) h_wr_lt
        (h_ranges.dualStepDelta idx h_sel_dual_mem)
    simpa [h_rowAt] using h_step_le_rowAt
  exact activeMemReplayEntriesOfRow_chronological_of_spec_of_dual_step_le
    h_spec_row h_step_le_of_dual

/-- On a bridged non-boundary same-address Mem table position, if the previous
    `Valid_Mem` row has no dual emission, the previous primary timestamp is no
    later than the current primary timestamp. This is the adjacent-row
    cross-row ordering step behind full chronological `Pairwise` order. -/
theorem previous_primary_step_le_step_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_no_dual : mem.sel_dual (idx.val - 1) = 0) :
    (mem.step (idx.val - 1)).val ≤ (mem.step idx.val).val := by
  exact
    ZiskFv.Airs.Mem.previous_primary_step_le_step_of_same_addr_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary
      (h_ranges.stepColumns idx)
      (wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx)
      (h_ranges.incrementChunks idx) h_no_dual

/-- On a bridged non-boundary same-address Mem table position, if the previous
    `Valid_Mem` row has a dual emission, the previous dual timestamp is no
    later than the current primary timestamp. This is the dual predecessor case
    for adjacent-row chronological order. -/
theorem previous_dual_step_le_step_of_memTableGeneratedRowsBridge
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {rowCount : ℕ}
    (h_bridge : MemTableGeneratedRowsBridge table mem segment permutation rowCount)
    (h_ranges : MemTableGeneratedRangeFacts table mem)
    (idx : Fin table.table.length)
    (h_same_addr : mem.addr_changes idx.val = 0)
    (h_not_boundary : segment.segment_l1 idx.val = 0)
    (h_dual : mem.sel_dual (idx.val - 1) = 1) :
    (mem.step_dual (idx.val - 1)).val ≤ (mem.step idx.val).val := by
  exact
    ZiskFv.Airs.Mem.previous_dual_step_le_step_of_same_addr_not_boundary_segment_every_row
      (cols := segment) (v := mem) (row := idx.val)
      (h_bridge.generatedAt idx).1 h_same_addr h_not_boundary
      (h_ranges.stepColumns idx)
      (wr_val_lt_two_of_memTableGeneratedRowsBridge h_bridge idx)
      (h_ranges.incrementChunks idx) h_dual

/-- Row-order facts for the concrete mutable-Mem replay projection. This is
    the table-local target that accepted full-execution integration should
    prove from Mem sorting, segment carry, and timestamp range facts.

    The target intentionally does not require `Nodup`: the Mem PIL allows
    equal-timestamp read/read dual rows, and identical duplicate reads are
    harmless for replay because reads do not mutate memory. -/
structure MemReplayRowsOfTableOrderFacts
    (table : Table FGL) : Prop where
  chronologicalRows :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (memReplayRowsOfTable table)

/-- Prefix-read soundness for the concrete mutable-Mem replay projection.
    Proving this is the memory-continuity part of the accepted Mem trace
    bridge, after the replay row list has been identified with the concrete
    table projection. -/
def MemReplayRowsOfTablePrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
    initialMemory (memReplayRowsOfTable table)

/-- Row-order facts for the active mutable-Mem replay projection. This is the
    sound chronological target: inactive selector-gated emissions are not
    replay events.  As above, duplicate read entries are permitted. -/
structure ActiveMemReplayRowsOfTableOrderFacts
    (table : Table FGL) : Prop where
  chronologicalRows :
    ZiskFv.AirsClean.Mem.MemoryBusRowsChronological
      (activeMemReplayRowsOfTable table)

/-- Prefix-read soundness for the active mutable-Mem replay projection. -/
def ActiveMemReplayRowsOfTablePrefixReadSound
    (initialMemory : Std.ExtHashMap Nat (BitVec 8))
    (table : Table FGL) : Prop :=
  ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
    initialMemory (activeMemReplayRowsOfTable table)

/-- Transport table-local replay-row order facts across the concrete row-list
    equality used by the raw accepted Mem extraction path. -/
theorem generatedMemRowOrderFacts_of_memReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = memReplayRowsOfTable table)
    (h_order : MemReplayRowsOfTableOrderFacts table) :
    ZiskFv.AirsClean.Mem.GeneratedMemRowOrderFacts rows := by
  rw [h_rows]
  exact
    { chronologicalRows := h_order.chronologicalRows }

/-- Transport table-local prefix-read soundness across the concrete row-list
    equality used by the raw accepted Mem extraction path. -/
theorem memoryBusRowsPrefixReadSound_of_memReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {initialMemory : Std.ExtHashMap Nat (BitVec 8)}
    (h_rows : rows = memReplayRowsOfTable table)
    (h_prefix : MemReplayRowsOfTablePrefixReadSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      initialMemory rows := by
  rw [h_rows]
  exact h_prefix

/-- Transport table-local active replay-row order facts across the concrete
    row-list equality used by the raw accepted Mem extraction path. -/
theorem generatedMemRowOrderFacts_of_activeMemReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_order : ActiveMemReplayRowsOfTableOrderFacts table) :
    ZiskFv.AirsClean.Mem.GeneratedMemRowOrderFacts rows := by
  rw [h_rows]
  exact
    { chronologicalRows := h_order.chronologicalRows }

/-- Transport table-local active prefix-read soundness across the concrete
    row-list equality used by the raw accepted Mem extraction path. -/
theorem memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {initialMemory : Std.ExtHashMap Nat (BitVec 8)}
    (h_rows : rows = activeMemReplayRowsOfTable table)
    (h_prefix : ActiveMemReplayRowsOfTablePrefixReadSound initialMemory table) :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      initialMemory rows := by
  rw [h_rows]
  exact h_prefix

/-- The projected read-replay rows of a concrete Mem table are embedded in
    the accepted chronological memory-bus row trace. Proving this embedding
    is the global AIR/Main/Mem integration obligation; selected-row coverage
    can then be discharged from the table-local projection lemmas below. -/
def MemReadReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ memReadReplayRowsOfTable table → entry ∈ rows

/-- The projected read/write replay rows of a concrete Mem table are embedded
    in the accepted chronological memory-bus row trace. This is the stronger
    table-level embedding needed by global memory replay: writes must be
    present in the chronological trace so store replay can update memory. -/
def MemReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ memReplayRowsOfTable table → entry ∈ rows

/-- Active read/write replay rows of a concrete Mem table are embedded in the
    accepted chronological memory-bus row trace. -/
def ActiveMemReplayRowsEmbeddedInTrace
    (table : Table FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ entry, entry ∈ activeMemReplayRowsOfTable table → entry ∈ rows

/-- If the accepted chronological row list is definitionally supplied by the
    concrete mutable-Mem table replay projection, then all projected replay
    rows are embedded in that trace. This is the structural projection lemma
    used before proving the harder chronological/replay facts. -/
theorem memReplayRowsEmbeddedInTrace_of_rows_eq
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = memReplayRowsOfTable table) :
    MemReplayRowsEmbeddedInTrace table rows := by
  intro entry h_entry
  rw [h_rows]
  exact h_entry

/-- If the accepted chronological row list is definitionally supplied by the
    active mutable-Mem table replay projection, then all active projected
    replay rows are embedded in that trace. -/
theorem activeMemReplayRowsEmbeddedInTrace_of_rows_eq
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    (h_rows : rows = activeMemReplayRowsOfTable table) :
    ActiveMemReplayRowsEmbeddedInTrace table rows := by
  intro entry h_entry
  rw [h_rows]
  exact h_entry

/-- Witness-level embedding obligation for mutable Mem tables. Accepted
    full-execution integration should prove this from the chronological
    AIR/Main/Mem trace: every dual-aware mutable Mem table in the full
    ensemble witness has its projected read-replay rows embedded in the
    accepted chronological memory row list. -/
def MutableMemReadReplayRowsEmbeddedInTrace
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
      MemReadReplayRowsEmbeddedInTrace table rows

/-- Witness-level embedding obligation for all mutable-Mem replay rows,
    including primary writes. This is the trace/table projection needed before
    accepted full execution can prove chronological memory replay, while the
    older read-only embedding remains available for selected-load coverage. -/
def MutableMemReplayRowsEmbeddedInTrace
    {length : ℕ} {program : Program length}
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (rows : List (Interaction.MemoryBusEntry FGL)) : Prop :=
  ∀ table : Table FGL,
    table ∈ witness.allTables →
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus →
      MemReplayRowsEmbeddedInTrace table rows

/-- A primary read projection is the polarity-preserving primary replay row
    when the concrete Mem row is a read. -/
theorem memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 0) :
    memPrimaryReadReplayEntryOfRow row = memPrimaryReplayEntryOfRow row := by
  simp [memPrimaryReadReplayEntryOfRow, memPrimaryReplayEntryOfRow, h_wr]

/-- A primary polarity-preserving replay row is a legacy read row when
    `wr = 0`. -/
theorem memoryBusTraceEventOfRow_memPrimaryReplayEntryOfRow_read_of_wr_zero
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 0) :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow
      (memPrimaryReplayEntryOfRow row) =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.read
          (memPrimaryReplayEntryOfRow row)) := by
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow,
    memPrimaryReplayEntryOfRow, h_wr]

/-- A primary polarity-preserving replay row is a legacy write row when
    `wr = 1`. -/
theorem memoryBusTraceEventOfRow_memPrimaryReplayEntryOfRow_write_of_wr_one
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow
      (memPrimaryReplayEntryOfRow row) =
        some (ZiskFv.ZiskCircuit.MemTrace.MemoryBusTraceEvent.write
          (memPrimaryReplayEntryOfRow row)) := by
  have h_one_ne_neg_one : ¬((1 : FGL) = (-1 : FGL)) := by
    native_decide
  simp [ZiskFv.ZiskCircuit.MemTrace.memoryBusTraceEventOfRow,
    memPrimaryReplayEntryOfRow, h_wr, h_one_ne_neg_one]

/-- On primary Mem writes, the raw-row replay step is exactly the store
    update carried by the polarity-preserving primary replay entry. -/
theorem replayMemoryAfterBusRow_memPrimaryReplayEntryOfRow_of_wr_one
    (mem : Std.ExtHashMap Nat (BitVec 8))
    {row : ZiskFv.AirsClean.Mem.MemRow FGL}
    (h_wr : row.wr = 1) :
    ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow
      mem (memPrimaryReplayEntryOfRow row) =
        ZiskFv.ZiskCircuit.MemTrace.replayStoreEvent mem
          (ZiskFv.ZiskCircuit.MemTrace.storeEventOfEntry
            (memPrimaryReplayEntryOfRow row)) := by
  simp [ZiskFv.ZiskCircuit.MemTrace.replayMemoryAfterBusRow,
    memPrimaryReplayEntryOfRow, h_wr]

/-- A concrete Mem table row contributes its primary polarity-preserving
    projection to the table's full replay-row surface. -/
theorem mem_primary_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReplayRowsOfTable table := by
  unfold memReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its primary
    polarity-preserving projection to the table's active replay-row surface. -/
theorem active_mem_primary_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1) :
    memPrimaryReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReplayRowsOfTable table := by
  unfold activeMemReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReplayEntriesOfRow, h_sel]⟩

/-- A concrete Mem table row contributes its dual read projection to the
    table's full replay-row surface. -/
theorem mem_dual_read_replay_entry_mem_of_replay_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReplayRowsOfTable table := by
  unfold memReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its dual read projection to
    the table's active replay-row surface. -/
theorem active_mem_dual_read_replay_entry_mem_of_replay_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReplayRowsOfTable table := by
  unfold activeMemReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReplayEntriesOfRow, h_sel_dual]⟩

/-- The all-replay-row embedding implies read-only embedding for selected
    primary reads, once the selected Mem row is known to be a read. -/
theorem mem_primary_read_replay_entry_mem_of_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows := by
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (mem_primary_replay_entry_mem_of_table_row h_row)

/-- Active replay-row embedding implies read-only embedding for selected
    primary reads, once the selected Mem row is known to be a read and active. -/
theorem mem_primary_read_replay_entry_mem_of_active_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows := by
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (active_mem_primary_replay_entry_mem_of_table_row h_row h_sel)

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace from active replay-row embedding, provided the
    concrete Mem row is selected and is a read. -/
theorem mem_primary_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact
    mem_primary_read_replay_entry_mem_of_active_replay_embedded_table_row
      h_embedded h_row h_sel h_wr

/-- The all-replay-row embedding directly implies dual-read embedding. -/
theorem mem_dual_read_replay_entry_mem_of_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows :=
  h_embedded _
    (mem_dual_read_replay_entry_mem_of_replay_table_row h_row)

/-- Active replay-row embedding directly implies selected dual-read
    embedding. -/
theorem mem_dual_read_replay_entry_mem_of_active_replay_embedded_table_row
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ rows :=
  h_embedded _
    (active_mem_dual_read_replay_entry_mem_of_replay_table_row
      h_row h_sel_dual)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace from active replay-row embedding, provided the
    concrete dual emission is selected. -/
theorem mem_dual_read_replay_entry_mem_of_active_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : ActiveMemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact
    mem_dual_read_replay_entry_mem_of_active_replay_embedded_table_row
      h_embedded h_row h_sel_dual

/-- A concrete Mem table row contributes its primary read projection to the
    table's read-replay row surface. -/
theorem mem_primary_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReadReplayRowsOfTable table := by
  unfold memReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReadReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its primary read projection
    to the table's active read-replay row surface. -/
theorem active_mem_primary_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel = 1) :
    memPrimaryReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReadReplayRowsOfTable table := by
  unfold activeMemReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReadReplayEntriesOfRow, h_sel]⟩

/-- A concrete Mem table row contributes its dual read projection to the
    table's read-replay row surface. -/
theorem mem_dual_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ memReadReplayRowsOfTable table := by
  unfold memReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by simp [memReadReplayEntriesOfRow]⟩

/-- A selected concrete Mem table row contributes its dual read projection to
    the table's active read-replay row surface. -/
theorem active_mem_dual_read_replay_entry_mem_of_table_row
    {table : Table FGL} {providerRow : Array FGL}
    (h_row : providerRow ∈ table.table)
    (h_sel_dual :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).sel_dual = 1) :
    memDualReadReplayEntryOfRow
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar)
      ∈ activeMemReadReplayRowsOfTable table := by
  unfold activeMemReadReplayRowsOfTable
  exact List.mem_flatMap.mpr
    ⟨providerRow, h_row, by
      simp [activeMemReadReplayEntriesOfRow, h_sel_dual]⟩

/-- If a selected legacy memory row matches a concrete primary Mem row's
    read projection, then it is covered by the table's read-replay rows. -/
theorem mem_primary_read_replay_entry_mem_of_table_row_match
    {table : Table FGL} {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ memReadReplayRowsOfTable table := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact mem_primary_read_replay_entry_mem_of_table_row h_row

/-- If a selected legacy memory row matches a concrete dual Mem row's read
    projection, then it is covered by the table's read-replay rows. -/
theorem mem_dual_read_replay_entry_mem_of_table_row_match
    {table : Table FGL} {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ memReadReplayRowsOfTable table := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact mem_dual_read_replay_entry_mem_of_table_row h_row

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace once the table's projected replay rows are
    embedded in that trace. -/
theorem mem_primary_read_replay_entry_mem_of_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReadReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows :=
  h_embedded entry
    (mem_primary_read_replay_entry_mem_of_table_row_match h_row h_match)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace once the table's projected replay rows are
    embedded in that trace. -/
theorem mem_dual_read_replay_entry_mem_of_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReadReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows :=
  h_embedded entry
    (mem_dual_read_replay_entry_mem_of_table_row_match h_row h_match)

/-- A matched primary Mem provider read projection is covered by the accepted
    chronological row trace from the stronger replay-row embedding, provided
    the concrete Mem row is a read. This is the selected-load adapter needed
    to avoid requiring every primary Mem row, including writes, to appear in
    the accepted trace with read polarity. -/
theorem mem_primary_read_replay_entry_mem_of_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_wr :
      (eval (table.environment providerRow)
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar).wr = 0)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memPrimaryReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memPrimaryReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  rw [memPrimaryReadReplayEntryOfRow_eq_primaryReplayEntryOfRow_of_wr_zero
    h_wr]
  exact h_embedded _
    (mem_primary_replay_entry_mem_of_table_row h_row)

/-- A matched dual Mem provider read projection is covered by the accepted
    chronological row trace from the stronger replay-row embedding. Dual Mem
    projections are always read events in the replay surface. -/
theorem mem_dual_read_replay_entry_mem_of_replay_embedded_trace_row_match
    {table : Table FGL}
    {rows : List (Interaction.MemoryBusEntry FGL)}
    {providerRow : Array FGL}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_embedded : MemReplayRowsEmbeddedInTrace table rows)
    (h_row : providerRow ∈ table.table)
    (h_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry entry
        (memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar))) :
    entry ∈ rows := by
  have h_eq :
      entry =
        memDualReadReplayEntryOfRow
          (eval (table.environment providerRow)
            ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar) := by
    obtain ⟨h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
    cases entry
    simp [memDualReadReplayEntryOfRow,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
      at h_mult h_as h_ptr h_v0 h_v1 h_ts ⊢
    rw [h_mult, h_as, h_ptr, h_v0, h_v1, h_ts]
    simp
  rw [h_eq]
  exact h_embedded _
    (mem_dual_read_replay_entry_mem_of_replay_table_row h_row)

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
