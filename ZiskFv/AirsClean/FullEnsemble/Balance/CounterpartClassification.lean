import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

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
            ∧ (table.component = arithMulProviderComponent
              ∨ table.component = shiftStaticLookupComponent
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
            ∧ (table.component = arithMulProviderComponent
              ∨ table.component = shiftStaticLookupComponent
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


end ZiskFv.AirsClean.FullEnsemble
