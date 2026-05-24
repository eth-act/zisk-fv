import ZiskFv.AirsClean.BinaryFamily.Ensemble

/-!
# Binary-family operation-bus balance projections

Small C7 bridge lemmas that expose the Clean ensemble's balanced
`OpBusChannel` fact in the form needed by the later `matches_entry`
replacement proofs.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.BinaryFamily

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus

/-- The concrete component list in the Binary-family ensemble. Kept as a
    small standalone lemma because dependent component equalities are fragile
    when case-split in larger balance proofs. -/
theorem component_mem_binaryFamily_cases
    {component : Component FGL}
    (h_mem : component ∈ binaryFamilyOpBusEnsemble.ensemble.allTables) :
    component = binaryFamilyOpBusEnsemble.ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.Main.component
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component = ZiskFv.AirsClean.Binary.component
      ∨ component = ZiskFv.AirsClean.BinaryExtension.component := by
  simp [binaryFamilyOpBusEnsemble, SoundEnsemble.toFormal, Ensemble.allTables,
    SoundEnsemble.addTable_tables, SoundEnsemble.addFinishedChannel_tables] at h_mem
  rcases h_mem with h_verifier | h_binaryExtension | h_binary | h_binaryAdd | h_main | h_empty
  · exact Or.inl h_verifier
  · exact Or.inr (Or.inr (Or.inr (Or.inr h_binaryExtension)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_binary)))
  · exact Or.inr (Or.inr (Or.inl h_binaryAdd))
  · exact Or.inr (Or.inl h_main)
  · cases h_empty

/-- The Binary-family verifier table is the empty verifier component, so it
    cannot contribute operation-bus interactions. -/
theorem verifierTable_interactionsWith_opBus_nil :
    binaryFamilyOpBusEnsemble.ensemble.verifierTable.operations.interactionsWith
      OpBusChannel.toRaw = [] := by
  simp [binaryFamilyOpBusEnsemble, SoundEnsemble.toFormal,
    Ensemble.verifierTable_interactionsWith, Ensemble.verifierOperations,
    GeneralFormalCircuit.empty, circuit_norm]

/-- If a table's operation-bus abstract interactions are a singleton, any
    concrete table-level interaction on that channel is that singleton
    evaluated at some row. -/
theorem exists_row_eval_of_singleton_interactionsWith
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

/-- Row extraction for a Main operation-bus interaction. -/
theorem exists_main_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_main : table.component = ZiskFv.AirsClean.Main.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.emitted
          (-ZiskFv.AirsClean.Main.component.rowInputVar.is_external_op)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            ZiskFv.AirsClean.Main.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_main] using ZiskFv.AirsClean.Main.component_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a BinaryAdd operation-bus provider interaction. -/
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
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using ZiskFv.AirsClean.BinaryAdd.component_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a Binary operation-bus provider interaction. -/
theorem exists_binary_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.Binary.opBusMessageExpr
            ZiskFv.AirsClean.Binary.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using ZiskFv.AirsClean.Binary.component_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a BinaryExtension operation-bus provider interaction. -/
theorem exists_binaryExtension_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.BinaryExtension.component)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            ZiskFv.AirsClean.BinaryExtension.component.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryExtension.component_interactionsWith_opBus
  · exact h_mem

/-- Project the Binary-family ensemble's `BalancedChannels` hypothesis to
    the concrete operation-bus interaction list. -/
theorem opBus_balanced_of_witness
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels) :
    BalancedInteractions (witness.interactionsWith OpBusChannel.toRaw) := by
  have h := h_balanced OpBusChannel.toRaw (by
    change OpBusChannel.toRaw ∈ [OpBusChannel.toRaw]
    simp)
  simpa [EnsembleWitness.BalancedChannel,
    EnsembleWitness.interactionsWith_allTablesWitness] using h

/-- Clean balance gives the first replacement shape for the old op-bus
    permutation axiom: an active Main-side interaction (`mult = -1`) has a
    same-message counterpart whose multiplicity is neither a pull nor an
    inactive zero row. Later C7 lemmas specialize the counterpart to one of
    the Binary-family provider components using the component
    interaction-shape lemmas. -/
theorem exists_matching_nonzero_nonpull_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
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

/-- Compatibility projection for existing C7 callers that only need the
    older non-pull shape. -/
theorem exists_matching_nonpull_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1 := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, _h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_interaction witness h_balanced h_mem h_active
  exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull⟩

/-- A constrained Main table can only contribute operation-bus interactions
    with multiplicity `-1` (active row) or `0` (inactive row). -/
theorem main_table_opBus_mult_neg_one_or_zero_of_constraints
    {table : Table FGL}
    (h_constraints : table.Constraints)
    (h_main : table.component = ZiskFv.AirsClean.Main.component) :
    ∀ {interaction : Interaction FGL},
      interaction ∈ table.interactionsWith OpBusChannel.toRaw →
      interaction.mult = -1 ∨ interaction.mult = 0 := by
  intro interaction h_interaction
  refine ((Table.forall_interactionsWith_iff table OpBusChannel.toRaw
    (fun interaction => interaction.mult = -1 ∨ interaction.mult = 0)).mpr ?_)
    interaction h_interaction
  intro row h_row abstractInteraction h_abs h_channel
  have h_abs_with :
      abstractInteraction ∈ table.component.operations.interactionsWith OpBusChannel.toRaw := by
    simp [Operations.interactionsWith, h_abs, h_channel]
  have h_main_interactions :
      table.component.operations.interactionsWith OpBusChannel.toRaw =
        [((OpBusChannel.emitted
            (-ZiskFv.AirsClean.Main.component.rowInputVar.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              ZiskFv.AirsClean.Main.component.rowInputVar)).toRaw)] := by
    simpa [h_main] using ZiskFv.AirsClean.Main.component_interactionsWith_opBus
  have h_abs_eq :
      abstractInteraction =
        ((OpBusChannel.emitted
            (-ZiskFv.AirsClean.Main.component.rowInputVar.is_external_op)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              ZiskFv.AirsClean.Main.component.rowInputVar)).toRaw) := by
    simpa [h_main_interactions] using h_abs_with
  subst abstractInteraction
  have h_bool :=
    ZiskFv.AirsClean.Main.is_external_op_boolean_of_component_constraints
      (table.environment row) (by simpa [h_main] using h_constraints row h_row)
  let x := (table.environment row)
    ZiskFv.AirsClean.Main.component.rowInputVar.is_external_op
  have h_mul_raw : x * (1 + -1 * x) = 0 := by
    simpa [Expression.eval, x] using h_bool
  have h_mul : x * (1 - x) = 0 := by
    convert h_mul_raw using 1
    ring
  rcases mul_eq_zero.mp h_mul with h_zero | h_one_sub
  · right
    change Expression.eval (table.environment row)
      (-ZiskFv.AirsClean.Main.component.rowInputVar.is_external_op) = 0
    simp [Expression.eval, x, h_zero]
  · left
    have h_one : x = 1 := (sub_eq_zero.mp h_one_sub).symm
    change Expression.eval (table.environment row)
      (-ZiskFv.AirsClean.Main.component.rowInputVar.is_external_op) = -1
    simp [Expression.eval, x, h_one]

/-- Classify the nonzero non-pull counterpart supplied by balance as not
    coming from the Main component, provided Main rows have already been
    locally ruled out as nonzero non-pulls.

This is the next C7 bridge layer. The Main local-shape obligation is derived
from `witness.Constraints`, not supplied by the caller. -/
theorem exists_matching_nonMain_component_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
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
            ∧ table.component ≠ ZiskFv.AirsClean.Main.component := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero⟩ :=
    exists_matching_nonzero_nonpull_of_active_main_interaction
      witness h_balanced h_mem h_active
  rw [EnsembleWitness.mem_interactionsWith] at h_mem_provider
  obtain ⟨table, h_table, h_mem_table⟩ := h_mem_provider
  have h_not_main : table.component ≠ ZiskFv.AirsClean.Main.component := by
    intro h_main
    have h_mult := main_table_opBus_mult_neg_one_or_zero_of_constraints
      (h_constraints table h_table) h_main h_mem_table
    rcases h_mult with h_neg | h_zero
    · exact h_nonpull h_neg
    · exact h_nonzero h_zero
  refine ⟨providerInteraction, ?_, h_msg, h_nonpull, h_nonzero, table, h_table,
    h_mem_table, h_not_main⟩
  rw [EnsembleWitness.mem_interactionsWith]
  exact ⟨table, h_table, h_mem_table⟩

/-- Provider classification for the balanced same-message counterpart:
    after verifier/Main exclusion, it must come from one of the three
    Binary-family provider components. -/
theorem exists_matching_provider_component_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
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
            ∧ (table.component = ZiskFv.AirsClean.BinaryAdd.component
              ∨ table.component = ZiskFv.AirsClean.Binary.component
              ∨ table.component = ZiskFv.AirsClean.BinaryExtension.component) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, h_not_main⟩ :=
    exists_matching_nonMain_component_of_active_main_interaction
      witness h_constraints h_balanced h_mem h_active
  have h_component_mem :
      table.component ∈ binaryFamilyOpBusEnsemble.ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_binaryFamily_cases h_component_mem with
    h_verifier | h_main | h_binaryAdd | h_binary | h_binaryExtension
  · have h_nil :
        table.interactionsWith OpBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith OpBusChannel.toRaw = [] := by
        simpa [h_verifier] using verifierTable_interactionsWith_opBus_nil
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · exact False.elim (h_not_main h_main)
  · exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inl h_binaryAdd⟩
  · exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inl h_binary)⟩
  · exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inr h_binaryExtension)⟩

end ZiskFv.AirsClean.BinaryFamily
