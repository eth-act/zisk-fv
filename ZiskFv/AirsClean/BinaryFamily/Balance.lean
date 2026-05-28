import ZiskFv.AirsClean.BinaryFamily.Ensemble
import ZiskFv.AirsClean.Binary.Bridge

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

/-- Component classification for the lookup-aware Binary-family ensemble. -/
theorem component_mem_binaryFamilyStatic_cases
    {component : Component FGL}
    (h_mem :
      component ∈ binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble.allTables) :
    component = binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble.verifierTable
      ∨ component = ZiskFv.AirsClean.Main.component
      ∨ component = ZiskFv.AirsClean.BinaryAdd.component
      ∨ component = ZiskFv.AirsClean.Binary.staticLookupComponent
      ∨ component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent := by
  simp [binaryFamilyStaticBinaryTableOpBusEnsemble, SoundEnsemble.toFormal,
    Ensemble.allTables, SoundEnsemble.addTable_tables,
    SoundEnsemble.addFinishedChannel_tables] at h_mem
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

theorem staticVerifierTable_interactionsWith_opBus_nil :
    binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble.verifierTable.operations.interactionsWith
      OpBusChannel.toRaw = [] := by
  simp [binaryFamilyStaticBinaryTableOpBusEnsemble, SoundEnsemble.toFormal,
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

/-- Row extraction for a lookup-aware Binary operation-bus provider interaction. -/
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
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.Binary.staticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Table-spec projection for the lookup-aware Binary provider: the same
    concrete Clean row used for the op-bus interaction supplies both Binary's
    algebraic core facts and the static BinaryTable semantic facts. -/
theorem staticBinary_core_and_wf_of_table_spec
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_spec : table.Spec)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ZiskFv.Airs.Binary.core_every_row
        (ZiskFv.AirsClean.Binary.validOfRow
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (table.environment row))) 0
      ∧ ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts
          (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
            (table.environment row)) := by
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (table.environment row) := by
    simpa [h_component] using h_spec row h_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  obtain ⟨h_core_spec, h_static_specs⟩ := h_component_spec
  exact ⟨ ZiskFv.AirsClean.Binary.core_every_row_of_spec _ h_core_spec
        , ZiskFv.AirsClean.Binary.static_table_wf_facts_of_spec_facts _ h_static_specs ⟩

/-- Sibling of `staticBinary_core_and_wf_of_table_spec` exposing the raw
    `StaticBinaryTableSpecFacts` (exact static-table memberships for the 8
    per-byte entries). Needed by the W-mode dispatch to apply
    `spec_op_val_ne_W_add_sub` and exclude the (mode32 = 0, b_op = op_emit)
    decomposition of the op-bus emission. -/
theorem staticBinary_spec_facts_of_table_spec
    {table : Table FGL}
    (h_component : table.component = ZiskFv.AirsClean.Binary.staticLookupComponent)
    (h_spec : table.Spec)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts
      (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
        (table.environment row)) := by
  have h_component_spec :
      ZiskFv.AirsClean.Binary.staticLookupComponent.Spec
        (table.environment row) := by
    simpa [h_component] using h_spec row h_row
  rw [ZiskFv.AirsClean.Binary.staticLookupComponent_spec] at h_component_spec
  exact h_component_spec.2

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

/-- Row extraction for a lookup-aware BinaryExtension operation-bus provider
    interaction. -/
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
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryExtension.staticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Row extraction for a shift-range lookup-aware BinaryExtension
    operation-bus provider interaction. -/
theorem exists_shiftStaticBinaryExtension_row_eval_of_interaction_mem
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    {interaction : Interaction FGL}
    (h_mem : interaction ∈ table.interactionsWith OpBusChannel.toRaw) :
    ∃ row ∈ table.table,
      interaction =
        ((OpBusChannel.pushed
          (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
            ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInputVar)).toRaw).eval
          (table.environment row) := by
  apply exists_row_eval_of_singleton_interactionsWith
  · simpa [h_component] using
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_interactionsWith_opBus
  · exact h_mem

/-- Table-spec projection for the lookup-aware BinaryExtension provider: the
    same Clean row used for the op-bus interaction supplies the eight static
    BinaryExtensionTable facts. -/
theorem staticBinaryExtension_wf_of_table_spec
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent)
    (h_spec : table.Spec)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts
      (ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInput
        (table.environment row)) := by
  have h_component_spec :
      ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.Spec
        (table.environment row) := by
    simpa [h_component] using h_spec row h_row
  rw [ZiskFv.AirsClean.BinaryExtension.staticLookupComponent_spec] at h_component_spec
  exact ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts _
    h_component_spec.2

/-- Table-spec projection for the shift-range lookup-aware BinaryExtension
    provider. It exposes the same eight static BinaryExtensionTable facts as
    `staticBinaryExtension_wf_of_table_spec`, plus the selected
    `b_0 < 2^24` PIL range-check carried by the stricter shift component. -/
theorem shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_spec : table.Spec)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts
      (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
        (table.environment row))
      ∧ ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact
          (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
            (table.environment row)) := by
  have h_component_spec :
      ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.Spec
        (table.environment row) := by
    simpa [h_component] using h_spec row h_row
  rw [ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent_spec] at h_component_spec
  exact ⟨ZiskFv.AirsClean.BinaryExtension.static_table_wf_facts_of_spec_facts _
      h_component_spec.2.1, h_component_spec.2.2⟩

/-- Convenience projection for consumers that only need the shift-selected
    `b_0 < 2^24` range fact. -/
theorem shiftStaticBinaryExtension_b0_range_of_table_spec
    {table : Table FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent)
    (h_spec : table.Spec)
    {row : Array FGL} (h_row : row ∈ table.table) :
    ZiskFv.AirsClean.BinaryExtension.ShiftB0RangeSpecFact
      (ZiskFv.AirsClean.BinaryExtension.shiftStaticLookupComponent.rowInput
        (table.environment row)) :=
  (shiftStaticBinaryExtension_wf_and_b0_range_of_table_spec
    h_component h_spec h_row).2

/-- A lookup-aware BinaryExtension provider row cannot match a bitwise
    Binary opcode (`AND`/`OR`/`XOR`, opcode values 14/15/16). The exclusion is
    derived from the provider row's own static BinaryExtensionTable facts. -/
theorem staticBinaryExtension_matches_entry_ne_bitwise
    {mainEntry : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {table : Table FGL} {row : Array FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.BinaryExtension.staticLookupComponent)
    (h_spec : table.Spec) (h_row : row ∈ table.table)
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry mainEntry
        (OpBusMessage.toEntry
          (eval (table.environment row)
            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
              ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInputVar)) 1))
    (h_main_op :
      mainEntry.op.val = 14 ∨ mainEntry.op.val = 15 ∨ mainEntry.op.val = 16) :
    False := by
  have h_component_spec :
      ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.Spec
        (table.environment row) := by
    simpa [h_component] using h_spec row h_row
  have h_ne :=
    ZiskFv.AirsClean.BinaryExtension.staticLookupComponent_op_val_ne_bitwise_of_spec
      (table.environment row) h_component_spec
  have h_match_op := h_match.2.1
  have h_provider_op :
      mainEntry.op.val =
        (ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInput
          (table.environment row)).flags.op.val := by
    rw [h_match_op]
    exact congrArg Fin.val
      (ZiskFv.AirsClean.BinaryExtension.staticLookupComponent_eval_opBusMessageExpr_op
        (table.environment row))
  rcases h_main_op with h14 | h15 | h16
  · exact h_ne.1 (by rw [← h_provider_op, h14])
  · exact h_ne.2.1 (by rw [← h_provider_op, h15])
  · exact h_ne.2.2 (by rw [← h_provider_op, h16])

/-- BinaryAdd's provider message has opcode 10, so it cannot match a bitwise
    Binary opcode (`AND`/`OR`/`XOR`, values 14/15/16). -/
theorem binaryAdd_matches_entry_ne_bitwise
    {mainEntry : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {env : Environment FGL}
    (h_match :
      ZiskFv.Airs.OperationBus.matches_entry mainEntry
        (OpBusMessage.toEntry
          (eval env
            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
    (h_main_op :
      mainEntry.op.val = 14 ∨ mainEntry.op.val = 15 ∨ mainEntry.op.val = 16) :
    False := by
  have h_match_op := h_match.2.1
  have h_provider_op : mainEntry.op.val = 10 := by
    rw [h_match_op]
    change (eval env
      (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
        ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)).op.val = 10
    rw [OpBusMessage.eval_op]
    rfl
  rcases h_main_op with h14 | h15 | h16 <;> omega

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

theorem staticOpBus_balanced_of_witness
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
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

theorem exists_static_matching_nonzero_nonpull_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
    (h_balanced : witness.BalancedChannels)
    {mainInteraction : Interaction FGL}
    (h_mem : mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
      providerInteraction.msg = mainInteraction.msg
        ∧ providerInteraction.mult ≠ -1
        ∧ providerInteraction.mult ≠ 0 := by
  exact exists_nonzero_push_of_pull (witness.interactionsWith OpBusChannel.toRaw)
    (staticOpBus_balanced_of_witness witness h_balanced)
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

theorem exists_static_matching_nonMain_component_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
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
    exists_static_matching_nonzero_nonpull_of_active_main_interaction
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

theorem exists_static_matching_provider_component_of_active_main_interaction
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
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
              ∨ table.component = ZiskFv.AirsClean.Binary.staticLookupComponent
              ∨ table.component =
                  ZiskFv.AirsClean.BinaryExtension.staticLookupComponent) := by
  obtain ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, h_not_main⟩ :=
    exists_static_matching_nonMain_component_of_active_main_interaction
      witness h_constraints h_balanced h_mem h_active
  have h_component_mem :
      table.component ∈ binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble.allTables :=
    EnsembleWitness.mem_allTables_component_of_mem_allTables h_table
  rcases component_mem_binaryFamilyStatic_cases h_component_mem with
    h_verifier | h_main | h_binaryAdd | h_binary | h_binaryExtension
  · have h_nil :
        table.interactionsWith OpBusChannel.toRaw = [] := by
      have h_ops_nil :
          table.component.operations.interactionsWith OpBusChannel.toRaw = [] := by
        simpa [h_verifier] using staticVerifierTable_interactionsWith_opBus_nil
      simp [Table.interactionsWith, Operations.interactionValuesWith_eq_map, h_ops_nil]
    simp [h_nil] at h_mem_table
  · exact False.elim (h_not_main h_main)
  · exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inl h_binaryAdd⟩
  · exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inl h_binary)⟩
  · exact ⟨providerInteraction, h_mem_provider, h_msg, h_nonpull, h_nonzero,
      table, h_table, h_mem_table, Or.inr (Or.inr h_binaryExtension)⟩

/-- Row-native C7 projection: an active Main table interaction has a
    balanced provider row whose evaluated Clean operation-bus message matches
    the evaluated Main message as a legacy `matches_entry`.

This is deliberately stated over Clean `Table` rows/environments, not over
legacy `Valid_*` row accessors. The remaining provider disjunction mirrors the
three Binary-family provider components. -/
theorem exists_provider_row_matches_entry_of_active_main_table_interaction
    (witness : EnsembleWitness binaryFamilyOpBusEnsemble.ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent : mainTable.component = ZiskFv.AirsClean.Main.component)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
        providerInteraction.msg = mainInteraction.msg
          ∧ providerInteraction.mult ≠ -1
          ∧ providerInteraction.mult ≠ 0
          ∧ ∃ providerTable ∈ witness.allTables,
            providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
              ∧
              ((∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                    ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                        (OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.Binary.component
                    ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                        (OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Binary.opBusMessageExpr
                              ZiskFv.AirsClean.Binary.component.rowInputVar)) 1))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.BinaryExtension.component
                    ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                        (OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryExtension.component.rowInputVar)) 1))) := by
  have h_main_mem_witness :
      mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_matching_provider_component_of_active_main_interaction
      witness h_constraints h_balanced h_main_mem_witness h_active
  refine ⟨mainRow, h_mainRow, providerInteraction, h_provider_witness, h_msg,
    h_nonpull, h_nonzero, providerTable, h_providerTable,
    h_providerInteraction, ?_⟩
  rcases h_providerComponent with h_binaryAdd | h_binary | h_binaryExtension
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binaryAdd_row_eval_of_interaction_mem h_binaryAdd h_providerInteraction
    left
    refine ⟨providerRow, h_providerRow, h_binaryAdd, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binary_row_eval_of_interaction_mem h_binary h_providerInteraction
    right
    left
    refine ⟨providerRow, h_providerRow, h_binary, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binaryExtension_row_eval_of_interaction_mem
        h_binaryExtension h_providerInteraction
    right
    right
    refine ⟨providerRow, h_providerRow, h_binaryExtension, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg

/-- Lookup-aware version of
    `exists_provider_row_matches_entry_of_active_main_table_interaction`.
    The Binary provider branch returns
    `AirsClean.Binary.staticLookupComponent`, so the same provider row is
    also constrained by the static BinaryTable lookup circuit. -/
theorem exists_static_provider_row_matches_entry_of_active_main_table_interaction
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
    (h_constraints : witness.Constraints)
    (h_balanced : witness.BalancedChannels)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent : mainTable.component = ZiskFv.AirsClean.Main.component)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1) :
    ∃ mainRow ∈ mainTable.table,
      ∃ providerInteraction ∈ witness.interactionsWith OpBusChannel.toRaw,
        providerInteraction.msg = mainInteraction.msg
          ∧ providerInteraction.mult ≠ -1
          ∧ providerInteraction.mult ≠ 0
          ∧ ∃ providerTable ∈ witness.allTables,
            providerInteraction ∈ providerTable.interactionsWith OpBusChannel.toRaw
              ∧
              ((∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.BinaryAdd.component
                    ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                        (OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryAdd.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryAdd.component.rowInputVar)) 1))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
                    ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                        (OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.Binary.opBusMessageExpr
                              ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1))
                ∨ (∃ providerRow ∈ providerTable.table,
                  providerTable.component =
                    ZiskFv.AirsClean.BinaryExtension.staticLookupComponent
                    ∧ ZiskFv.Airs.OperationBus.matches_entry
                        (OpBusMessage.toEntry
                          (eval (mainTable.environment mainRow)
                            (ZiskFv.AirsClean.Main.opBusMessageExpr
                              ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                        (OpBusMessage.toEntry
                          (eval (providerTable.environment providerRow)
                            (ZiskFv.AirsClean.BinaryExtension.opBusMessageExpr
                              ZiskFv.AirsClean.BinaryExtension.staticLookupComponent.rowInputVar)) 1))) := by
  have h_main_mem_witness :
      mainInteraction ∈ witness.interactionsWith OpBusChannel.toRaw := by
    rw [EnsembleWitness.mem_interactionsWith]
    exact ⟨mainTable, h_mainTable, h_mainInteraction⟩
  obtain ⟨mainRow, h_mainRow, h_mainEval⟩ :=
    exists_main_row_eval_of_interaction_mem h_mainComponent h_mainInteraction
  obtain ⟨providerInteraction, h_provider_witness, h_msg, h_nonpull, h_nonzero,
      providerTable, h_providerTable, h_providerInteraction, h_providerComponent⟩ :=
    exists_static_matching_provider_component_of_active_main_interaction
      witness h_constraints h_balanced h_main_mem_witness h_active
  refine ⟨mainRow, h_mainRow, providerInteraction, h_provider_witness, h_msg,
    h_nonpull, h_nonzero, providerTable, h_providerTable,
    h_providerInteraction, ?_⟩
  rcases h_providerComponent with h_binaryAdd | h_binary | h_binaryExtension
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_binaryAdd_row_eval_of_interaction_mem h_binaryAdd h_providerInteraction
    left
    refine ⟨providerRow, h_providerRow, h_binaryAdd, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinary_row_eval_of_interaction_mem h_binary h_providerInteraction
    right
    left
    refine ⟨providerRow, h_providerRow, h_binary, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg
  · obtain ⟨providerRow, h_providerRow, h_providerEval⟩ :=
      exists_staticBinaryExtension_row_eval_of_interaction_mem
        h_binaryExtension h_providerInteraction
    right
    right
    refine ⟨providerRow, h_providerRow, h_binaryExtension, ?_⟩
    apply ZiskFv.Channels.OperationBus.matches_entry_of_eval_msg_eq
    rw [← h_providerEval, ← h_mainEval]
    exact h_msg

/-- Bitwise specialization of the lookup-aware static Binary-family balance
    projection. If the active Main-side Clean message has opcode 14/15/16, the
    balanced provider row cannot be BinaryAdd or BinaryExtension, so it is the
    lookup-aware Binary component row. -/
theorem exists_staticBinary_provider_row_matches_entry_of_bitwise_active_main_table_interaction
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
    (h_constraints : witness.Constraints)
    (h_specs : witness.Spec)
    (h_balanced : witness.BalancedChannels)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent : mainTable.component = ZiskFv.AirsClean.Main.component)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      ∀ mainRow ∈ mainTable.table,
        (OpBusMessage.toEntry
          (eval (mainTable.environment mainRow)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              ZiskFv.AirsClean.Main.component.rowInputVar)) 1).op.val = 14
          ∨ (OpBusMessage.toEntry
            (eval (mainTable.environment mainRow)
              (ZiskFv.AirsClean.Main.opBusMessageExpr
                ZiskFv.AirsClean.Main.component.rowInputVar)) 1).op.val = 15
          ∨ (OpBusMessage.toEntry
            (eval (mainTable.environment mainRow)
              (ZiskFv.AirsClean.Main.opBusMessageExpr
                ZiskFv.AirsClean.Main.component.rowInputVar)) 1).op.val = 16) :
    ∃ mainRow ∈ mainTable.table,
      ∃ providerTable ∈ witness.allTables,
        ∃ providerRow ∈ providerTable.table,
          providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
            ∧ ZiskFv.Airs.OperationBus.matches_entry
                (OpBusMessage.toEntry
                  (eval (mainTable.environment mainRow)
                    (ZiskFv.AirsClean.Main.opBusMessageExpr
                      ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
                (OpBusMessage.toEntry
                  (ZiskFv.AirsClean.Binary.opBusMessage
                    (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                      (providerTable.environment providerRow))) 1) := by
  obtain ⟨mainRow, h_mainRow, providerInteraction, _h_provider_witness, _h_msg,
      _h_nonpull, _h_nonzero, providerTable, h_providerTable,
      _h_providerInteraction, h_providerBranches⟩ :=
    exists_static_provider_row_matches_entry_of_active_main_table_interaction
      witness h_constraints h_balanced h_mainTable h_mainComponent
      h_mainInteraction h_active
  have h_main_op_row := h_main_op mainRow h_mainRow
  rcases h_providerBranches with h_binaryAdd | h_binary | h_binaryExtension
  · rcases h_binaryAdd with ⟨providerRow, _h_providerRow, _h_component, h_match⟩
    exact False.elim (binaryAdd_matches_entry_ne_bitwise h_match h_main_op_row)
  · rcases h_binary with ⟨providerRow, h_providerRow, h_component, h_match⟩
    have h_match_row :
        ZiskFv.Airs.OperationBus.matches_entry
          (OpBusMessage.toEntry
            (eval (mainTable.environment mainRow)
              (ZiskFv.AirsClean.Main.opBusMessageExpr
                ZiskFv.AirsClean.Main.component.rowInputVar)) 1)
          (OpBusMessage.toEntry
            (ZiskFv.AirsClean.Binary.opBusMessage
              (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                (providerTable.environment providerRow))) 1) := by
      simpa only [ZiskFv.AirsClean.Binary.staticLookupComponent_eval_opBusMessageExpr]
        using h_match
    exact ⟨mainRow, h_mainRow, providerTable, h_providerTable,
      providerRow, h_providerRow, h_component, h_match_row⟩
  · rcases h_binaryExtension with ⟨providerRow, h_providerRow, h_component, h_match⟩
    exact False.elim
      (staticBinaryExtension_matches_entry_ne_bitwise h_component
        (h_specs providerTable h_providerTable) h_providerRow h_match
        h_main_op_row)

/-- Legacy-Main specialization of the bitwise static-provider route.

This is the C7 adapter from a concrete Clean Main table row back to the
existing opcode-proof surface: if every row in the selected Clean Main table
is the legacy row `m,r_main`, the balanced static Binary provider row matches
`opBus_row_Main m r_main` directly. -/
theorem exists_staticBinary_provider_row_matches_legacy_main_of_bitwise_active_main_table_interaction
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL) (r_main : ℕ)
    (witness : EnsembleWitness binaryFamilyStaticBinaryTableOpBusEnsemble.ensemble)
    (h_constraints : witness.Constraints)
    (h_specs : witness.Spec)
    (h_balanced : witness.BalancedChannels)
    {mainTable : Table FGL}
    (h_mainTable : mainTable ∈ witness.allTables)
    (h_mainComponent : mainTable.component = ZiskFv.AirsClean.Main.component)
    (h_main_row :
      ∀ mainRow ∈ mainTable.table,
        ZiskFv.AirsClean.Main.component.rowInput
          (mainTable.environment mainRow) =
            ZiskFv.AirsClean.Main.rowAt m r_main)
    (h_main_active : m.is_external_op r_main = 1)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ mainTable.interactionsWith OpBusChannel.toRaw)
    (h_active : mainInteraction.mult = -1)
    (h_main_op :
      ∀ mainRow ∈ mainTable.table,
        (OpBusMessage.toEntry
          (eval (mainTable.environment mainRow)
            (ZiskFv.AirsClean.Main.opBusMessageExpr
              ZiskFv.AirsClean.Main.component.rowInputVar)) 1).op.val = 14
          ∨ (OpBusMessage.toEntry
            (eval (mainTable.environment mainRow)
              (ZiskFv.AirsClean.Main.opBusMessageExpr
                ZiskFv.AirsClean.Main.component.rowInputVar)) 1).op.val = 15
          ∨ (OpBusMessage.toEntry
            (eval (mainTable.environment mainRow)
              (ZiskFv.AirsClean.Main.opBusMessageExpr
                ZiskFv.AirsClean.Main.component.rowInputVar)) 1).op.val = 16) :
    ∃ providerTable ∈ witness.allTables,
      ∃ providerRow ∈ providerTable.table,
        providerTable.component = ZiskFv.AirsClean.Binary.staticLookupComponent
          ∧ providerTable.Spec
          ∧ ZiskFv.Airs.OperationBus.matches_entry
              (ZiskFv.Airs.OperationBus.opBus_row_Main m r_main)
              (OpBusMessage.toEntry
                (ZiskFv.AirsClean.Binary.opBusMessage
                  (ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
                    (providerTable.environment providerRow))) 1) := by
  obtain ⟨mainRow, h_mainRow, providerTable, h_providerTable,
      providerRow, h_providerRow, h_component, h_match⟩ :=
    exists_staticBinary_provider_row_matches_entry_of_bitwise_active_main_table_interaction
      witness h_constraints h_specs h_balanced h_mainTable h_mainComponent
      h_mainInteraction h_active h_main_op
  have h_main_entry :
      OpBusMessage.toEntry
        (eval (mainTable.environment mainRow)
          (ZiskFv.AirsClean.Main.opBusMessageExpr
            ZiskFv.AirsClean.Main.component.rowInputVar)) 1 =
        ZiskFv.Airs.OperationBus.opBus_row_Main m r_main := by
    rw [ZiskFv.AirsClean.Main.component_eval_opBusMessageExpr]
    rw [h_main_row mainRow h_mainRow]
    rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
    rw [h_main_active]
  exact ⟨providerTable, h_providerTable, providerRow, h_providerRow,
    h_component, h_specs providerTable h_providerTable, by
      rw [h_main_entry] at h_match
      exact h_match⟩

end ZiskFv.AirsClean.BinaryFamily
