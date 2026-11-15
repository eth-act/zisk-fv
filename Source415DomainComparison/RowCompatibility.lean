import Source415DomainComparison.WitnessSplice
import Source415DomainComparison.PhysicalCompletion

/-! Actual row-local direction for the 16-to-18 comparison. Replacing static
lookups by channel emissions does not change polynomial constraints. The
Extension consumer retains its existing 24-bit shift-range lookup. The new
provider constraints are proved on their real, complete fixed source rows.
This file does not assert the unproved new-channel no-overflow bounds. -/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

 theorem binary_constraint_projection :
    Binary.tableConsumerComponent.operations.constraints =
      Binary.staticLookupComponent.operations.constraints := by
  rw [Component.constraints_eq, Component.constraints_eq]
  rfl

 theorem binary_consumer_lookups :
    Binary.tableConsumerComponent.operations.lookups = [] := by
  rw [Component.lookups_eq]
  rfl

 theorem extension_constraint_projection :
    BinaryExtension.shiftTableConsumerComponent.operations.constraints =
      BinaryExtension.shiftStaticLookupComponent.operations.constraints := by
  rw [Component.constraints_eq, Component.constraints_eq]
  rfl

 theorem extension_lookup_projection :
    BinaryExtension.shiftStaticLookupComponent.operations.lookups =
      BinaryExtension.staticLookupComponent.operations.lookups ++
        BinaryExtension.shiftTableConsumerComponent.operations.lookups := by
  rw [Component.lookups_eq, Component.lookups_eq, Component.lookups_eq]
  rfl

 theorem binary_row_constraints (env : Environment FGL)
    (h : Binary.staticLookupComponent.operations.ConstraintsHold env) :
    Binary.tableConsumerComponent.operations.ConstraintsHold env := by
  constructor
  · simpa only [binary_constraint_projection] using h.1
  · intro lookup hlookup
    rw [binary_consumer_lookups] at hlookup
    cases hlookup

 theorem extension_row_constraints (env : Environment FGL)
    (h : BinaryExtension.shiftStaticLookupComponent.operations.ConstraintsHold env) :
    BinaryExtension.shiftTableConsumerComponent.operations.ConstraintsHold env := by
  constructor
  · simpa only [extension_constraint_projection] using h.1
  · intro lookup hlookup
    apply h.2 lookup
    rw [extension_lookup_projection]
    exact List.mem_append_right _ hlookup

 theorem binary_table_constraints {p : ℕ}
    {program : Program p}
    (old : OldWitness p program) (h : (oldTable old 12).Constraints) :
    (binaryConsumerTable old).Constraints := by
  intro row hrow
  rw [binaryConsumerTable_table] at hrow
  have hold := h row hrow
  rw [old_binary_component] at hold
  change Binary.tableConsumerComponent.operations.ConstraintsHold
    ((oldTable old 12).environment row)
  exact binary_row_constraints _ hold

 theorem extension_table_constraints {p : ℕ}
    {program : Program p}
    (old : OldWitness p program) (h : (oldTable old 11).Constraints) :
    (extensionConsumerTable old).Constraints := by
  intro row hrow
  rw [extensionConsumerTable_table] at hrow
  have hold := h row hrow
  rw [old_extension_component] at hold
  change BinaryExtension.shiftTableConsumerComponent.operations.ConstraintsHold
    ((oldTable old 11).environment row)
  exact extension_row_constraints _ hold

 theorem oldTable_mem {p : ℕ}
    {program : Program p}
    (old : OldWitness p program) (index : Fin 15) :
    oldTable old index ∈ old.allTables := by
  exact List.mem_cons_of_mem _ (List.get_mem _ _)

 theorem completed_constraints {p : ℕ}
    {program : Program p}
    (old : OldWitness p program) (raw : PackedVirtualTableSources.Witness FGL)
    (h : old.Constraints) : (completedWitness old raw).Constraints := by
  have hext := extension_table_constraints old (h _ (oldTable_mem old 11))
  have hbin := binary_table_constraints old (h _ (oldTable_mem old 12))
  have hesource := (extension_full_checks raw old.data).1
  have hbsource := (binary_full_checks raw old.data).1
  intro table htable
  simp only [EnsembleWitness.allTables, completedWitness_tables,
    completedWitness_verifierTable, completedTables, commonTables,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at htable
  rcases htable with htable | htable | htable | htable | htable | htable |
    htable | htable | htable | htable | htable | htable | htable | htable |
    htable | htable | htable | htable <;> subst table
  · exact h _ (List.mem_cons_self)
  · exact h _ (oldTable_mem old 0)
  · exact h _ (oldTable_mem old 1)
  · exact h _ (oldTable_mem old 2)
  · exact h _ (oldTable_mem old 3)
  · exact h _ (oldTable_mem old 4)
  · exact h _ (oldTable_mem old 5)
  · exact h _ (oldTable_mem old 6)
  · exact h _ (oldTable_mem old 7)
  · exact h _ (oldTable_mem old 8)
  · exact h _ (oldTable_mem old 9)
  · exact h _ (oldTable_mem old 10)
  · exact hext
  · exact hbin
  · exact h _ (oldTable_mem old 13)
  · exact hesource
  · exact hbsource
  · exact h _ (oldTable_mem old 14)

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
