import Source415DomainComparison.RowCompatibility

/-! Actual source-transition direction. Original shared tables are unchanged;
the two retargeted consumers have the actual trivial transition specifications,
and both added full providers satisfy their real transition specifications.
This adds no condition to the accepted contract. -/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open PackedVirtualTableSources
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

variable {p : Nat} {program : Program p}

private theorem completed_table_predicate (old : OldWitness p program)
    (raw : Witness FGL) (predicate : Table FGL → Prop)
    (original : ∀ table ∈ old.allTables, predicate table)
    (extension : predicate (extensionConsumerTable old))
    (binary : predicate (binaryConsumerTable old))
    (extensionSource : predicate (extensionProviderTable raw old.data))
    (binarySource : predicate (binaryProviderTable raw old.data)) :
    ∀ table ∈ (completedWitness old raw).allTables, predicate table := by
  intro table member
  simp only [EnsembleWitness.allTables, completedWitness_tables,
    completedWitness_verifierTable, completedTables, commonTables,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | member | member | member | member | member |
    member | member | member | member | member | member | member | member |
    member | member | member | member <;> subst table
  · exact original _ (List.mem_cons_self)
  · exact original _ (oldTable_mem old 0)
  · exact original _ (oldTable_mem old 1)
  · exact original _ (oldTable_mem old 2)
  · exact original _ (oldTable_mem old 3)
  · exact original _ (oldTable_mem old 4)
  · exact original _ (oldTable_mem old 5)
  · exact original _ (oldTable_mem old 6)
  · exact original _ (oldTable_mem old 7)
  · exact original _ (oldTable_mem old 8)
  · exact original _ (oldTable_mem old 9)
  · exact original _ (oldTable_mem old 10)
  · exact extension
  · exact binary
  · exact original _ (oldTable_mem old 13)
  · exact extensionSource
  · exact binarySource
  · exact original _ (oldTable_mem old 14)

 theorem completed_transitions (old : OldWitness p program) (raw : Witness FGL)
    (original : old.TransitionConstraints) :
    (completedWitness old raw).TransitionConstraints := by
  apply completed_table_predicate old raw (fun table => table.TransitionConstraints) original
  · intro index
    trivial
  · intro index
    trivial
  · exact (extension_full_checks raw old.data).2.1
  · exact (binary_full_checks raw old.data).2.1

 theorem completed_cyclic_transitions (old : OldWitness p program) (raw : Witness FGL)
    (original : old.CyclicSuccessorTransitionConstraints) :
    (completedWitness old raw).CyclicSuccessorTransitionConstraints := by
  apply completed_table_predicate old raw
    (fun table => table.CyclicSuccessorTransitionConstraints) original
  · intro index
    trivial
  · intro index
    trivial
  · exact (extension_full_checks raw old.data).2.2
  · exact (binary_full_checks raw old.data).2.2

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
