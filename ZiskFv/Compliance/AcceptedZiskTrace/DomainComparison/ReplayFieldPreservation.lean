import ZiskFv.AirsClean.FullEnsemble.DomainComparison.RowCompatibility

/-! Concrete preservation of the three dependent accepted-field contracts.
The splice preserves the chosen replay `Table` itself, the exact objective
mutable-Mem guard, coverage of every Mem table, and height of every Main table.
This is not an old/new accepted-domain equivalence: finished new-channel
balance remains a separate, unproved direction of that comparison. -/

namespace ZiskFv.Compliance.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.FullEnsemble.DomainComparison
open ZiskFv.AirsClean.PackedVirtualTableSources

variable {n : Nat}

 theorem completed_universal_main_height (trace : Legacy45.AcceptedZiskTrace n)
    (raw : Witness FGL) :
    ∀ table ∈ (completedWitness trace.witness raw).allTables,
      table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
        ∀ i : Fin n, i.val < table.table.length :=
  (main_height_iff trace.witness (completedWitness trace.witness raw)
    (completed_main_membership trace.witness raw) n).mp trace.main_height

/-- The exact existing selected physical Table remains in the new roster;
no replacement replay rows or newly selected table are introduced. -/
 theorem completed_selected_replay_table (trace : Legacy45.AcceptedZiskTrace n)
    (raw : Witness FGL)
    (guard : MutableMemPresent (completedWitness trace.witness raw)) :
    let oldGuard := (completed_mutableMemPresent trace.witness raw).mpr guard
    let table := (trace.mem_replay_table oldGuard).1
    table ∈ (completedWitness trace.witness raw).allTables ∧
      table.component = Mem.componentWithDualMemBus ∧ 0 < table.table.length := by
  dsimp only
  have selected := (trace.mem_replay_table
    ((completed_mutableMemPresent trace.witness raw).mpr guard)).2
  exact ⟨(completed_mem_membership trace.witness raw _ selected.2.1).mp selected.1,
    selected.2⟩

/-- The existing coverage field still covers every target Mem table, not only
its originally selected member. Proof irrelevance changes no physical Table. -/
 theorem completed_replay_source_covers (trace : Legacy45.AcceptedZiskTrace n)
    (raw : Witness FGL)
    (guard : MutableMemPresent (completedWitness trace.witness raw))
    (table : Table FGL)
    (member : table ∈ (completedWitness trace.witness raw).allTables)
    (component : table.component = Mem.componentWithDualMemBus) :
    table = (trace.mem_replay_table
      ((completed_mutableMemPresent trace.witness raw).mpr guard)).1 :=
  trace.mem_replay_source_covers
    ((completed_mutableMemPresent trace.witness raw).mpr guard)
    table ((completed_mem_membership trace.witness raw table component).mpr member) component

end ZiskFv.Compliance.DomainComparison
