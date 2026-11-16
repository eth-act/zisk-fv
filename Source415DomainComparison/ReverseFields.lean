import Source415DomainComparison.ReverseStreams

/-!
# Current accepted18 to the frozen accepted16 contract

All verifier predicates below are derived for the actual projected witness.
The objective Mem guard, selected physical table, coverage of every Mem table,
and universal Main height are transported using exact table membership.
-/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

variable {p : Nat} {program : Program p}

theorem projected_component_membership (new : NewWitness p program)
    (component : Component FGL) (hwidth : component.rawWidth ∉ [29, 39, 10, 1])
    (table : Table FGL) (hc : table.component = component) :
    table ∈ (projectedWitness new).allTables ↔ table ∈ new.allTables := by
  have oldWidths : ([extensionStaticTable new, binaryStaticTable new, newTable new 13].map
      (fun t => t.component.rawWidth)) = [29, 39, 10] := by
    simp only [List.map_cons, List.map_nil, newTable_component]
    rfl
  have newWidths : ([newTable new 11, newTable new 12, newTable new 13,
      newTable new 14, newTable new 15].map (fun t => t.component.rawWidth)) =
      [29, 39, 10, 1, 1] := by
    simp only [List.map_cons, List.map_nil, newTable_component]
    rfl
  have removed_other : ∀ t ∈ [extensionStaticTable new, binaryStaticTable new,
      newTable new 13], ¬ t.component = component := by
    intro t ht he
    have hw : t.component.rawWidth ∈ [29, 39, 10] := by
      rw [← oldWidths]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [he] at hw
    apply hwidth
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    tauto
  have inserted_other : ∀ t ∈ [newTable new 11, newTable new 12, newTable new 13,
      newTable new 14, newTable new 15], ¬ t.component = component := by
    intro t ht he
    have hw : t.component.rawWidth ∈ [29, 39, 10, 1, 1] := by
      rw [← newWidths]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [he] at hw
    exact hwidth (by simpa using hw)
  have hs := ZiskFv.Compliance.DomainComparison.component_membership_splice
    (fun t : Table FGL => t.component = component)
    (new.verifierTable :: projectedCommonTables new)
    [extensionStaticTable new, binaryStaticTable new, newTable new 13]
    [newTable new 11, newTable new 12, newTable new 13, newTable new 14, newTable new 15]
    [newTable new 16] removed_other inserted_other table hc
  change table ∈ (projectedWitness new).verifierTable :: projectedTables new ↔
    table ∈ new.verifierTable :: new.tables
  rw [projected_verifierTable, new_tables_eq]
  simpa only [projectedTables, List.cons_append, List.append_assoc, List.nil_append] using hs

theorem projected_mem_membership (new : NewWitness p program)
    (table : Table FGL) (hc : table.component = Mem.componentWithDualMemBus) :
    table ∈ (projectedWitness new).allTables ↔ table ∈ new.allTables :=
  projected_component_membership new Mem.componentWithDualMemBus
    (by change (17 : Nat) ∉ [29, 39, 10, 1]; decide) table hc

theorem projected_main_membership (new : NewWitness p program)
    (table : Table FGL) (hc : table.component = Main.componentWithRomMemAndOpBus p program) :
    table ∈ (projectedWitness new).allTables ↔ table ∈ new.allTables :=
  projected_component_membership new (Main.componentWithRomMemAndOpBus p program)
    (by change (41 : Nat) ∉ [29, 39, 10, 1]; decide) table hc

theorem projected_mutableMemPresent (new : NewWitness p program) :
    ZiskFv.Compliance.Legacy45.MutableMemPresent (projectedWitness new) ↔
      ZiskFv.Compliance.MutableMemPresent new :=
  ZiskFv.Compliance.DomainComparison.mutableMemPresent_iff (projectedWitness new) new
    (projected_mem_membership new)

/-- Exact forward/back physical row relationship; no claim is made that the
arbitrary source prefixes are canonical or recoverable after dropping them. -/
theorem projected_completed_rawRows (old : OldWitness p program)
    (raw : PackedVirtualTableSources.Witness FGL) (index : Fin 15) :
    (oldTable (projectedWitness (completedWitness old raw)) index).rawRows =
      (oldTable old index).rawRows := by
  fin_cases index <;> rfl

theorem projected_completed_data (old : OldWitness p program)
    (raw : PackedVirtualTableSources.Witness FGL) :
    (projectedWitness (completedWitness old raw)).data = old.data := rfl

end ZiskFv.AirsClean.FullEnsemble.DomainComparison

namespace ZiskFv.Compliance.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.FullEnsemble.DomainComparison

variable {n : Nat}

theorem projected_universal_main_height (trace : AcceptedZiskTrace n) :
    ∀ table ∈ (projectedWitness trace.witness).allTables,
      table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
        ∀ i : Fin n, i.val < table.table.length :=
  (main_height_iff (projectedWitness trace.witness) trace.witness
    (projected_main_membership trace.witness) n).mpr trace.main_height

theorem projected_selected_replay_table (trace : AcceptedZiskTrace n)
    (guard : Legacy45.MutableMemPresent (projectedWitness trace.witness)) :
    let newGuard := (projected_mutableMemPresent trace.witness).mp guard
    let table := (trace.mem_replay_table newGuard).1
    table ∈ (projectedWitness trace.witness).allTables ∧
      table.component = Mem.componentWithDualMemBus ∧ 0 < table.table.length := by
  dsimp only
  have selected := (trace.mem_replay_table
    ((projected_mutableMemPresent trace.witness).mp guard)).2
  exact ⟨(projected_mem_membership trace.witness _ selected.2.1).mpr selected.1,
    selected.2⟩

theorem projected_replay_source_covers (trace : AcceptedZiskTrace n)
    (guard : Legacy45.MutableMemPresent (projectedWitness trace.witness))
    (table : Table FGL)
    (member : table ∈ (projectedWitness trace.witness).allTables)
    (component : table.component = Mem.componentWithDualMemBus) :
    table = (trace.mem_replay_table
      ((projected_mutableMemPresent trace.witness).mp guard)).1 :=
  trace.mem_replay_source_covers
    ((projected_mutableMemPresent trace.witness).mp guard)
    table ((projected_mem_membership trace.witness table component).mp member) component

/-- Genuine arbitrary currentAccepted18→Legacy45Accepted16. There are no
additional candidate-witness predicates or source-fullness promises. -/
def currentAcceptedToLegacy (trace : AcceptedZiskTrace n) : Legacy45.AcceptedZiskTrace n :=
  toLegacy trace (projectedWitness trace.witness)
    (projected_mem_membership trace.witness) (projected_main_membership trace.witness)
    (projected_constraints trace.witness trace.constraints_hold trace.channels_balanced)
    (projected_transitions trace.witness trace.transitions_hold)
    (projected_cyclic_transitions trace.witness trace.cyclic_successor_transitions_hold)
    (projected_balanced trace.witness trace.channels_balanced)

theorem currentAcceptedToLegacy_witness (trace : AcceptedZiskTrace n) :
    (currentAcceptedToLegacy trace).witness = projectedWitness trace.witness := rfl

theorem currentAcceptedToLegacy_memReplayTable (trace : AcceptedZiskTrace n)
    (ho : Legacy45.MutableMemPresent (currentAcceptedToLegacy trace).witness)
    (hn : MutableMemPresent trace.witness) :
    (currentAcceptedToLegacy trace).memReplayTable ho = trace.memReplayTable hn := rfl

theorem currentAcceptedToLegacy_memReplayRows (trace : AcceptedZiskTrace n)
    (ho : Legacy45.MutableMemPresent (currentAcceptedToLegacy trace).witness)
    (hn : MutableMemPresent trace.witness) :
    (currentAcceptedToLegacy trace).memReplayRows ho = trace.memReplayRows hn := rfl

end ZiskFv.Compliance.DomainComparison
