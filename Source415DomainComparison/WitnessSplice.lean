import Source415DomainComparison.Old16
import ZiskFv.AirsClean.PackedVirtualTableSources
import Source415DomainComparison.FieldTransport

/-!
# Concrete old16 to source18 witness splice

This is a data construction, not an acceptance equivalence. The fifteen old
physical tables are retained in order, except that the two Binary-family
components are retargeted on the exact same raw rows and prover data. The two
full canonical fixed-source tables are inserted before Main. Every untouched
Table, including the selected mutable Mem table, is preserved as an actual
Table, not merely by its decoded rows. No Root/Accepted declaration is changed.
-/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open PackedVirtualTableSources
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

variable {p : Nat} {program : Program p}

abbrev OldWitness (p : Nat) (program : Program p) :=
  EnsembleWitness (Legacy45.fullRv64imEnsemble p program).ensemble

abbrev NewWitness (p : Nat) (program : Program p) :=
  EnsembleWitness (fullRv64imEnsemble p program).ensemble

theorem old_tables_length (old : OldWitness p program) : old.tables.length = 15 :=
  old.same_length.symm

def oldTable (old : OldWitness p program) (index : Fin 15) : Table FGL :=
  old.tables.get ⟨index.val, by rw [old_tables_length]; exact index.isLt⟩

theorem oldTable_component (old : OldWitness p program) (index : Fin 15) :
    (oldTable old index).component =
      (Legacy45.fullRv64imEnsemble p program).ensemble.tables.get
        ⟨index.val, by change index.val < 15; exact index.isLt⟩ :=
  (old.same_circuits index.val (by change index.val < 15; exact index.isLt)).symm

theorem oldTable_data (old : OldWitness p program) (index : Fin 15) :
    (oldTable old index).data = old.data :=
  old.same_data _ (List.get_mem _ _)

theorem old_extension_component (old : OldWitness p program) :
    (oldTable old 11).component = BinaryExtension.shiftStaticLookupComponent :=
  oldTable_component old 11

theorem old_binary_component (old : OldWitness p program) :
    (oldTable old 12).component = Binary.staticLookupComponent :=
  oldTable_component old 12

/-- Retargeting does not copy, decode or replace any original witness cell. -/
def binaryConsumerTable (old : OldWitness p program) : Table FGL where
  component := Binary.tableConsumerComponent
  rawRows := (oldTable old 12).rawRows
  data := (oldTable old 12).data
  raw_uniform_width := by
    intro row hr
    have h := (oldTable old 12).raw_uniform_width row hr
    rw [old_binary_component] at h
    exact h
  fixed_domain := by
    intro columns hc
    change (none : Option _) = some columns at hc
    cases hc

def extensionConsumerTable (old : OldWitness p program) : Table FGL where
  component := BinaryExtension.shiftTableConsumerComponent
  rawRows := (oldTable old 11).rawRows
  data := (oldTable old 11).data
  raw_uniform_width := by
    intro row hr
    have h := (oldTable old 11).raw_uniform_width row hr
    rw [old_extension_component] at h
    exact h
  fixed_domain := by
    intro columns hc
    change (none : Option _) = some columns at hc
    cases hc

theorem binaryConsumerTable_rawRows (old : OldWitness p program) :
    (binaryConsumerTable old).rawRows = (oldTable old 12).rawRows := rfl

theorem extensionConsumerTable_rawRows (old : OldWitness p program) :
    (extensionConsumerTable old).rawRows = (oldTable old 11).rawRows := rfl

theorem binaryConsumerTable_environment (old : OldWitness p program) (row : Array FGL) :
    (binaryConsumerTable old).environment row = (oldTable old 12).environment row := rfl

theorem extensionConsumerTable_environment (old : OldWitness p program) (row : Array FGL) :
    (extensionConsumerTable old).environment row = (oldTable old 11).environment row := rfl

private theorem fixed_none_of_component_eq {component expected : Component FGL}
    (equal : component = expected) (none : expected.fixedColumns = Option.none) :
    component.fixedColumns = Option.none := by
  cases equal
  exact none

theorem binaryConsumerTable_table (old : OldWitness p program) :
    (binaryConsumerTable old).table = (oldTable old 12).table := by
  change (oldTable old 12).rawRows = (oldTable old 12).table
  unfold Table.table
  have hnone : (oldTable old 12).component.fixedColumns = none :=
    fixed_none_of_component_eq (old_binary_component old) rfl
  simp only [hnone]

theorem extensionConsumerTable_table (old : OldWitness p program) :
    (extensionConsumerTable old).table = (oldTable old 11).table := by
  change (oldTable old 11).rawRows = (oldTable old 11).table
  unfold Table.table
  have hnone : (oldTable old 11).component.fixedColumns = none :=
    fixed_none_of_component_eq (old_extension_component old) rfl
  simp only [hnone]

/-- Original shared rows, in their original order; this includes mutable Mem. -/
def commonTables (old : OldWitness p program) : List (Table FGL) :=
  [oldTable old 0, oldTable old 1, oldTable old 2, oldTable old 3,
   oldTable old 4, oldTable old 5, oldTable old 6, oldTable old 7,
   oldTable old 8, oldTable old 9, oldTable old 10]

def completedTables (old : OldWitness p program) (raw : Witness FGL) : List (Table FGL) :=
  commonTables old ++
    [extensionConsumerTable old, binaryConsumerTable old, oldTable old 13,
     extensionProviderTable raw old.data, binaryProviderTable raw old.data,
     oldTable old 14]

theorem old_tables_eq (old : OldWitness p program) :
    old.tables = commonTables old ++
      [oldTable old 11, oldTable old 12, oldTable old 13, oldTable old 14] := by
  apply List.ext_getElem
  · rw [old_tables_length]
    rfl
  · intro index hi hi'
    have hindex : index < 15 := by simpa only [old_tables_length] using hi
    interval_cases index <;> rfl

/-- A concrete source18 witness for every old witness and actual packed raw
array. This asserts no constraints or balance before their separate proofs. -/
def completedWitness (old : OldWitness p program) (raw : Witness FGL) :
    NewWitness p program where
  tables := completedTables old raw
  data := old.data
  publicInput := old.publicInput
  same_length := by rfl
  same_circuits := by
    intro index hi
    have hindex : index < 17 := by change index < 17 at hi; exact hi
    interval_cases index <;>
      simp only [completedTables, commonTables, List.cons_append, List.nil_append,
        List.getElem_cons_zero, List.getElem_cons_succ] <;>
      first | rw [oldTable_component]; rfl | rfl
  same_data := by
    intro table ht
    simp only [completedTables, commonTables, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with
      ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht |
      ht | ht | ht | ht | ht | ht <;> subst table
    all_goals first
      | exact oldTable_data old _
      | exact oldTable_data old 11
      | exact oldTable_data old 12
      | rfl

theorem completedWitness_tables (old : OldWitness p program) (raw : Witness FGL) :
    (completedWitness old raw).tables = completedTables old raw := rfl

theorem completedWitness_verifierTable (old : OldWitness p program) (raw : Witness FGL) :
    (completedWitness old raw).verifierTable = old.verifierTable := by
  apply Ensemble.verifierTable_ext <;> rfl

theorem old_allTables_length (old : OldWitness p program) : old.allTables.length = 16 := by
  simp only [EnsembleWitness.allTables, List.length_cons, old_tables_length]

theorem completed_allTables_length (old : OldWitness p program) (raw : Witness FGL) :
    (completedWitness old raw).allTables.length = 18 := rfl

theorem model_component_rosters_differ :
    (Legacy45.fullRv64imEnsemble p program).ensemble.allTables ≠
      (fullRv64imEnsemble p program).ensemble.allTables := by
  intro h
  have hn := congrArg List.length h
  change (16 : Nat) = 18 at hn
  omega

private theorem replaced_widths (old : OldWitness p program) :
    ([oldTable old 11, oldTable old 12, oldTable old 13].map
      (fun table => table.component.rawWidth)) = [29, 39, 10] := by
  simp only [List.map_cons, List.map_nil, oldTable_component]
  rfl

private theorem inserted_widths (old : OldWitness p program) (raw : Witness FGL) :
    ([extensionConsumerTable old, binaryConsumerTable old, oldTable old 13,
      extensionProviderTable raw old.data, binaryProviderTable raw old.data].map
      (fun table => table.component.rawWidth)) = [29, 39, 10, 1, 1] := by
  simp only [List.map_cons, List.map_nil, oldTable_component]
  rfl

/-- Concrete membership preservation for components not retargeted or inserted.
The width exclusions are applied below to the actual Main/Mem schemas. -/
theorem completed_component_membership (old : OldWitness p program) (raw : Witness FGL)
    (component : Component FGL)
    (hwidth : component.rawWidth ∉ [29, 39, 10, 1])
    (table : Table FGL) (hc : table.component = component) :
    table ∈ old.allTables ↔ table ∈ (completedWitness old raw).allTables := by
  have removed_other : ∀ t ∈ [oldTable old 11, oldTable old 12, oldTable old 13],
      ¬ t.component = component := by
    intro t ht he
    have hw : t.component.rawWidth ∈ [29, 39, 10] := by
      rw [← replaced_widths old]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [he] at hw
    apply hwidth
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    tauto
  have inserted_other : ∀ t ∈ [extensionConsumerTable old, binaryConsumerTable old,
      oldTable old 13, extensionProviderTable raw old.data, binaryProviderTable raw old.data],
      ¬ t.component = component := by
    intro t ht he
    have hw : t.component.rawWidth ∈ [29, 39, 10, 1, 1] := by
      rw [← inserted_widths old raw]
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    rw [he] at hw
    exact hwidth (by simpa using hw)
  have hs := ZiskFv.Compliance.DomainComparison.component_membership_splice
    (fun t : Table FGL => t.component = component)
    (old.verifierTable :: commonTables old)
    [oldTable old 11, oldTable old 12, oldTable old 13]
    [extensionConsumerTable old, binaryConsumerTable old, oldTable old 13,
      extensionProviderTable raw old.data, binaryProviderTable raw old.data]
    [oldTable old 14] removed_other inserted_other table hc
  change table ∈ old.verifierTable :: old.tables ↔
    table ∈ (completedWitness old raw).verifierTable :: completedTables old raw
  rw [completedWitness_verifierTable, old_tables_eq]
  simpa only [completedTables, List.cons_append, List.append_assoc, List.nil_append] using hs

theorem completed_mem_membership (old : OldWitness p program) (raw : Witness FGL)
    (table : Table FGL) (hc : table.component = Mem.componentWithDualMemBus) :
    table ∈ old.allTables ↔ table ∈ (completedWitness old raw).allTables :=
  completed_component_membership old raw Mem.componentWithDualMemBus
    (by change (17 : Nat) ∉ [29, 39, 10, 1]; decide) table hc

theorem completed_main_membership (old : OldWitness p program) (raw : Witness FGL)
    (table : Table FGL) (hc : table.component = Main.componentWithRomMemAndOpBus p program) :
    table ∈ old.allTables ↔ table ∈ (completedWitness old raw).allTables :=
  completed_component_membership old raw (Main.componentWithRomMemAndOpBus p program)
    (by change (41 : Nat) ∉ [29, 39, 10, 1]; decide) table hc

/-- The objective guard is unchanged by the actual splice, even though the two
full source tables are nonempty. Their raw width is1, not the mutable-Mem17. -/
theorem completed_mutableMemPresent (old : OldWitness p program) (raw : Witness FGL) :
    ZiskFv.Compliance.Legacy45.MutableMemPresent old ↔
      ZiskFv.Compliance.MutableMemPresent (completedWitness old raw) :=
  ZiskFv.Compliance.DomainComparison.mutableMemPresent_iff old (completedWitness old raw)
    (completed_mem_membership old raw)

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
