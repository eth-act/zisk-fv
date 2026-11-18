import Source458DomainComparison.WitnessTransport
import Source415DomainComparison.OldChannelStreams
import ZiskFv.AirsClean.FullEnsemble.Balance.BinaryTableProviderMatch

/-!
# Projection of an arbitrary source18 witness

Only source tables14/15 are dropped. Consumer raw rows and prover data are
retargeted to the original static components; Main16 becomes Main14 without
changing its physical table. No full-height assumption is made on either source.
The restored static lookups use the actual finished-channel provider matching.
-/
namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open BinaryTableBalance (binaryMessage)

variable {p : Nat} {program : Program p}

theorem new_tables_length (new : NewWitness p program) : new.tables.length = 17 :=
  new.same_length.symm

def newTable (new : NewWitness p program) (index : Fin 17) : Table FGL :=
  new.tables.get ⟨index.val, by rw [new_tables_length]; exact index.isLt⟩

theorem newTable_component (new : NewWitness p program) (index : Fin 17) :
    (newTable new index).component =
      (Legacy457.fullRv64imEnsemble p program).ensemble.tables.get
        ⟨index.val, by change index.val < 17; exact index.isLt⟩ :=
  (new.same_circuits index.val (by change index.val < 17; exact index.isLt)).symm

theorem newTable_data (new : NewWitness p program) (index : Fin 17) :
    (newTable new index).data = new.data :=
  new.same_data _ (List.get_mem _ _)

theorem newTable_mem (new : NewWitness p program) (index : Fin 17) :
    newTable new index ∈ new.allTables :=
  List.mem_cons_of_mem _ (List.get_mem _ _)

def binaryStaticTable (new : NewWitness p program) : Table FGL where
  component := Binary.staticLookupComponent
  rawRows := (newTable new 12).rawRows
  data := (newTable new 12).data
  raw_uniform_width := by
    intro row hr
    have h := (newTable new 12).raw_uniform_width row hr
    rw [newTable_component] at h
    exact h
  fixed_domain := by
    intro columns hc
    change (none : Option _) = some columns at hc
    cases hc

def extensionStaticTable (new : NewWitness p program) : Table FGL where
  component := BinaryExtension.shiftStaticLookupComponent
  rawRows := (newTable new 11).rawRows
  data := (newTable new 11).data
  raw_uniform_width := by
    intro row hr
    have h := (newTable new 11).raw_uniform_width row hr
    rw [newTable_component] at h
    exact h
  fixed_domain := by
    intro columns hc
    change (none : Option _) = some columns at hc
    cases hc

private theorem reverse_fixed_none_of_component_eq {component expected : Component FGL}
    (equal : component = expected) (none : expected.fixedColumns = Option.none) :
    component.fixedColumns = Option.none := by
  cases equal
  exact none

theorem binaryStaticTable_table (new : NewWitness p program) :
    (binaryStaticTable new).table = (newTable new 12).table := by
  change (newTable new 12).rawRows = (newTable new 12).table
  unfold Table.table
  have component : (newTable new 12).component = Binary.tableConsumerComponent :=
    newTable_component new 12
  have none := reverse_fixed_none_of_component_eq component rfl
  simp only [none]

theorem extensionStaticTable_table (new : NewWitness p program) :
    (extensionStaticTable new).table = (newTable new 11).table := by
  change (newTable new 11).rawRows = (newTable new 11).table
  unfold Table.table
  have component : (newTable new 11).component = BinaryExtension.shiftTableConsumerComponent :=
    newTable_component new 11
  have none := reverse_fixed_none_of_component_eq component rfl
  simp only [none]

def projectedCommonTables (new : NewWitness p program) : List (Table FGL) :=
  [newTable new 0, newTable new 1, newTable new 2, newTable new 3,
   newTable new 4, newTable new 5, newTable new 6, newTable new 7,
   newTable new 8, newTable new 9, newTable new 10]

def projectedTables (new : NewWitness p program) : List (Table FGL) :=
  projectedCommonTables new ++
    [extensionStaticTable new, binaryStaticTable new, newTable new 13, newTable new 16]

theorem new_tables_eq (new : NewWitness p program) :
    new.tables = projectedCommonTables new ++
      [newTable new 11, newTable new 12, newTable new 13,
       newTable new 14, newTable new 15, newTable new 16] := by
  apply List.ext_getElem
  · rw [new_tables_length]
    rfl
  · intro index hi hi'
    have hindex : index < 17 := by simpa only [new_tables_length] using hi
    interval_cases index <;> rfl

def projectedWitness (new : NewWitness p program) : OldWitness p program where
  tables := projectedTables new
  data := new.data
  publicInput := new.publicInput
  same_length := by rfl
  same_circuits := by
    intro index hi
    have hindex : index < 15 := by change index < 15 at hi; exact hi
    interval_cases index <;>
      simp only [projectedTables, projectedCommonTables, List.cons_append, List.nil_append,
        List.getElem_cons_zero, List.getElem_cons_succ] <;>
      first | rw [newTable_component]; rfl | rfl
  same_data := by
    intro table ht
    simp only [projectedTables, projectedCommonTables, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht |
      ht | ht | ht | ht <;> subst table
    all_goals first
      | exact newTable_data new _
      | exact newTable_data new 11
      | exact newTable_data new 12

theorem projected_verifierTable (new : NewWitness p program) :
    (projectedWitness new).verifierTable = new.verifierTable := by
  apply Ensemble.verifierTable_ext <;> rfl

theorem projected_allTables_length (new : NewWitness p program) :
    (projectedWitness new).allTables.length = 16 := rfl

/-- The exact physical-index backmap, including Main16→14. -/
def projectionBackmap (index : Fin 15) : Fin 17 :=
  ⟨if index.val = 14 then 16 else index.val, by split_ifs <;> omega⟩

theorem projected_rawRows (new : NewWitness p program) (index : Fin 15) :
    (oldTable (projectedWitness new) index).rawRows =
      (newTable new (projectionBackmap index)).rawRows := by
  fin_cases index <;> rfl

theorem projected_table_data (new : NewWitness p program) (index : Fin 15) :
    (oldTable (projectedWitness new) index).data =
      (newTable new (projectionBackmap index)).data := by
  fin_cases index <;> rfl

theorem projected_mainTable (new : NewWitness p program) :
    oldTable (projectedWitness new) 14 = newTable new 16 := rfl

/-- Retargeting back to the consumer recovers the original physical table. -/
theorem projected_binary_consumer (new : NewWitness p program) :
    binaryConsumerTable (projectedWitness new) = newTable new 12 := by
  apply Table.ext_iff.mpr
  exact ⟨(newTable_component new 12).symm, rfl, rfl⟩

theorem projected_extension_consumer (new : NewWitness p program) :
    extensionConsumerTable (projectedWitness new) = newTable new 11 := by
  apply Table.ext_iff.mpr
  exact ⟨(newTable_component new 11).symm, rfl, rfl⟩

/-- Every non-retargeted physical table is retained as the exact Table value. -/
theorem projected_sharedTable (new : NewWitness p program) (index : Fin 15)
    (hext : index.val ≠ 11) (hbin : index.val ≠ 12) :
    oldTable (projectedWitness new) index = newTable new (projectionBackmap index) := by
  fin_cases index <;> first | rfl | contradiction

theorem projected_data (new : NewWitness p program) :
    (projectedWitness new).data = new.data := rfl

theorem projected_publicInput (new : NewWitness p program) :
    (projectedWitness new).publicInput = new.publicInput := rfl

private theorem binary_static_lookups :
    Binary.staticLookupComponent.operations.lookups = (List.finRange 8).map
      (fun index => ({ table := (Table.fromStatic BinaryTable.binaryTable).toRaw, entry := toElements (binaryMessage Binary.tableConsumerComponent.rowInputVar index) } : Lookup FGL)) := by
  rw [Component.lookups_eq]
  rfl

private theorem extension_static_lookups :
    BinaryExtension.staticLookupComponent.operations.lookups = (List.finRange 8).map
      (fun index => ({ table := (Table.fromStatic BinaryExtensionTable.binaryExtensionTable).toRaw, entry := toElements (BinaryExtension.byteMessage BinaryExtension.tableConsumerComponent.rowInputVar index) } : Lookup FGL)) := by
  rw [Component.lookups_eq]
  rfl

/-- This reflection uses static membership, not a completeness assumption on
an arbitrary row. The membership itself is obtained from real source matching. -/
private theorem static_lookup_contains {Row : TypeMap} [ProvableType Row]
    (static : StaticTable FGL Row) (env : Environment FGL)
    (message : Row (Expression FGL)) (h : static.Spec (eval env message)) :
    ({ table := (Table.fromStatic static).toRaw, entry := toElements message } :
      Lookup FGL).Contains env := by
  apply (Table.fromStatic static).toRaw.implied_by_completeness
  change ({ table := (Table.fromStatic static).toRaw, entry := toElements message } :
    Lookup FGL).Completeness env
  simpa only [Lookup.completeness_def, Table.fromStatic, StaticTable.toTable] using h

theorem projected_binary_constraints (new : NewWitness p program)
    (hc : new.Constraints) (hb : new.BalancedChannels) :
    (binaryStaticTable new).Constraints := by
  intro row hr
  rw [binaryStaticTable_table] at hr
  have h := hc _ (newTable_mem new 12) row hr
  rw [newTable_component] at h
  change Binary.staticLookupComponent.operations.ConstraintsHold
    ((newTable new 12).environment row)
  constructor
  · rw [← binary_constraint_projection]
    exact h.1
  · intro lookup hl
    change lookup ∈ Binary.staticLookupComponent.operations.lookups at hl
    rw [binary_static_lookups] at hl
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp hl
    exact static_lookup_contains _ _ _
      (binary_all_eight (MemDomainComparison.eraseLegacyMem new)
        (MemDomainComparison.eraseLegacyMem_constraints new hc)
        (MemDomainComparison.eraseLegacyMem_balancedChannels new hb)
        (MemDomainComparison.nonMem_table_preserved new _ (newTable_mem new 12) (by
          intro hm
          have hw := congrArg (fun c : Component FGL => c.rawWidth) hm
          rw [newTable_component] at hw
          change (39 : Nat) = 17 at hw
          omega))
        (newTable_component new 12) hr index)

theorem projected_extension_constraints (new : NewWitness p program)
    (hc : new.Constraints) (hb : new.BalancedChannels) :
    (extensionStaticTable new).Constraints := by
  intro row hr
  rw [extensionStaticTable_table] at hr
  have h := hc _ (newTable_mem new 11) row hr
  rw [newTable_component] at h
  change BinaryExtension.shiftStaticLookupComponent.operations.ConstraintsHold
    ((newTable new 11).environment row)
  constructor
  · rw [← extension_constraint_projection]
    exact h.1
  · intro lookup hl
    change lookup ∈ BinaryExtension.shiftStaticLookupComponent.operations.lookups at hl
    rw [extension_lookup_projection] at hl
    rcases List.mem_append.mp hl with hl | hl
    · rw [extension_static_lookups] at hl
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp hl
      exact static_lookup_contains _ _ _
        (extension_all_eight (MemDomainComparison.eraseLegacyMem new)
          (MemDomainComparison.eraseLegacyMem_constraints new hc)
          (MemDomainComparison.eraseLegacyMem_balancedChannels new hb)
          (MemDomainComparison.nonMem_table_preserved new _ (newTable_mem new 11) (by
            intro hm
            have hw := congrArg (fun c : Component FGL => c.rawWidth) hm
            rw [newTable_component] at hw
            change (29 : Nat) = 17 at hw
            omega))
          (newTable_component new 11) hr index)
    · exact h.2 lookup hl

/-- All original predicates transfer literally on the shared tables. -/
theorem projected_table_predicate (new : NewWitness p program)
    (predicate : Table FGL → Prop)
    (original : ∀ table ∈ new.allTables, predicate table)
    (extension : predicate (extensionStaticTable new))
    (binary : predicate (binaryStaticTable new)) :
    ∀ table ∈ (projectedWitness new).allTables, predicate table := by
  intro table ht
  change table ∈ (projectedWitness new).verifierTable :: projectedTables new at ht
  rw [projected_verifierTable] at ht
  simp only [projectedTables, projectedCommonTables, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht | ht |
    ht | ht | ht | ht <;> subst table
  · exact original _ List.mem_cons_self
  · exact original _ (newTable_mem new 0)
  · exact original _ (newTable_mem new 1)
  · exact original _ (newTable_mem new 2)
  · exact original _ (newTable_mem new 3)
  · exact original _ (newTable_mem new 4)
  · exact original _ (newTable_mem new 5)
  · exact original _ (newTable_mem new 6)
  · exact original _ (newTable_mem new 7)
  · exact original _ (newTable_mem new 8)
  · exact original _ (newTable_mem new 9)
  · exact original _ (newTable_mem new 10)
  · exact extension
  · exact binary
  · exact original _ (newTable_mem new 13)
  · exact original _ (newTable_mem new 16)

theorem projected_constraints (new : NewWitness p program)
    (hc : new.Constraints) (hb : new.BalancedChannels) :
    (projectedWitness new).Constraints :=
  projected_table_predicate new (fun table => table.Constraints) hc
    (projected_extension_constraints new hc hb) (projected_binary_constraints new hc hb)

theorem projected_transitions (new : NewWitness p program)
    (h : new.TransitionConstraints) : (projectedWitness new).TransitionConstraints := by
  apply projected_table_predicate new (fun table => table.TransitionConstraints) h
  · intro index
    trivial
  · intro index
    trivial

theorem projected_cyclic_transitions (new : NewWitness p program)
    (h : new.CyclicSuccessorTransitionConstraints) :
    (projectedWitness new).CyclicSuccessorTransitionConstraints := by
  apply projected_table_predicate new (fun table => table.CyclicSuccessorTransitionConstraints) h
  · intro index
    trivial
  · intro index
    trivial

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
