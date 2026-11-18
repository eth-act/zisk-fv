import Source458DomainComparison.Accepted18
import Source415DomainComparison.Accepted16

/-!
# Conditional transport of the historical accepted fields

Both endpoints here are frozen: historical45 old16 and historical457 old18.
The retained `toCurrent` name means the latter historical endpoint, not the
corrected production domain. Production erasure is the distinct Source458
MemDomainComparison transport. These assembly lemmas require the actual full
balance predicate, including the original interaction-list length bound.
No public Accepted/Root declaration or mutable-memory guard changes here.
-/

namespace ZiskFv.Compliance.DomainComparison

open ZiskFv.AirsClean

section Witnesses

variable {p : Nat} {program : ZiskInstructionRom.Program p}
variable (old : Air.Flat.EnsembleWitness
  (FullEnsemble.Legacy45.fullRv64imEnsemble p program).ensemble)
variable (new : Air.Flat.EnsembleWitness
  (FullEnsemble.Legacy457.fullRv64imEnsemble p program).ensemble)
/- Exact table identity, not equality of decoded or replay rows. This condition
must be derived from the concrete splice; it quantifies over empty tables too. -/
variable (mem : ∀ table : Air.Flat.Table FGL,
  table.component = Mem.Legacy457.componentWithDualMemBus →
    (table ∈ old.allTables ↔ table ∈ new.allTables))

include mem in
 theorem mutableMemPresent_iff :
    Legacy45.MutableMemPresent old ↔ Legacy457.MutableMemPresent new := by
  constructor
  · rintro ⟨table, ht, hc, hn⟩
    exact ⟨table, (mem table hc).mp ht, hc, hn⟩
  · rintro ⟨table, ht, hc, hn⟩
    exact ⟨table, (mem table hc).mpr ht, hc, hn⟩

/- Main height remains universal over every Main table, with its unchanged
component-owned fixed schema. No selected-table-only height premise is used. -/
variable (main : ∀ table : Air.Flat.Table FGL,
  table.component = Main.componentWithRomMemAndOpBus p program →
    (table ∈ old.allTables ↔ table ∈ new.allTables))

include main in
 theorem main_height_iff (n : Nat) :
    (∀ table ∈ old.allTables,
      table.component = Main.componentWithRomMemAndOpBus p program →
        ∀ i : Fin n, i.val < table.table.length) ↔
    (∀ table ∈ new.allTables,
      table.component = Main.componentWithRomMemAndOpBus p program →
        ∀ i : Fin n, i.val < table.table.length) := by
  constructor
  · intro h table ht hc
    exact h table ((main table hc).mpr ht) hc
  · intro h table ht hc
    exact h table ((main table hc).mp ht) hc

end Witnesses

/-- Forward assembly for a supplied candidate witness. All four target verifier
obligations remain explicit: this does not assert that arbitrary old accepted
witnesses admit a balanced source18 completion. -/
def toCurrent {n : Nat} (trace : Legacy45.AcceptedZiskTrace n)
    (new : Air.Flat.EnsembleWitness
      (FullEnsemble.Legacy457.fullRv64imEnsemble trace.programLength trace.program).ensemble)
    (mem : ∀ table : Air.Flat.Table FGL,
      table.component = Mem.Legacy457.componentWithDualMemBus →
        (table ∈ trace.witness.allTables ↔ table ∈ new.allTables))
    (main : ∀ table : Air.Flat.Table FGL,
      table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
        (table ∈ trace.witness.allTables ↔ table ∈ new.allTables))
    (constraints : new.Constraints)
    (transitions : new.TransitionConstraints)
    (cyclic : new.CyclicSuccessorTransitionConstraints)
    (balance : new.BalancedChannels) : Legacy457.AcceptedZiskTrace n where
  programLength := trace.programLength
  program := trace.program
  witness := new
  constraints_hold := constraints
  channels_balanced := balance
  transitions_hold := transitions
  cyclic_successor_transitions_hold := cyclic
  mem_replay_table := fun h =>
    let selected := trace.mem_replay_table
      ((mutableMemPresent_iff trace.witness new mem).mpr h)
    ⟨selected.1, (mem selected.1 selected.2.2.1).mp selected.2.1,
      selected.2.2⟩
  mem_replay_source_covers := by
    intro h table ht hc
    exact trace.mem_replay_source_covers
      ((mutableMemPresent_iff trace.witness new mem).mpr h)
      table ((mem table hc).mpr ht) hc
  main_height := (main_height_iff trace.witness new main n).mp trace.main_height

/-- Reverse assembly has the same exact membership boundary and requires the
finished old verifier predicates, rather than silently inferring balance. -/
def toLegacy {n : Nat} (trace : Legacy457.AcceptedZiskTrace n)
    (old : Air.Flat.EnsembleWitness
      (FullEnsemble.Legacy45.fullRv64imEnsemble trace.programLength trace.program).ensemble)
    (mem : ∀ table : Air.Flat.Table FGL,
      table.component = Mem.Legacy457.componentWithDualMemBus →
        (table ∈ old.allTables ↔ table ∈ trace.witness.allTables))
    (main : ∀ table : Air.Flat.Table FGL,
      table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
        (table ∈ old.allTables ↔ table ∈ trace.witness.allTables))
    (constraints : old.Constraints)
    (transitions : old.TransitionConstraints)
    (cyclic : old.CyclicSuccessorTransitionConstraints)
    (balance : old.BalancedChannels) : Legacy45.AcceptedZiskTrace n where
  programLength := trace.programLength
  program := trace.program
  witness := old
  constraints_hold := constraints
  channels_balanced := balance
  transitions_hold := transitions
  cyclic_successor_transitions_hold := cyclic
  mem_replay_table := fun h =>
    let selected := trace.mem_replay_table
      ((mutableMemPresent_iff old trace.witness mem).mp h)
    ⟨selected.1, (mem selected.1 selected.2.2.1).mpr selected.2.1,
      selected.2.2⟩
  mem_replay_source_covers := by
    intro h table ht hc
    exact trace.mem_replay_source_covers
      ((mutableMemPresent_iff old trace.witness mem).mp h)
      table ((mem table hc).mp ht) hc
  main_height := (main_height_iff old trace.witness main n).mpr trace.main_height

section ForwardSelection

variable {n : Nat} (trace : Legacy45.AcceptedZiskTrace n)
variable (new : Air.Flat.EnsembleWitness
  (FullEnsemble.Legacy457.fullRv64imEnsemble trace.programLength trace.program).ensemble)
variable (mem : ∀ table : Air.Flat.Table FGL,
  table.component = Mem.Legacy457.componentWithDualMemBus →
    (table ∈ trace.witness.allTables ↔ table ∈ new.allTables))
variable (main : ∀ table : Air.Flat.Table FGL,
  table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
    (table ∈ trace.witness.allTables ↔ table ∈ new.allTables))
variable (constraints : new.Constraints) (transitions : new.TransitionConstraints)
variable (cyclic : new.CyclicSuccessorTransitionConstraints) (balance : new.BalancedChannels)

/-- Arbitrary proofs of the objective guard select the exact same table;
Lean proof irrelevance identifies the guard arguments. -/
theorem toCurrent_memReplayTable
    (hn : Legacy457.MutableMemPresent new) (ho : Legacy45.MutableMemPresent trace.witness) :
    (toCurrent trace new mem main constraints transitions cyclic balance).memReplayTable hn =
      trace.memReplayTable ho := by
  rfl

theorem toCurrent_memReplayRows
    (hn : Legacy457.MutableMemPresent new) (ho : Legacy45.MutableMemPresent trace.witness) :
    (toCurrent trace new mem main constraints transitions cyclic balance).memReplayRows hn =
      trace.memReplayRows ho := by
  rfl

end ForwardSelection

section ReverseSelection

variable {n : Nat} (trace : Legacy457.AcceptedZiskTrace n)
variable (old : Air.Flat.EnsembleWitness
  (FullEnsemble.Legacy45.fullRv64imEnsemble trace.programLength trace.program).ensemble)
variable (mem : ∀ table : Air.Flat.Table FGL,
  table.component = Mem.Legacy457.componentWithDualMemBus →
    (table ∈ old.allTables ↔ table ∈ trace.witness.allTables))
variable (main : ∀ table : Air.Flat.Table FGL,
  table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
    (table ∈ old.allTables ↔ table ∈ trace.witness.allTables))
variable (constraints : old.Constraints) (transitions : old.TransitionConstraints)
variable (cyclic : old.CyclicSuccessorTransitionConstraints) (balance : old.BalancedChannels)

theorem toLegacy_memReplayTable
    (ho : Legacy45.MutableMemPresent old) (hn : Legacy457.MutableMemPresent trace.witness) :
    (toLegacy trace old mem main constraints transitions cyclic balance).memReplayTable ho =
      trace.memReplayTable hn := by
  rfl

theorem toLegacy_memReplayRows
    (ho : Legacy45.MutableMemPresent old) (hn : Legacy457.MutableMemPresent trace.witness) :
    (toLegacy trace old mem main constraints transitions cyclic balance).memReplayRows ho =
      trace.memReplayRows hn := by
  rfl

end ReverseSelection

/-- A list splice preserves exact membership in a component-filtered collection
when neither removed nor inserted tables have that component. Empty tables are
not discarded. Apply separately to Main and Mem after proving source exclusion
from the actual component schemas. -/
theorem component_membership_splice
    {α : Type*} (component : α → Prop)
    (before removed inserted after : List α)
    (removed_other : ∀ t ∈ removed, ¬ component t)
    (inserted_other : ∀ t ∈ inserted, ¬ component t)
    (table : α) (hc : component table) :
    table ∈ before ++ removed ++ after ↔ table ∈ before ++ inserted ++ after := by
  have hr : table ∉ removed := fun h => removed_other table h hc
  have hi : table ∉ inserted := fun h => inserted_other table h hc
  simp only [List.mem_append, hr, hi, or_false, false_or]

end ZiskFv.Compliance.DomainComparison
