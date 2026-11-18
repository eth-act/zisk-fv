import Source458DomainComparison.WitnessTransport

/-!
# Historical accepted eighteen-table traces embed in the corrected domain

The candidate witness and every target verifier certificate are constructed
from the old trace. No new witness, balance, transition, membership, coverage,
height, or replay certificate is an argument. Selection preserves the chosen
Mem source's actual buffers; its component identity alone is retargeted.
-/

namespace ZiskFv.Compliance.MemDomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean
open ZiskFv.AirsClean.FullEnsemble.MemDomainComparison

variable {p : Nat} {program : ZiskInstructionRom.Program p}

noncomputable section

/-- A corrected Mem member in the image comes from the historical Mem slot.
This classifies a source table; it reconstructs no old numeric predicate. -/
theorem historical_mem_source (old : OldWitness p program) (table : Table FGL)
    (ht : table ∈ old.allTables)
    (hc : (retargetTable table).component = Mem.componentWithDualMemBus) :
    table.component = Mem.Legacy457.componentWithDualMemBus := by
  apply old_mem_component_of_width old table ht
  rw [← retargetTable_rawWidth table, hc] <;> rfl

theorem eraseLegacyMem_memPresent (old : OldWitness p program)
    (h : Legacy457.MutableMemPresent old) : MutableMemPresent (eraseLegacyMem old) := by
  rcases h with ⟨table, ht, hc, hn⟩
  refine ⟨retargetTable table, ?_, retargetTable_mem_component table hc, ?_⟩
  · rw [eraseLegacyMem_allTables]
    exact List.mem_map.mpr ⟨table, ht, rfl⟩
  · simpa only [retargetTable_table] using hn

/-- The objective presence guard is reflected by the same roster and rows.
This is not a reverse accepted-domain or scalar-constraint theorem. -/
theorem eraseLegacyMem_memPresent_source (old : OldWitness p program)
    (h : MutableMemPresent (eraseLegacyMem old)) : Legacy457.MutableMemPresent old := by
  rcases h with ⟨table, ht, hc, hn⟩
  rw [eraseLegacyMem_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  exact ⟨source, hs, historical_mem_source old source hs hc,
    by simpa only [retargetTable_table] using hn⟩

theorem eraseLegacyMem_memAbsent (old : OldWitness p program)
    (h : ¬ Legacy457.MutableMemPresent old) : ¬ MutableMemPresent (eraseLegacyMem old) :=
  fun present => h (eraseLegacyMem_memPresent_source old present)

variable {n : Nat}

theorem erased_main_height (trace : Legacy457.AcceptedZiskTrace n) :
    ∀ table ∈ (eraseLegacyMem trace.witness).allTables,
      table.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program →
        ∀ i : Fin n, i.val < table.table.length := by
  intro table ht hc index
  rw [eraseLegacyMem_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  have notMem : source.component ≠ Mem.Legacy457.componentWithDualMemBus := by
    intro hm
    have impossible := congrArg (fun component : Component FGL => component.rawWidth) hc
    rw [retargetTable_mem_component source hm] at impossible
    change (17 : Nat) = 41 at impossible
    omega
  have sourceMain : source.component =
      Main.componentWithRomMemAndOpBus trace.programLength trace.program := by
    simpa only [retargetTable_of_ne source notMem] using hc
  simpa only [retargetTable_table] using trace.main_height source hs sourceMain index

/-- The existing chosen source, retargeted on exactly its old rows/data. -/
def erased_selected_table (trace : Legacy457.AcceptedZiskTrace n)
    (guard : MutableMemPresent (eraseLegacyMem trace.witness)) :
    { table : Table FGL //
      table ∈ (eraseLegacyMem trace.witness).allTables ∧
        table.component = Mem.componentWithDualMemBus ∧ 0 < table.table.length } :=
  let oldGuard := eraseLegacyMem_memPresent_source trace.witness guard
  let selected := trace.mem_replay_table oldGuard
  ⟨retargetTable selected.1,
    by
      rw [eraseLegacyMem_allTables]
      exact List.mem_map.mpr ⟨selected.1, selected.2.1, rfl⟩,
    retargetTable_mem_component selected.1 selected.2.2.1,
    by simpa only [retargetTable_table] using selected.2.2.2⟩

theorem erased_source_covers (trace : Legacy457.AcceptedZiskTrace n)
    (guard : MutableMemPresent (eraseLegacyMem trace.witness))
    (table : Table FGL) (ht : table ∈ (eraseLegacyMem trace.witness).allTables)
    (hc : table.component = Mem.componentWithDualMemBus) :
    table = (erased_selected_table trace guard).1 := by
  rw [eraseLegacyMem_allTables] at ht
  rcases List.mem_map.mp ht with ⟨source, hs, rfl⟩
  have sourceMem := historical_mem_source trace.witness source hs hc
  have covered := trace.mem_replay_source_covers
    (eraseLegacyMem_memPresent_source trace.witness guard) source hs sourceMem
  exact congrArg retargetTable covered

/-- Actual one-way old18 -> current18 accepted-trace construction. -/
def toCurrent (trace : Legacy457.AcceptedZiskTrace n) : AcceptedZiskTrace n where
  programLength := trace.programLength
  program := trace.program
  witness := eraseLegacyMem trace.witness
  constraints_hold := eraseLegacyMem_constraints trace.witness trace.constraints_hold
  channels_balanced := eraseLegacyMem_balancedChannels trace.witness trace.channels_balanced
  mem_replay_table := erased_selected_table trace
  mem_replay_source_covers := erased_source_covers trace
  transitions_hold := eraseLegacyMem_transitions trace.witness trace.transitions_hold
  cyclic_successor_transitions_hold :=
    eraseLegacyMem_cyclic trace.witness trace.cyclic_successor_transitions_hold
  main_height := erased_main_height trace

@[simp] theorem toCurrent_programLength (trace : Legacy457.AcceptedZiskTrace n) :
    (toCurrent trace).programLength = trace.programLength := rfl

@[simp] theorem toCurrent_program (trace : Legacy457.AcceptedZiskTrace n) :
    (toCurrent trace).program = trace.program := rfl

@[simp] theorem toCurrent_witness (trace : Legacy457.AcceptedZiskTrace n) :
    (toCurrent trace).witness = eraseLegacyMem trace.witness := rfl

/-- Proof irrelevance changes no selected source or raw data. -/
theorem toCurrent_memReplayTable (trace : Legacy457.AcceptedZiskTrace n)
    (currentGuard : MutableMemPresent (toCurrent trace).witness)
    (oldGuard : Legacy457.MutableMemPresent trace.witness) :
    (toCurrent trace).memReplayTable currentGuard =
      retargetTable (trace.memReplayTable oldGuard) := rfl

theorem toCurrent_memReplayTable_rawRows (trace : Legacy457.AcceptedZiskTrace n)
    (currentGuard : MutableMemPresent (toCurrent trace).witness)
    (oldGuard : Legacy457.MutableMemPresent trace.witness) :
    ((toCurrent trace).memReplayTable currentGuard).rawRows =
      (trace.memReplayTable oldGuard).rawRows := by
  rw [toCurrent_memReplayTable trace currentGuard oldGuard, retargetTable_rawRows]

theorem toCurrent_memReplayTable_data (trace : Legacy457.AcceptedZiskTrace n)
    (currentGuard : MutableMemPresent (toCurrent trace).witness)
    (oldGuard : Legacy457.MutableMemPresent trace.witness) :
    ((toCurrent trace).memReplayTable currentGuard).data =
      (trace.memReplayTable oldGuard).data := by
  rw [toCurrent_memReplayTable trace currentGuard oldGuard, retargetTable_data]

theorem toCurrent_memReplayTable_table (trace : Legacy457.AcceptedZiskTrace n)
    (currentGuard : MutableMemPresent (toCurrent trace).witness)
    (oldGuard : Legacy457.MutableMemPresent trace.witness) :
    ((toCurrent trace).memReplayTable currentGuard).table =
      (trace.memReplayTable oldGuard).table := by
  rw [toCurrent_memReplayTable trace currentGuard oldGuard, retargetTable_table]

theorem toCurrent_memReplayTable_fixedAt (trace : Legacy457.AcceptedZiskTrace n)
    (currentGuard : MutableMemPresent (toCurrent trace).witness)
    (oldGuard : Legacy457.MutableMemPresent trace.witness) (slot row : Nat) :
    ((toCurrent trace).memReplayTable currentGuard).fixedAt slot row =
      (trace.memReplayTable oldGuard).fixedAt slot row := by
  rw [toCurrent_memReplayTable trace currentGuard oldGuard, retargetTable_fixedAt]

end
end ZiskFv.Compliance.MemDomainComparison
