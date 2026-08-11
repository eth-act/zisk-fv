import ZiskFv.Soundness
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification

/-!
# Degenerate `stepSound_of_programDecodes` instantiation (end-to-end integration witness, base case)

The first concrete inhabitant of `ZiskFv.Compliance.AcceptedZiskTrace` fed through
`ZiskFv.Compliance.stepSound_of_programDecodes` (eth-act/zisk-fv#217, foundation of #74).

This is the DEGENERATE base case: `numInstructions = 0`, every provider table empty.
It exercises the whole witness-construction pipeline — the 11-table
`EnsembleWitness` (`same_length`/`same_circuits`/`same_data`), `constraints_hold`,
    `transitions_hold`, and the first forward `BalancedChannels`
proof — and applies `stepSound_of_programDecodes` to the result. The `∀ i : Fin 0` conclusion
is vacuous, so this establishes only that the quantified-over trace object is
INHABITED and accepted; the non-vacuous single-ADD instance is #219/#220. No new
axioms, no `sorry`.

## Regeneration

The trace is hand-authored (not dumped from an execution): the empty program
`nofun : Program 0` has no rows, so there are no literals to regenerate. #220 will
add the first witness with real row literals.
-/

namespace ZiskFv.TrustConsistency

open Goldilocks
open Air.Flat
open ZiskFv.Compliance
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble fullRv64imSoundEnsemble)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

/-- The empty 0-instruction program. -/
private def prog : Program 0 := nofun

private def emptyData : ProverData FGL := fun _ _ => #[]

/-- The degenerate witness: every one of the ensemble's tables carries no rows. -/
private def wit : EnsembleWitness (fullRv64imEnsemble 0 prog).ensemble :=
  EnsembleWitness.ofRows (fullRv64imEnsemble 0 prog).ensemble emptyData ()
    (fun _ => []) (by intro i row hrow; simp at hrow)
    (by intro i columns h_columns; simp)

/-- The full ensemble's verifier is empty (it is `SoundEnsemble.empty`'s verifier,
    preserved by `addTable`/`addFinishedChannel`; `fullRv64imEnsemble` is
    definitionally its `SoundEnsemble`'s ensemble). -/
private theorem wit_verifier :
    (fullRv64imEnsemble 0 prog).ensemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 0 prog).verifier_empty

/-- Every table of the degenerate witness has at most one row: the provider
    tables are empty (0 rows) and the verifier table carries the single public
    input row. Provider transitions are vacuous; the verifier's row-zero-saturated
    default transition is trivial. -/
private theorem wit_tables_len_le_one (table : Table FGL)
    (hmem : table ∈ wit.allTables) : table.table.length ≤ 1 := by
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · rw [hv]; simp [EnsembleWitness.verifierTable]
  · simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [EnsembleWitness.tableAt, Table.table]
    split <;> simp

/-- Any mutable-Mem component table in the degenerate witness is empty. The verifier table is
    ruled out by its empty MemBus interaction list, while every provider table is empty by
    construction. -/
private theorem mutable_mem_component_tables_empty (table : Table FGL)
    (hmem : table ∈ wit.allTables)
    (hcomp : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · exfalso
    rw [hv, EnsembleWitness.verifierTable_component] at hcomp
    have hv_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 0 prog
    rw [hcomp,
      ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at hv_nil
    exact absurd hv_nil (by simp)
  · simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [EnsembleWitness.tableAt, Table.table]
    split <;> rfl

private theorem wit_not_mutableMemPresent : ¬ MutableMemPresent wit := by
  intro h_present
  obtain ⟨table, hmem, hcomp, hlen⟩ := h_present
  have htab := mutable_mem_component_tables_empty table hmem hcomp
  exact absurd hlen (by simp [htab])

private theorem wit_constraints : wit.Constraints := by
  refine wit.constraints_of_tables wit_verifier ?_
  intro t ht
  simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
  obtain ⟨i, rfl⟩ := ht
  simp [Air.Flat.Table.Constraints, EnsembleWitness.tableAt, Table.table]
  split <;> simp

private theorem wit_balanced : wit.BalancedChannels := by
  refine wit.balancedChannels_of_tables wit_verifier ?_
  intro channel _
  have hnil : wit.tables.flatMap (·.interactionsWith channel) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro t ht
    simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [Air.Flat.Table.interactionsWith, EnsembleWitness.tableAt, Table.table]
    split <;> simp
  rw [hnil]
  exact balancedInteractions_of_present (Or.symm (Nat.eq_zero_or_pos _)) []
    (by simp) (by simp)

private theorem wit_transitions : wit.TransitionConstraints := by
  intro table hmem
  rw [Table.TransitionConstraints]
  intro index
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with h_verifier | h_table
  · subst table
    simp [EnsembleWitness.verifierTable]
  · simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at h_table
    obtain ⟨i, rfl⟩ := h_table
    change Fin 0 at index
    exact Fin.elim0 index

private theorem wit_cyclicSuccessorTransitions : wit.CyclicSuccessorTransitionConstraints := by
  intro table hmem
  rw [Table.CyclicSuccessorTransitionConstraints]
  intro index
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with h_verifier | h_table
  · subst table
    simp [EnsembleWitness.verifierTable]
  · simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at h_table
    obtain ⟨i, rfl⟩ := h_table
    change Fin 0 at index
    exact Fin.elim0 index

/-- The degenerate accepted trace: empty program, all-empty witness, trivial
    channel balance, and vacuous transition / row-height obligations. -/
private def trace : AcceptedZiskTrace 0 where
  programLength := 0
  program := prog
  witness := wit
  constraints_hold := wit_constraints
  channels_balanced := wit_balanced
  mem_replay_table := fun h => absurd h wit_not_mutableMemPresent
  mem_replay_source_covers := fun h => absurd h wit_not_mutableMemPresent
  transitions_hold := wit_transitions
  cyclic_successor_transitions_hold := wit_cyclicSuccessorTransitions
  main_height := by intro table _ _ i; exact i.elim0

private def sail : SailTrace 0 := nofun

private def step : ∀ i : Fin 0, ZiskStep trace i := nofun
private def decode : ∀ i : Fin 0, ProgramDecode trace i (step i) := nofun

/-- The degenerate boot / cross-segment memory seed: empty boot memory, no rows,
    and every per-instruction obligation vacuous over `Fin 0`.  With the concrete
    seed form (#115) the seed carries real fields (`memInit`/`rowsOf` plus guarded
    read-soundness inputs), so it is given explicitly rather than the old `nomatch`. -/
private def seed : BootSegmentMemorySeed trace sail step where
  memInit := {}
  rowsOf := fun _ => []
  boot := fun h => absurd h (Nat.not_lt_zero _)
  step := fun _ h => absurd h (Nat.not_lt_zero _)
  readSoundInputs := fun h => absurd h wit_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_ne
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_ne
  placement := fun i => i.elim0

/-- The PC premises for the degenerate execution (#330). All of them are vacuous for the
    same reason `seed`'s are: there is no step `0`, and no step `j + 1`. -/
def pcChain : SegmentPcChain trace sail step where
  retire := fun _ h => absurd h (Nat.not_lt_zero _)
  boot := fun h => absurd h (Nat.not_lt_zero _)

/-- #330 Phase 7: vacuous on the degenerate execution. -/
def rowsAligned :
    StepRowsAligned trace step (fun i => rowDecode_of_programDecode trace i (decode i)) :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- `stepSound_of_programDecodes` applied to a concrete (degenerate) accepted trace. The `Fin 0`
    conclusion is vacuous, but the term genuinely constructs an `AcceptedZiskTrace`
    and feeds it through the headline theorem — witnessing that the object
    `stepSound_of_programDecodes` quantifies over is inhabited and accepted. -/
theorem root_soundness_instantiation_degenerate :
    ∀ i : Fin 0,
      StepSound trace sail i (step i)
        (rowDecode_of_programDecode trace i (decode i)) :=
  stepSound_of_programDecodes 0 trace sail step decode nofun pcChain rowsAligned seed nofun

#print axioms root_soundness_instantiation_degenerate

end ZiskFv.TrustConsistency
