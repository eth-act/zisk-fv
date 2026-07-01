import ZiskFv.Soundness
import ZiskFv.Compliance.EnsembleWitnessBuilder
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification

/-!
# Degenerate `root_soundness` instantiation (end-to-end integration witness, base case)

The first concrete inhabitant of `ZiskFv.Compliance.AcceptedZiskTrace` fed through
`ZiskFv.Compliance.root_soundness` (eth-act/zisk-fv#217, foundation of #74).

This is the DEGENERATE base case: `numInstructions = 0`, every provider table empty.
It exercises the whole witness-construction pipeline — the 10-table
`EnsembleWitness` (`same_length`/`same_circuits`/`same_data`), `constraints_hold`,
`transitions_hold`, `segment_l1_fixed`, and the first forward `BalancedChannels`
proof — and applies `root_soundness` to the result. The `∀ i : Fin 0` conclusion
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

/-- The full ensemble's verifier is empty (it is `SoundEnsemble.empty`'s verifier,
    preserved by `addTable`/`addFinishedChannel`; `fullRv64imEnsemble` is
    definitionally its `SoundEnsemble`'s ensemble). -/
private theorem wit_verifier :
    (fullRv64imEnsemble 0 prog).ensemble.verifier = .empty FGL unit :=
  (fullRv64imSoundEnsemble 0 prog).verifier_empty

/-- Every table of the degenerate witness has at most one row: the provider
    tables are empty (0 rows) and the verifier table carries the single public
    input row. This is what makes `transitions_hold` vacuous (no consecutive row
    pair exists). -/
private theorem wit_tables_len_le_one (table : Table FGL)
    (hmem : table ∈ wit.allTables) : table.table.length ≤ 1 := by
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · rw [hv]; simp [EnsembleWitness.verifierTable]
  · simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [EnsembleWitness.tableAt_table]

/-- The only table of the degenerate witness carrying the Main component has no
    rows. The provider tables are empty by construction; the single non-empty
    table is the verifier, whose component exposes NO operation-bus interactions
    (`verifierTable_interactionsWith_opBus_nil`) while Main's are a non-empty
    singleton (`componentWithRomMemAndOpBus_interactionsWith_opBus`), so the
    verifier's component cannot equal Main's. This makes `segment_l1_fixed`
    vacuous. -/
private theorem main_component_tables_empty (table : Table FGL)
    (hmem : table ∈ wit.allTables)
    (hcomp : table.component =
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 0 prog) :
    table.table = [] := by
  rw [EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · exfalso
    rw [hv, EnsembleWitness.verifierTable_component] at hcomp
    have hv_nil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_opBus_nil 0 prog
    rw [hcomp,
      ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_interactionsWith_opBus 0 prog] at hv_nil
    exact absurd hv_nil (by simp)
  · simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [EnsembleWitness.tableAt_table]

private theorem wit_constraints : wit.Constraints := by
  refine wit.constraints_of_tables wit_verifier ?_
  intro t ht
  simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
  obtain ⟨i, rfl⟩ := ht
  simp [Air.Flat.Table.Constraints, EnsembleWitness.tableAt_table]

private theorem wit_balanced : wit.BalancedChannels := by
  refine wit.balancedChannels_of_tables wit_verifier ?_
  intro channel _
  have hnil : wit.tables.flatMap (·.interactionsWith channel) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro t ht
    simp only [wit, EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [Air.Flat.Table.interactionsWith, EnsembleWitness.tableAt_table]
  rw [hnil]
  exact balancedInteractions_of_present (Or.symm (Nat.eq_zero_or_pos _)) []
    (by simp) (by simp)

private theorem wit_transitions : wit.TransitionConstraints := by
  intro table hmem i h
  exact absurd h (by have := wit_tables_len_le_one table hmem; omega)

private theorem wit_segment_l1 :
    ∀ table ∈ wit.allTables,
      table.component =
          ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus 0 prog →
        (0 < table.table.length →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable prog table).segment_l1 0 = 1) ∧
        (∀ idx : Fin table.table.length, 0 < idx.val →
            (ZiskFv.AirsClean.FullEnsemble.mainOfTable prog table).segment_l1 idx.val = 0) := by
  intro table hmem hcomp
  have htab : table.table = [] := main_component_tables_empty table hmem hcomp
  exact ⟨fun h => absurd h (by simp [htab]), fun idx _ => absurd idx.isLt (by simp [htab])⟩

/-- The degenerate accepted trace: empty program, all-empty witness, trivial
    channel balance, vacuous transition / row-height / segment-fixed obligations. -/
private def trace : AcceptedZiskTrace 0 where
  program := prog
  witness := wit
  constraints_hold := wit_constraints
  channels_balanced := wit_balanced
  transitions_hold := wit_transitions
  main_height := by intro table _ _ i; exact i.elim0
  segment_l1_fixed := wit_segment_l1

private def sail : SailTrace 0 := nofun

private def step : ∀ i : Fin 0, ZiskStep trace i := nofun

/-- `root_soundness` applied to a concrete (degenerate) accepted trace. The `Fin 0`
    conclusion is vacuous, but the term genuinely constructs an `AcceptedZiskTrace`
    and feeds it through the headline theorem — witnessing that the object
    `root_soundness` quantifies over is inhabited and accepted. -/
theorem root_soundness_instantiation_degenerate :
    ∀ i : Fin 0, StepSound trace sail i (step i) :=
  root_soundness 0 trace sail step nofun nofun nofun

#print axioms root_soundness_instantiation_degenerate

end ZiskFv.TrustConsistency
