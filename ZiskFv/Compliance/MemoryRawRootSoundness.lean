import ZiskFv.Soundness
import ZiskFv.Compliance.TraceLevelExport.RawProgramBindingMemoryNonvacuity

/-!
# Memory raw-program root soundness (non-vacuity)

A concrete instantiation of `ZiskFv.Compliance.root_soundness` (eth-act/zisk-fv#320) on
the all-empty-execution MEMORY witness (`memoryAcceptedTrace` from
`RawProgramBindingMemoryNonvacuity.lean`, `numInstructions = 0`, `programLength = 3`),
using the already-proven `memoryProgramRowsBinding` as the real `programBinding` premise
— not a placeholder. This strengthens `root_soundness_instantiation_degenerate`, which
exercises the same empty-execution shape but with no binding evidence at all.

The conclusion and every per-step premise are vacuous over `Fin 0`, as expected for an
empty execution; the point of this probe is that `programBinding` is a genuine,
production-faithful `ProgramRowsBinding` witness, not that the conclusion is
non-vacuous (that is #219/#220's job for the per-op soundness lemmas).

`memoryAcceptedTrace_not_mutableMemPresent` re-derives (from public API only) the fact
that the memory witness in `RawProgramBindingMemoryNonvacuity.lean` carries no mutable-Mem
rows. The original proof of this fact (`memoryWitness_not_mutableMemPresent`) is `private`
to that file, so it is re-derived here from `memoryAcceptedTrace.witness`'s public
definitional content rather than duplicated by widening that file's public surface.
-/

namespace ZiskFv.Compliance.MemoryRawRootSoundness

open ZiskFv.Compliance
open ZiskFv.Compliance.RawProgramBinding
  (memoryAcceptedTrace memoryAddr memoryRawProgram memoryStart memoryProgram
    memoryProgramRowsBinding)
open ZiskFv.AirsClean.FullEnsemble (fullRv64imEnsemble)

/-- `memoryAcceptedTrace.witness`'s definitional content, spelled out via the same
    public `EnsembleWitness.ofRows` constructor `RawProgramBindingMemoryNonvacuity.lean`
    used for its (private) `memoryWitness`. Provable by `rfl`: both sides reduce to the
    identical `EnsembleWitness.ofRows` application (the two `by`-proofs are proof-irrelevant). -/
private theorem memoryAcceptedTrace_witness_eq :
    memoryAcceptedTrace.witness =
      Air.Flat.EnsembleWitness.ofRows (fullRv64imEnsemble 3 memoryProgram).ensemble
        (fun (_ : String) (_ : ℕ) => (#[] : Array (Vector FGL _)))
        () (fun _ => [])
        (by intro i row hrow; simp at hrow)
        (by intro i columns _hcolumns; simp) :=
  rfl

/-- Every mutable-Mem-component table of the memory witness is empty: the verifier table
    is ruled out by its empty MemBus interaction list, and every provider table is empty
    by construction (`fun _ => []`). Mirrors `memoryWitness_mutable_tables_empty` in
    `RawProgramBindingMemoryNonvacuity.lean`, re-derived here via
    `memoryAcceptedTrace_witness_eq` instead of that file's private `memoryWitness`. -/
private theorem memoryAcceptedTrace_mutable_tables_empty (table : Air.Flat.Table FGL)
    (hmem : table ∈ memoryAcceptedTrace.witness.allTables)
    (hcomp : table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus) :
    table.table = [] := by
  rw [memoryAcceptedTrace_witness_eq, Air.Flat.EnsembleWitness.allTables, List.mem_cons] at hmem
  rcases hmem with hv | ht
  · exfalso
    have hcomp' : (fullRv64imEnsemble 3 memoryProgram).ensemble.verifierTable =
        ZiskFv.AirsClean.Mem.componentWithDualMemBus := by
      subst hv
      exact hcomp
    have hvnil :=
      ZiskFv.AirsClean.FullEnsemble.verifierTable_interactionsWith_memBus_nil 3 memoryProgram
    rw [hcomp', ZiskFv.AirsClean.Mem.componentWithDualMemBus_interactionsWith_memBus] at hvnil
    exact absurd hvnil (by simp)
  · simp only [Air.Flat.EnsembleWitness.ofRows_tables, List.mem_ofFn] at ht
    obtain ⟨i, rfl⟩ := ht
    simp [Air.Flat.EnsembleWitness.tableAt, Air.Flat.Table.table]
    split <;> rfl

/-- The memory witness carries no mutable-Mem replay evidence. -/
private theorem memoryAcceptedTrace_not_mutableMemPresent :
    ¬ MutableMemPresent memoryAcceptedTrace.witness := by
  intro hpresent
  obtain ⟨table, hmem, hcomp, hlen⟩ := hpresent
  have htable := memoryAcceptedTrace_mutable_tables_empty table hmem hcomp
  exact absurd hlen (by simp [htable])

/-- The empty Sail trace over the empty execution. -/
def memorySailTrace : SailTrace 0 := nofun

/-- The empty per-step ZisK decode family over the empty execution. -/
def memoryZiskStep : ∀ i : Fin 0, ZiskStep memoryAcceptedTrace i := nofun

/-- The boot / cross-segment memory seed for the memory witness: empty boot memory, no
    execution-order rows, and every per-index obligation either vacuous over `Fin 0`
    (`boot`, `step`, `placement`) or discharged by `memoryAcceptedTrace_not_mutableMemPresent`
    (`readSoundInputs`) / `List.range_zero` (`memPresent_of_executionRows_nonempty`).
    Mirrors `addPaddedBootSeed` (`ZiskFv/Compliance/AddSpinRootSoundness.lean:404-422`). -/
def memoryBootSeed :
    BootSegmentMemorySeed memoryAcceptedTrace memorySailTrace memoryZiskStep where
  memInit := {}
  rowsOf := fun _ => []
  boot := fun h => absurd h (Nat.not_lt_zero _)
  step := fun _ h => absurd h (Nat.not_lt_zero _)
  readSoundInputs := fun h => absurd h memoryAcceptedTrace_not_mutableMemPresent
  memPresent_of_executionRows_nonempty := by
    intro h_ne
    exact absurd (by simp [AcceptedZiskTrace.numInstructions]) h_ne
  placement := fun i => i.elim0

/-- The PC premises for the empty execution. All of them are vacuous here for the same
    reason `memoryBootSeed`'s are: there is no step `0`, and no step `j + 1`. -/
def memoryPcChain :
    SegmentPcChain memoryAcceptedTrace memorySailTrace memoryZiskStep where
  retire := fun _ h => absurd h (Nat.not_lt_zero _)
  boot := fun h => absurd h (Nat.not_lt_zero _)

def memoryRowsAligned :
    StepRowsAligned memoryAcceptedTrace memoryZiskStep
      (fun i => rowDecode_of_programDecode memoryAcceptedTrace i
        (programDecode_of_rawProgramDecode memoryAcceptedTrace i (memoryZiskStep i)
          memoryStart memoryAddr memoryRawProgram memoryProgramRowsBinding i.elim0)) :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- `root_soundness` instantiated on the memory witness with the real, already-proven
    `memoryProgramRowsBinding` as `programBinding` — strengthening
    `root_soundness_instantiation_degenerate`, which uses the same empty-execution shape
    but no binding evidence. The `∀ i : Fin 0` conclusion is vacuous, as expected for an
    all-empty execution; the substance is that `programBinding` is genuine. -/
theorem memoryRawRootSoundness :
    ∀ i : Fin 0,
      StepSound memoryAcceptedTrace memorySailTrace i (memoryZiskStep i)
        (rowDecode_of_programDecode memoryAcceptedTrace i
          (programDecode_of_rawProgramDecode memoryAcceptedTrace i (memoryZiskStep i)
            memoryStart memoryAddr memoryRawProgram memoryProgramRowsBinding i.elim0)) :=
  root_soundness 0 3 memoryAcceptedTrace memorySailTrace memoryZiskStep
    memoryStart memoryAddr memoryRawProgram memoryProgramRowsBinding
    (fun i => i.elim0) (fun i => i.elim0) memoryPcChain memoryRowsAligned memoryBootSeed
    (fun i => i.elim0)

#print axioms memoryRawRootSoundness

end ZiskFv.Compliance.MemoryRawRootSoundness
