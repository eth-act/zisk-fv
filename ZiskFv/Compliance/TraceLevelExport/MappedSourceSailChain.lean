import ZiskFv.Compliance.TraceLevelExport.CanonicalExecutionRows
import ZiskFv.Compliance.TraceLevelExport.ChainedSailTrace

/-!
# Source-derived physical ownership and architectural Sail execution

The physical endpoint and every owner are derived from successful source
lowerings. Sail executes once per source word, at its computed physical start;
auxiliary rows merely pull back that word's pre-state. The bounded recursion
also retains the final architectural post-state, without an out-of-range action
or a default state. Producer-PC projection below deliberately names the actual
producer successor, not an unproved next-source placement.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)

variable {m : Nat} {words : Fin m → BitVec 32}

/-- Every source start is strictly before the endpoint, since actual widths are
positive. This also handles the empty source without choosing a dummy word. -/
theorem sourceStart_lt_sourceEnd
    (L : ∀ i, SuccessfulRowLowering (words i)) (i : Fin m) :
    sourceStart L i < sourceEnd L := by
  have hs := prefix_succ (sourceWidth L) i
  have hm := prefix_mono (sourceWidth L) (Nat.succ_le_of_lt i.isLt)
  have hp := (L i).width_pos
  change rowPrefix (sourceWidth L) i.val < rowPrefix (sourceWidth L) m
  change 0 < sourceWidth L i at hp
  omega

/-- The physical start is computed from all preceding actual source widths. -/
def physicalStart (L : ∀ i, SuccessfulRowLowering (words i)) (i : Fin m) :
    Fin (sourceEnd L) :=
  ⟨sourceStart L i, sourceStart_lt_sourceEnd L i⟩

@[simp] theorem physicalStart_val
    (L : ∀ i, SuccessfulRowLowering (words i)) (i : Fin m) :
    (physicalStart L i).val = sourceStart L i := rfl

/-- The unique covering source interval determines ownership; there is no
caller-supplied row map, fallback owner, or nonempty-source premise. -/
noncomputable def physicalOwner
    (L : ∀ i, SuccessfulRowLowering (words i)) (r : Fin (sourceEnd L)) : Fin m :=
  Classical.choose (source_prefix_exact L r.val r.isLt).exists

theorem physicalOwner_spec
    (L : ∀ i, SuccessfulRowLowering (words i)) (r : Fin (sourceEnd L)) :
    sourceStart L (physicalOwner L r) ≤ r.val ∧
      r.val < sourceStart L (physicalOwner L r) + (L (physicalOwner L r)).width :=
  Classical.choose_spec (source_prefix_exact L r.val r.isLt).exists

/-- Precise whole-prefix uniqueness, including auxiliary physical rows. -/
theorem physicalOwner_unique
    (L : ∀ i, SuccessfulRowLowering (words i)) (r : Fin (sourceEnd L))
    (i : Fin m)
    (hi : sourceStart L i ≤ r.val ∧ r.val < sourceStart L i + (L i).width) :
    i = physicalOwner L r := by
  obtain ⟨j, _, unique⟩ := source_prefix_exact L r.val r.isLt
  exact (unique i hi).trans (unique (physicalOwner L r) (physicalOwner_spec L r)).symm

theorem physicalOwner_eq_iff
    (L : ∀ i, SuccessfulRowLowering (words i)) (r : Fin (sourceEnd L))
    (i : Fin m) :
    physicalOwner L r = i ↔
      sourceStart L i ≤ r.val ∧ r.val < sourceStart L i + (L i).width := by
  constructor
  · intro h
    simpa only [h] using physicalOwner_spec L r
  · intro hi
    exact (physicalOwner_unique L r i hi).symm

@[simp] theorem physicalOwner_start
    (L : ∀ i, SuccessfulRowLowering (words i)) (i : Fin m) :
    physicalOwner L (physicalStart L i) = i := by
  apply (physicalOwner_eq_iff L (physicalStart L i) i).mpr
  have hp := (L i).width_pos
  change sourceStart L i ≤ sourceStart L i ∧
    sourceStart L i < sourceStart L i + (L i).width
  omega

theorem physicalStart_strict
    (L : ∀ i, SuccessfulRowLowering (words i)) (i j : Fin m)
    (hij : i.val < j.val) : (physicalStart L i).val < (physicalStart L j).val :=
  source_starts_strict L i j hij

theorem physicalStart_injective
    (L : ∀ i, SuccessfulRowLowering (words i)) : Function.Injective (physicalStart L) := by
  intro i j h
  have howner := congrArg (physicalOwner L) h
  simpa only [physicalOwner_start] using howner

theorem physical_prefix_exact
    (L : ∀ i, SuccessfulRowLowering (words i)) (r : Fin (sourceEnd L)) :
    ∃! i : Fin m, (physicalStart L i).val ≤ r.val ∧
      r.val < (physicalStart L i).val + (L i).width :=
  source_prefix_exact L r.val r.isLt

/-- Source-layout coverage only: the genuine width-two JALR followed by a
width-one ADDI has owner sequence 0,0,1. No accepted execution is asserted. -/
theorem nonfinal_jalr_physical_owners :
    ∃ h0 : 0 < sourceEnd nonfinalJalrLowering,
      ∃ h1 : 1 < sourceEnd nonfinalJalrLowering,
        ∃ h2 : 2 < sourceEnd nonfinalJalrLowering,
          physicalOwner nonfinalJalrLowering ⟨0, h0⟩ = (0 : Fin 2) ∧
          physicalOwner nonfinalJalrLowering ⟨1, h1⟩ = (0 : Fin 2) ∧
          physicalOwner nonfinalJalrLowering ⟨2, h2⟩ = (1 : Fin 2) := by
  obtain ⟨hs0, hs1, hend, _⟩ := nonfinal_jalr_source_layout
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
  · apply (physicalOwner_eq_iff _ _ _).mpr
    simp only [hs0]
    have hw : (nonfinalJalrLowering (0 : Fin 2)).width = 2 := sourceJalrTwo_width
    simp [hw]
  · apply (physicalOwner_eq_iff _ _ _).mpr
    simp only [hs0]
    have hw : (nonfinalJalrLowering (0 : Fin 2)).width = 2 := sourceJalrTwo_width
    simp [hw]
  · apply (physicalOwner_eq_iff _ _ _).mpr
    simp only [hs1]
    have hw : (nonfinalJalrLowering (1 : Fin 2)).width = 1 := sourceAddiOne_width
    simp [hw]

section SailChain

variable (L : ∀ i, SuccessfulRowLowering (words i))
variable {trace : AcceptedZiskTrace (sourceEnd L)}
variable (steps : ∀ i : Fin m, ZiskStep trace (physicalStart L i))
variable (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)

/-- Bounded architectural recursion. Exactly one real instruction is executed
for each source word, including expanded source words; no auxiliary Sail action
is executed. The proof bound precludes any out-of-range branch. -/
noncomputable def mappedSailStates :
    (j : Nat) → j ≤ m → PreSail.SequentialState RegisterType Sail.trivialChoiceSource
  | 0, _ => init
  | j + 1, h =>
      retirePC (sailStepPost
        (sailInstructionOf (physicalStart L ⟨j, by omega⟩) (steps ⟨j, by omega⟩))
        (mappedSailStates j (by omega)))

@[simp] theorem mappedSailStates_zero (h : 0 ≤ m) :
    mappedSailStates L steps init 0 h = init := rfl

/-- Every physical row carries its owner's architectural pre-state. -/
noncomputable def mappedSailTrace : SailTrace (sourceEnd L) :=
  fun r => mappedSailStates L steps init (physicalOwner L r).val
    (Nat.le_of_lt (physicalOwner L r).isLt)

@[simp] theorem state_at_start (i : Fin m) :
    mappedSailTrace L steps init (physicalStart L i) =
      mappedSailStates L steps init i.val (Nat.le_of_lt i.isLt) := by
  simp only [mappedSailTrace, physicalOwner_start]

theorem state_at_owned_row (r : Fin (sourceEnd L)) (i : Fin m)
    (hi : sourceStart L i ≤ r.val ∧ r.val < sourceStart L i + (L i).width) :
    mappedSailTrace L steps init r =
      mappedSailStates L steps init i.val (Nat.le_of_lt i.isLt) := by
  simp only [mappedSailTrace, (physicalOwner_unique L r i hi).symm]

/-- Architectural successor, not physical-row successor. The final source word
also has a genuine architectural post-state at index m. -/
theorem mappedSailStates_succ (i : Fin m) :
    mappedSailStates L steps init (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      retirePC (sailStepPost (sailInstructionOf (physicalStart L i) (steps i))
        (mappedSailTrace L steps init (physicalStart L i))) := by
  rw [state_at_start]
  rfl

/-- Successful execution identifies the complete successor state, not only PC. -/
theorem mappedSailStates_retire (i : Fin m) (result : ExecutionResult)
    (post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (hstep : execute_instruction (sailInstructionOf (physicalStart L i) (steps i))
      (mappedSailTrace L steps init (physicalStart L i)) = .ok result post) :
    mappedSailStates L steps init (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      retirePC post := by
  rw [mappedSailStates_succ, sailStepPost, hstep]

/-- Physical starts of consecutive source words inherit the architectural
retire, irrespective of whether their distance is one or two. -/
theorem mappedSailTrace_retire (i j : Fin m) (hnext : j.val = i.val + 1)
    (result : ExecutionResult)
    (post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (hstep : execute_instruction (sailInstructionOf (physicalStart L i) (steps i))
      (mappedSailTrace L steps init (physicalStart L i)) = .ok result post) :
    mappedSailTrace L steps init (physicalStart L j) = retirePC post := by
  rw [state_at_start]
  simpa only [hnext] using mappedSailStates_retire L steps init i result post hstep

end SailChain

/-- Retire preserves all mutable Sail memory, in both nextPC branches. -/
theorem retirePC_mem
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    (retirePC s).mem = s.mem := by
  unfold retirePC
  cases s.regs.get? Register.nextPC <;> rfl

/-- Retire preserves every architectural general-register lookup. -/
theorem retirePC_general_register
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) (r : Fin 32) :
    (retirePC s).regs.get? (reg_of_fin r) = s.regs.get? (reg_of_fin r) := by
  apply retirePC_regs_of_ne
  fin_cases r <;> simp [reg_of_fin]

/-- Retire's PC projection, including the absent-nextPC case. -/
theorem retirePC_pc
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    (retirePC s).regs.get? Register.PC = s.regs.get? Register.nextPC := by
  unfold retirePC
  cases hnext : s.regs.get? Register.nextPC <;> simp

/-- Uniform soundness projection at an arbitrary actual physical start. The PC
is the actual decode-selected producer successor's PC; no next-source placement
is supplied or inferred here. -/
theorem stepSound_producer_nextPC {q : Nat} {trace : AcceptedZiskTrace q}
    {binding : SailTrace q} (r : Fin q) (zs : ZiskStep trace r)
    (rd : RowDecode trace r zs) (sound : StepSound trace binding r zs rd) :
    ∃ result post,
      execute_instruction (sailInstructionOf r zs) (binding r) = .ok result post ∧
      post.regs.get? Register.nextPC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc
            (stepProducerRow r zs rd + 1)).val) := by
  obtain ⟨result, post, hok⟩ := stepChannelOutput_busEffect_ok r zs rd (binding r)
  have hx := stepChannelOutput_execRows r zs rd
  have hlen : (stepChannelOutput r zs rd).execRows.length = 2 := by rw [hx]; rfl
  have he0 : (stepChannelOutput r zs rd).execRows[0]!.multiplicity = -1 := by
    rw [hx]; rfl
  have he1 : (stepChannelOutput r zs rd).execRows[1]!.multiplicity = 1 := by
    rw [hx]; rfl
  have heq : sailStepResult binding r zs = .ok result post := by
    rw [(stepSound_iff r zs rd).mp sound]
    exact hok
  refine ⟨result, post, heq, ?_⟩
  have hpc := nextPC_of_busEffect_ok _ _ _ _ _ hlen he0 he1 hok
  rw [hx] at hpc
  exact hpc

section ProducerChain

variable (L : ∀ i, SuccessfulRowLowering (words i))
variable {trace : AcceptedZiskTrace (sourceEnd L)}
variable (steps : ∀ i : Fin m, ZiskStep trace (physicalStart L i))
variable (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)

/-- Soundness at a deterministic source start composes with the architectural
recursion, without identifying producer+1 with the next source start. -/
theorem mappedSailStates_pc_of_stepSound (i : Fin m)
    (rd : RowDecode trace (physicalStart L i) (steps i))
    (sound : StepSound trace (mappedSailTrace L steps init)
      (physicalStart L i) (steps i) rd) :
    (mappedSailStates L steps init (i.val + 1)
      (Nat.succ_le_of_lt i.isLt)).regs.get? Register.PC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc
            (stepProducerRow (physicalStart L i) (steps i) rd + 1)).val) := by
  obtain ⟨result, post, hstep, hpc⟩ :=
    stepSound_producer_nextPC (physicalStart L i) (steps i) rd sound
  rw [mappedSailStates_retire L steps init i result post hstep, retirePC_pc, hpc]

theorem mappedSailTrace_pc_of_stepSound (i j : Fin m)
    (hnext : j.val = i.val + 1)
    (rd : RowDecode trace (physicalStart L i) (steps i))
    (sound : StepSound trace (mappedSailTrace L steps init)
      (physicalStart L i) (steps i) rd) :
    (mappedSailTrace L steps init (physicalStart L j)).regs.get? Register.PC =
        some (register_type_pc_equiv ▸ BitVec.ofNat 64
          ((mainOfTable trace.program trace.mainTable).pc
            (stepProducerRow (physicalStart L i) (steps i) rd + 1)).val) := by
  rw [state_at_start]
  simpa only [hnext] using mappedSailStates_pc_of_stepSound L steps init i rd sound

/-- Memory and general-register chaining follows from actual execution and
retire alone; auxiliary physical rows introduce no additional Sail effect. -/
theorem mappedSailTrace_preserves_post (i j : Fin m)
    (hnext : j.val = i.val + 1) (result : ExecutionResult)
    (post : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (hstep : execute_instruction (sailInstructionOf (physicalStart L i) (steps i))
      (mappedSailTrace L steps init (physicalStart L i)) = .ok result post) :
    (mappedSailTrace L steps init (physicalStart L j)).mem = post.mem ∧
      ∀ r : Fin 32,
        (mappedSailTrace L steps init (physicalStart L j)).regs.get? (reg_of_fin r) =
          post.regs.get? (reg_of_fin r) := by
  rw [mappedSailTrace_retire L steps init i j hnext result post hstep]
  exact ⟨retirePC_mem post, retirePC_general_register post⟩

end ProducerChain

end ZiskFv.Compliance.SerializedExecutionRows
