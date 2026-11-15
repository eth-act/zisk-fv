import ZiskFv.Compliance.TraceLevelExport.MappedSourceSailChain

/-!
# Bounded transport from the old Sail chain to canonical source starts

The old trace counts architectural instructions; the canonical trace counts
physical rows. Equality of the actual instructions at the computed source
starts identifies their complete Sail states through the final architectural
post-state. No equation between physical starts and architectural indices is
assumed, and no step is requested at the final post-state.

The soundness transport uses the existing `stepSound_iff` interface and equality
of actual channel outputs. These internal comparison hypotheses are intended to
be discharged by concrete same-witness reindexing, not added to a root interface.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open CanonicalExecutionRows

variable {n : Nat} {words : Fin n → BitVec 32}
variable (L : ∀ i, SuccessfulRowLowering (words i))
variable {oldTrace : AcceptedZiskTrace n}
variable {newTrace : AcceptedZiskTrace (sourceEnd L)}
variable (oldSteps : ∀ i : Fin n, ZiskStep oldTrace i)
variable (newSteps : ∀ i : Fin n, ZiskStep newTrace (physicalStart L i))
variable (init : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)

/-- The bounded canonical recursion and the old architectural recursion agree
on whole states, including the genuine final post-state at `j = n`. The new
steps are required only at real physical source starts. -/
theorem mappedSailStates_eq_chainedSailStates
    (instruction_eq : ∀ i : Fin n,
      sailInstructionOf (physicalStart L i) (newSteps i) =
        sailInstructionOf i (oldSteps i))
    (j : Nat) (hj : j ≤ n) :
    mappedSailStates L newSteps init j hj = chainedSailStates oldSteps init j := by
  revert hj
  induction j with
  | zero =>
      intro hj
      rfl
  | succ j ih =>
      intro hj
      have hlt : j < n := Nat.lt_of_succ_le hj
      calc
        mappedSailStates L newSteps init (j + 1) hj =
            retirePC (sailStepPost
              (sailInstructionOf (physicalStart L ⟨j, hlt⟩) (newSteps ⟨j, hlt⟩))
              (mappedSailStates L newSteps init j (Nat.le_of_lt hlt))) := rfl
        _ = retirePC (sailStepPost
              (sailInstructionOf ⟨j, hlt⟩ (oldSteps ⟨j, hlt⟩))
              (chainedSailStates oldSteps init j)) := by
          rw [instruction_eq ⟨j, hlt⟩, ih (Nat.le_of_lt hlt)]
        _ = chainedSailStates oldSteps init (j + 1) := by
          symm
          rw [chainedSailStates, dif_pos hlt]

/-- Actual source starts carry exactly the old architectural pre-states. This
is equality of the entire Sail state, not merely its PC or register projection. -/
theorem mappedSailTrace_start_eq_chainedSailTrace
    (instruction_eq : ∀ i : Fin n,
      sailInstructionOf (physicalStart L i) (newSteps i) =
        sailInstructionOf i (oldSteps i))
    (i : Fin n) :
    mappedSailTrace L newSteps init (physicalStart L i) =
      chainedSailTrace oldSteps init i := by
  rw [state_at_start, chainedSailTrace_apply]
  exact mappedSailStates_eq_chainedSailStates L oldSteps newSteps init
    instruction_eq i.val (Nat.le_of_lt i.isLt)

/-- The final architectural post-state is transported without introducing a
`Fin (n + 1)` step family or selecting a fictitious old instruction at `n`. -/
theorem mappedSailStates_final_eq_chainedSailStates
    (instruction_eq : ∀ i : Fin n,
      sailInstructionOf (physicalStart L i) (newSteps i) =
        sailInstructionOf i (oldSteps i)) :
    mappedSailStates L newSteps init n (Nat.le_refl n) =
      chainedSailStates oldSteps init n :=
  mappedSailStates_eq_chainedSailStates L oldSteps newSteps init
    instruction_eq n (Nat.le_refl n)

/-- Old soundness transports to the actual canonical source-start steps using
only equal actual instructions, equal actual channel outputs, and the proved
whole-state comparison. No opcode dispatch or auxiliary Sail step is needed. -/
theorem mappedStepSound_of_old
    (oldDecoded : ∀ i : Fin n, RowDecode oldTrace i (oldSteps i))
    (newDecoded : ∀ i : Fin n,
      RowDecode newTrace (physicalStart L i) (newSteps i))
    (instruction_eq : ∀ i : Fin n,
      sailInstructionOf (physicalStart L i) (newSteps i) =
        sailInstructionOf i (oldSteps i))
    (channel_eq : ∀ i : Fin n,
      stepChannelOutput (physicalStart L i) (newSteps i) (newDecoded i) =
        stepChannelOutput i (oldSteps i) (oldDecoded i))
    (oldSound : ∀ i : Fin n,
      StepSound oldTrace (chainedSailTrace oldSteps init) i (oldSteps i) (oldDecoded i)) :
    ∀ i : Fin n,
      StepSound newTrace (mappedSailTrace L newSteps init)
        (physicalStart L i) (newSteps i) (newDecoded i) := by
  intro i
  apply (stepSound_iff (physicalStart L i) (newSteps i) (newDecoded i)).mpr
  change execute_instruction
      (sailInstructionOf (physicalStart L i) (newSteps i))
      (mappedSailTrace L newSteps init (physicalStart L i)) =
    ZiskFv.Channels.state_effect_via_channels
      (stepChannelOutput (physicalStart L i) (newSteps i) (newDecoded i))
      (mappedSailTrace L newSteps init (physicalStart L i))
  rw [instruction_eq i,
    mappedSailTrace_start_eq_chainedSailTrace L oldSteps newSteps init instruction_eq i,
    channel_eq i]
  exact (stepSound_iff i (oldSteps i) (oldDecoded i)).mp (oldSound i)

end ZiskFv.Compliance.SerializedExecutionRows
