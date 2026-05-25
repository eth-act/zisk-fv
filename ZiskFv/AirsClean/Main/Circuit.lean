import ZiskFv.AirsClean.Main.Constraints
import ZiskFv.AirsClean.Main.Soundness
import ZiskFv.AirsClean.Main.Bridge
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Main Clean Component

Packages the Main AIR's per-row constraints plus its assume-side operation-bus
emission as a Clean `Air.Flat.Component`.

The base `Constraints.main` definition remains the extracted nine F-typed
constraints. This component uses `mainWithOpBus`, which appends the
PIL-faithful operation-bus emission with multiplicity `-is_external_op`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

def circuit : GeneralFormalCircuit FGL MainRow unit :=
  { mainWithOpBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
        exact ⟨ by simpa [sub_eq_add_neg] using h0
              , by simpa [sub_eq_add_neg] using h1
              , by simpa [sub_eq_add_neg] using h2
              , by simpa [sub_eq_add_neg] using h3
              , by simpa [sub_eq_add_neg] using h4
              , by simpa [sub_eq_add_neg] using h5
              , by simpa [sub_eq_add_neg] using h6
              , by simpa [sub_eq_add_neg] using h7
              , by simpa [sub_eq_add_neg] using h8 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      simpa [sub_eq_add_neg] using h_assumptions }

def component : Air.Flat.Component FGL := ⟨ circuit ⟩

theorem component_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr component.rowInputVar) =
      opBusMessage (component.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env))

/-- The Main component exposes exactly its one operation-bus interaction.
    This keeps later C7 balance projections from unfolding the nine local
    constraints just to recover the channel message. -/
theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.emitted (-component.rowInputVar.is_external_op)
          (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.emitted (-component.rowInputVar.is_external_op)
          (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, mainWithOpBusElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

/-- Project the `is_external_op` boolean assertion from the concrete
    `mainWithOpBus` operations without unfolding the whole Component `Spec`.

This is the local Main-side fact C7 needs to prove that Main op-bus
interactions have only multiplicity `-1` or `0`. -/
theorem is_external_op_boolean_of_mainWithOpBus_constraints
    (row : Var MainRow FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds : Operations.ConstraintsHold env ((mainWithOpBus row).operations offset)) :
    env (row.is_external_op * (1 - row.is_external_op)) = 0 := by
  simp only [mainWithOpBus, main, circuit_norm] at h_holds
  exact h_holds (row.is_external_op * (1 - row.is_external_op)) (Or.inr (Or.inl rfl))

/-- Component-level adapter for the Main `is_external_op` boolean assertion.

This is the Clean-flat idiom: first project `component.operations` to the
per-row `rowOperations` via `Component.constraintsHold_iff`, then unfold only
the local Main component wrapper. -/
theorem is_external_op_boolean_of_component_constraints
    (env : Environment FGL)
    (h_holds : component.operations.ConstraintsHold env) :
    env (component.rowInputVar.is_external_op * (1 - component.rowInputVar.is_external_op)) = 0 := by
  have h_row : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff (component := component) env).mp h_holds
  exact is_external_op_boolean_of_mainWithOpBus_constraints
    component.rowInputVar component.rowOffset env (by
      simpa only [component, circuit, Component.rowOperations] using h_row)

theorem spec_via_component (row : MainRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  exact h_constraints

end ZiskFv.AirsClean.Main
