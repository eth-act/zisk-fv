import ZiskFv.AirsClean.MemAlign.Constraints
import ZiskFv.AirsClean.MemAlign.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlign Clean Component

Packages the MemAlign AIR per-row constraints and its unified memory-bus
interaction as a Clean `Air.Flat.Component`.

The channel emission is structural: it adds no new row-level soundness
obligation because `MemBusChannel.Guarantees` is `True`. Cross-row
continuity remains in `CrossRow.lean`.

## Trust note

No axioms. Completeness is conditional on the same row `Spec`, following
the existing soundness-only pattern used by `AirsClean/Mem/Circuit.lean`.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)

set_option maxRecDepth 2000 in
def circuit : GeneralFormalCircuit FGL MemAlignRow unit :=
  { memAlignWithMemBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
          h12, h13, h14, h15⟩ := h_holds
        exact ⟨ by simpa only [sub_eq_add_neg] using h0
              , by simpa only [sub_eq_add_neg] using h1
              , by simpa only [sub_eq_add_neg] using h2
              , by simpa only [sub_eq_add_neg] using h3
              , by simpa only [sub_eq_add_neg] using h4
              , by simpa only [sub_eq_add_neg] using h5
              , by simpa only [sub_eq_add_neg] using h6
              , by simpa only [sub_eq_add_neg] using h7
              , by simpa only [sub_eq_add_neg] using h8
              , by simpa only [sub_eq_add_neg] using h9
              , by simpa only [sub_eq_add_neg] using h10
              , by simpa only [sub_eq_add_neg] using h11
              , by simpa only [sub_eq_add_neg] using h12
              , by simpa only [sub_eq_add_neg] using h13
              , by simpa only [sub_eq_add_neg] using h14
              , by simpa only [sub_eq_add_neg] using h15 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [MemBusChannel]
      simpa only [Spec, sub_eq_add_neg] using h_assumptions }

def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-- Project the generic Clean component `Spec` to the concrete MemAlign row
    `Spec`. -/
theorem component_spec (env : Environment FGL) :
    component.Spec env = Spec (component.rowInput env) := by
  rfl

/-- The MemAlign component exposes exactly its one memory-bus interaction. -/
theorem component_interactionsWith_memBus :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [((MemBusChannel.emitted
          (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
          (memBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [((MemBusChannel.emitted
          (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
          (memBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, memAlignWithMemBusElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

theorem spec_via_component (row : MemAlignRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  exact h_constraints

end ZiskFv.AirsClean.MemAlign
