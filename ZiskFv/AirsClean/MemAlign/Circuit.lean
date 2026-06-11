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

No axioms. Completeness is intentionally a visible non-claim, following the
soundness-only project boundary.
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
    -- Completeness is intentionally NOT claimed (zisk-fv is soundness-
    -- only). `ProverAssumptions := False` makes this field a visible
    -- non-claim. See trust/defects.md
    -- ZISK-DEFECT-CLEAN-COMPLETENESS-TRIVIAL-AXIOMS.
    ProverAssumptions := fun _ _ _ => False
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
    completeness := fun _ _ _ _ _ _ h => h.elim }

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
