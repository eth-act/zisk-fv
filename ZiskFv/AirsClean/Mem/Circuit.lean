import ZiskFv.AirsClean.Mem.Constraints
import ZiskFv.AirsClean.Mem.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Mem Clean Component (Phase C8)

Packages ZisK's Mem AIR per-row F-constraints as a Clean
`Air.Flat.Component`.

This is the per-row component layer only. The memory-bus provider path is a
family-terminal C10 concern because it must compose Mem, MemAlign*, and Main
against the same memory-bus channel without reintroducing a hidden
lookup/permutation promise.

## Trust note

No axioms. The mandatory Clean completeness side is conditional on the same
row `Spec`, so this component does not claim honest-prover constructibility
beyond the already-stated per-row relation.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- Mem as a Clean `GeneralFormalCircuit`. -/
def circuit : GeneralFormalCircuit FGL MemRow unit :=
  { memElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
      exact ⟨ by simpa only [sub_eq_add_neg] using h0
            , by simpa only [sub_eq_add_neg] using h1
            , by simpa only [sub_eq_add_neg] using h2
            , by simpa only [sub_eq_add_neg] using h3
            , by simpa only [sub_eq_add_neg] using h4
            , by simpa only [sub_eq_add_neg] using h5
            , by simpa only [sub_eq_add_neg] using h6
            , by simpa only [sub_eq_add_neg] using h7
            , by simpa only [sub_eq_add_neg] using h8 ⟩
    completeness := by
      circuit_proof_start
      simpa only [Spec, sub_eq_add_neg] using h_assumptions }

/-- Mem as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-! ## T4.1 — Mem-with-MemBus Component

`circuitWithMemBus` wraps `memWithMemBusElaborated` (Mem's per-row
constraints + the memory-bus provider emission) as a Clean
`GeneralFormalCircuit`. The Spec is unchanged from `Mem.circuit` —
the channel emission adds no per-row soundness obligation; the
soundness/completeness proofs use exactly the same body. -/

def circuitWithMemBus : GeneralFormalCircuit FGL MemRow unit :=
  { memWithMemBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
        exact ⟨ by simpa only [sub_eq_add_neg] using h0
              , by simpa only [sub_eq_add_neg] using h1
              , by simpa only [sub_eq_add_neg] using h2
              , by simpa only [sub_eq_add_neg] using h3
              , by simpa only [sub_eq_add_neg] using h4
              , by simpa only [sub_eq_add_neg] using h5
              , by simpa only [sub_eq_add_neg] using h6
              , by simpa only [sub_eq_add_neg] using h7
              , by simpa only [sub_eq_add_neg] using h8 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [MemBusChannel]
      simpa only [Spec, sub_eq_add_neg] using h_assumptions }

/-- Mem as a Clean `Air.Flat.Component` exposing the memory-bus
    provider emission. Used by the T4.1 memory-family ensemble. -/
def componentWithMemBus : Air.Flat.Component FGL := ⟨ circuitWithMemBus ⟩

/-- The Mem `Spec` for a row, derived through the Clean Component. -/
theorem spec_via_component (row : MemRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, memElaborated,
    circuit_norm] at hsound
  refine hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { addr := .const row.addr
      step := .const row.step
      sel := .const row.sel
      addr_changes := .const row.addr_changes
      step_dual := .const row.step_dual
      sel_dual := .const row.sel_dual
      value_0 := .const row.value_0
      value_1 := .const row.value_1
      wr := .const row.wr
      previous_step := .const row.previous_step
      increment_0 := .const row.increment_0
      increment_1 := .const row.increment_1
      read_same_addr := .const row.read_same_addr }
    row ?_ ?_
  · rfl
  · simpa only [Spec, sub_eq_add_neg] using h_constraints

end ZiskFv.AirsClean.Mem
