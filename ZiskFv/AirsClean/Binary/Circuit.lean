import ZiskFv.AirsClean.Binary.Constraints
import ZiskFv.AirsClean.Binary.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Binary Clean Component (Phase C6)

Packages ZisK's Binary AIR as a Clean `Air.Flat.Component`.

The component covers the 7 F-typed constraints and the operation-bus push.
BinaryTable lookup semantics still flow through the existing table-soundness
boundary until the Binary-family terminal phase.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel)

def circuit : GeneralFormalCircuit FGL BinaryRow unit :=
  { binaryElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h_holds
        exact ⟨ by simpa [sub_eq_add_neg] using h0
              , by simpa [sub_eq_add_neg] using h1
              , by simpa [sub_eq_add_neg] using h2
              , by simpa [sub_eq_add_neg] using h3
              , by simpa [sub_eq_add_neg] using h4
              , by simpa [sub_eq_add_neg] using h5
              , by simpa [sub_eq_add_neg] using h6 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      simpa [sub_eq_add_neg] using h_assumptions }

def component : Air.Flat.Component FGL := ⟨ circuit ⟩

theorem spec_via_component (row : BinaryRow FGL)
    (h0 : row.mode.mode32 * (1 + -row.mode.mode32) = 0)
    (h1 : row.chain.carry_7 * (1 + -row.chain.carry_7) = 0)
    (h2 : row.mode.result_is_a * (1 + -row.mode.result_is_a) = 0)
    (h3 : row.mode.use_first_byte * (1 + -row.mode.use_first_byte) = 0)
    (h4 : row.mode.c_is_signed * (1 + -row.mode.c_is_signed) = 0)
    (h5 :
      row.chain.b_op_or_sext
        + -(row.mode.mode32 * (row.mode.c_is_signed + 512 + -row.chain.b_op)
            + row.chain.b_op) = 0)
    (h6 : row.mode.mode32_and_c_is_signed
        + -(row.mode.mode32 * row.mode.c_is_signed) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, binaryElaborated,
    circuit_norm] at hsound
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { aBytes := {
        free_in_a_0 := .const row.aBytes.free_in_a_0
        free_in_a_1 := .const row.aBytes.free_in_a_1
        free_in_a_2 := .const row.aBytes.free_in_a_2
        free_in_a_3 := .const row.aBytes.free_in_a_3
        free_in_a_4 := .const row.aBytes.free_in_a_4
        free_in_a_5 := .const row.aBytes.free_in_a_5
        free_in_a_6 := .const row.aBytes.free_in_a_6
        free_in_a_7 := .const row.aBytes.free_in_a_7 }
      bBytes := {
        free_in_b_0 := .const row.bBytes.free_in_b_0
        free_in_b_1 := .const row.bBytes.free_in_b_1
        free_in_b_2 := .const row.bBytes.free_in_b_2
        free_in_b_3 := .const row.bBytes.free_in_b_3
        free_in_b_4 := .const row.bBytes.free_in_b_4
        free_in_b_5 := .const row.bBytes.free_in_b_5
        free_in_b_6 := .const row.bBytes.free_in_b_6
        free_in_b_7 := .const row.bBytes.free_in_b_7 }
      cBytes := {
        free_in_c_0 := .const row.cBytes.free_in_c_0
        free_in_c_1 := .const row.cBytes.free_in_c_1
        free_in_c_2 := .const row.cBytes.free_in_c_2
        free_in_c_3 := .const row.cBytes.free_in_c_3
        free_in_c_4 := .const row.cBytes.free_in_c_4
        free_in_c_5 := .const row.cBytes.free_in_c_5
        free_in_c_6 := .const row.cBytes.free_in_c_6
        free_in_c_7 := .const row.cBytes.free_in_c_7 }
      chain := {
        carry_0 := .const row.chain.carry_0
        carry_1 := .const row.chain.carry_1
        carry_2 := .const row.chain.carry_2
        carry_3 := .const row.chain.carry_3
        carry_4 := .const row.chain.carry_4
        carry_5 := .const row.chain.carry_5
        carry_6 := .const row.chain.carry_6
        carry_7 := .const row.chain.carry_7
        b_op := .const row.chain.b_op
        b_op_or_sext := .const row.chain.b_op_or_sext }
      mode := {
        mode32 := .const row.mode.mode32
        result_is_a := .const row.mode.result_is_a
        use_first_byte := .const row.mode.use_first_byte
        c_is_signed := .const row.mode.c_is_signed
        mode32_and_c_is_signed := .const row.mode.mode32_and_c_is_signed } }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end ZiskFv.AirsClean.Binary
