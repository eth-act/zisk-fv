import ZiskFv.AirsClean.BinaryExtension.Constraints
import ZiskFv.AirsClean.BinaryExtension.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# BinaryExtension Clean Component (Phase C5)

Packages ZisK's BinaryExtension AIR as a Clean `Air.Flat.Component`.

BinaryExtension has no F-only `assertZero` constraints: its local semantic
content is table-lookup based, and its cross-AIR output is the operation-bus
push emitted by `main`. The Component `Spec` is therefore `True` for this C5
step; the load-bearing table facts still come through the existing
`bin_ext_table_consumer_wf` boundary until the Binary-family terminal phase.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- BinaryExtension as a Clean `GeneralFormalCircuit`. -/
def circuit : GeneralFormalCircuit FGL BinaryExtensionRow unit :=
  { binaryExtensionElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      intro _
      trivial
    completeness := by circuit_proof_start [OpBusChannel] }

/-- BinaryExtension as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-- The BinaryExtension `Spec` for a row, derived through the Clean
    Component. Since `Spec := True` at C5, this is mainly the load-bearing
    closure hook showing consumers can route through `circuit.soundness`.

    The proof still follows the normal F-3 idiom: normalize
    `circuit.soundness`, feed a constant-expression row, and discharge the
    generated obligations. That keeps this skeleton component aligned with
    the non-trivial AIRs instead of bypassing the component field. -/
theorem spec_via_component (row : BinaryExtensionRow FGL) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, binaryExtensionElaborated,
    circuit_norm] at hsound
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { aCols := {
        free_in_a_0 := .const row.aCols.free_in_a_0
        free_in_a_1 := .const row.aCols.free_in_a_1
        free_in_a_2 := .const row.aCols.free_in_a_2
        free_in_a_3 := .const row.aCols.free_in_a_3
        free_in_a_4 := .const row.aCols.free_in_a_4
        free_in_a_5 := .const row.aCols.free_in_a_5
        free_in_a_6 := .const row.aCols.free_in_a_6
        free_in_a_7 := .const row.aCols.free_in_a_7 }
      cColsLo := {
        free_in_c_0 := .const row.cColsLo.free_in_c_0
        free_in_c_1 := .const row.cColsLo.free_in_c_1
        free_in_c_2 := .const row.cColsLo.free_in_c_2
        free_in_c_3 := .const row.cColsLo.free_in_c_3
        free_in_c_4 := .const row.cColsLo.free_in_c_4
        free_in_c_5 := .const row.cColsLo.free_in_c_5
        free_in_c_6 := .const row.cColsLo.free_in_c_6
        free_in_c_7 := .const row.cColsLo.free_in_c_7 }
      cColsHi := {
        free_in_c_8 := .const row.cColsHi.free_in_c_8
        free_in_c_9 := .const row.cColsHi.free_in_c_9
        free_in_c_10 := .const row.cColsHi.free_in_c_10
        free_in_c_11 := .const row.cColsHi.free_in_c_11
        free_in_c_12 := .const row.cColsHi.free_in_c_12
        free_in_c_13 := .const row.cColsHi.free_in_c_13
        free_in_c_14 := .const row.cColsHi.free_in_c_14
        free_in_c_15 := .const row.cColsHi.free_in_c_15 }
      flags := {
        op := .const row.flags.op
        free_in_b := .const row.flags.free_in_b
        op_is_shift := .const row.flags.op_is_shift
        b_0 := .const row.flags.b_0
        b_1 := .const row.flags.b_1 } }
    row ?_).1
  · simp [circuit_norm]

end ZiskFv.AirsClean.BinaryExtension
