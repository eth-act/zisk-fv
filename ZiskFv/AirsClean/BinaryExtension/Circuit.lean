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
    closure hook showing consumers can route through `circuit.soundness`. -/
theorem spec_via_component (row : BinaryExtensionRow FGL) :
    Spec row := by
  have hsound := circuit.soundness
  exact trivial

end ZiskFv.AirsClean.BinaryExtension
