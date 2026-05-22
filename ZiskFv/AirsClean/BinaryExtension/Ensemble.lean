import ZiskFv.AirsClean.BinaryExtension.Circuit
import Clean.Air.Vm

/-!
# BinaryExtension minimal ensemble (Phase C5)

Assembles BinaryExtension's Clean `Component` into a minimal `Air.Flat`
ensemble with a trivial operation-bus consumer. The real Main consumer is
assembled at the Binary-family terminal phase.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open ZiskFv.Channels.OperationBus
open Air.Flat

/-- A deliberately trivial op-bus consumer. -/
def opBusConsumer : GeneralFormalCircuit FGL OpBusMessage unit where
  name := "BinaryExtensionOpBusConsumer"
  main msg := do OpBusChannel.pull msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [OpBusChannel.toRaw]
  channelsLawful := by simp only [circuit_norm, OpBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [OpBusChannel]
  completeness := by circuit_proof_start [OpBusChannel]

/-- Minimal BinaryExtension ensemble: provider component + trivial op-bus
    consumer, with the operation bus finished. -/
def binaryExtensionEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, binaryExtensionElaborated])
        (by simp [circuit_norm, component, circuit, binaryExtensionElaborated])
    |>.addFinishedChannel OpBusChannel.toRaw
    |>.addTable ⟨ opBusConsumer ⟩
        (by simp [circuit_norm, opBusConsumer])
        (by simp [circuit_norm, opBusConsumer])
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               component, circuit, opBusConsumer, binaryExtensionElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.BinaryExtension
