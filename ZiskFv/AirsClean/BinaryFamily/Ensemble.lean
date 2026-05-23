import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryExtension.Circuit
import Clean.Air.Vm

/-!
# Binary-family op-bus ensemble (Phase C7)

Provider-side Binary-family ensemble for the shared operation bus. This
assembles the migrated BinaryAdd, Binary, and BinaryExtension components with
a generic op-bus consumer.

This is C7 groundwork only: `op_bus_permutation_sound` retires when the real
Main consumer is wired into the same balanced channel path, not from this
provider-side ensemble alone.
-/

namespace ZiskFv.AirsClean.BinaryFamily

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus

def opBusConsumer : GeneralFormalCircuit FGL OpBusMessage unit where
  name := "BinaryFamilyOpBusConsumer"
  main msg := do OpBusChannel.pull msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [OpBusChannel.toRaw]
  channelsLawful := by simp only [circuit_norm, OpBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [OpBusChannel]
  completeness := by circuit_proof_start [OpBusChannel]

def binaryFamilyOpBusEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable ZiskFv.AirsClean.BinaryAdd.component
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryAdd.component,
          ZiskFv.AirsClean.BinaryAdd.circuit,
          ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryAdd.component,
          ZiskFv.AirsClean.BinaryAdd.circuit,
          ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated])
    |>.addTable ZiskFv.AirsClean.Binary.component
        (by simp [circuit_norm, ZiskFv.AirsClean.Binary.component,
          ZiskFv.AirsClean.Binary.circuit,
          ZiskFv.AirsClean.Binary.binaryElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.Binary.component,
          ZiskFv.AirsClean.Binary.circuit,
          ZiskFv.AirsClean.Binary.binaryElaborated])
    |>.addTable ZiskFv.AirsClean.BinaryExtension.component
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryExtension.component,
          ZiskFv.AirsClean.BinaryExtension.circuit,
          ZiskFv.AirsClean.BinaryExtension.binaryExtensionElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryExtension.component,
          ZiskFv.AirsClean.BinaryExtension.circuit,
          ZiskFv.AirsClean.BinaryExtension.binaryExtensionElaborated])
    |>.addFinishedChannel OpBusChannel.toRaw
    |>.addTable ⟨ opBusConsumer ⟩
        (by simp [circuit_norm, opBusConsumer])
        (by simp [circuit_norm, opBusConsumer])
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          clear h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h | h | h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               ZiskFv.AirsClean.BinaryAdd.component,
               ZiskFv.AirsClean.BinaryAdd.circuit,
               ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated,
               ZiskFv.AirsClean.Binary.component,
               ZiskFv.AirsClean.Binary.circuit,
               ZiskFv.AirsClean.Binary.binaryElaborated,
               ZiskFv.AirsClean.BinaryExtension.component,
               ZiskFv.AirsClean.BinaryExtension.circuit,
               ZiskFv.AirsClean.BinaryExtension.binaryExtensionElaborated,
               opBusConsumer]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.BinaryFamily
