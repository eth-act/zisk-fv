import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.AirsClean.BinaryExtension.Circuit
import ZiskFv.AirsClean.Main.Circuit
import Clean.Air.Vm

/-!
# Binary-family op-bus ensemble (Phase C7)

Binary-family ensemble for the shared operation bus. This assembles the
migrated BinaryAdd, Binary, and BinaryExtension provider components with the
Main assume-side operation-bus component.

This is C7 groundwork only: `op_bus_permutation_sound` retires when the
balanced channel result is projected into the canonical `matches_entry`
bridges, not from this assembly theorem alone.
-/

namespace ZiskFv.AirsClean.BinaryFamily

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus

def binaryFamilyOpBusEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable ZiskFv.AirsClean.Main.component
        (by simp [circuit_norm, ZiskFv.AirsClean.Main.component,
          ZiskFv.AirsClean.Main.circuit,
          ZiskFv.AirsClean.Main.mainWithOpBusElaborated])
        (by simp [circuit_norm, ZiskFv.AirsClean.Main.component,
          ZiskFv.AirsClean.Main.circuit,
          ZiskFv.AirsClean.Main.mainWithOpBusElaborated])
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
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          clear h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h | h | h | h <;>
            (rw [h]
             simp [circuit_norm, Air.Flat.Component.Assumptions,
               ZiskFv.AirsClean.Main.component,
               ZiskFv.AirsClean.Main.circuit,
               ZiskFv.AirsClean.Main.mainWithOpBusElaborated,
               ZiskFv.AirsClean.BinaryAdd.component,
               ZiskFv.AirsClean.BinaryAdd.circuit,
               ZiskFv.AirsClean.BinaryAdd.binaryAddElaborated,
               ZiskFv.AirsClean.Binary.component,
               ZiskFv.AirsClean.Binary.circuit,
               ZiskFv.AirsClean.Binary.binaryElaborated,
               ZiskFv.AirsClean.BinaryExtension.component,
               ZiskFv.AirsClean.BinaryExtension.circuit,
               ZiskFv.AirsClean.BinaryExtension.binaryExtensionElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.BinaryFamily
