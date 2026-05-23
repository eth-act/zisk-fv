import ZiskFv.AirsClean.Binary.Circuit
import Clean.Air.Vm

/-!
# Binary minimal ensemble (Phase C6)

Assembles Binary's Clean `Component` with a trivial operation-bus consumer.
The real Main consumer and BinaryTable lookup composition are terminal-phase
work.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open ZiskFv.Channels.OperationBus
open Air.Flat

def opBusConsumer : GeneralFormalCircuit FGL OpBusMessage unit where
  name := "BinaryOpBusConsumer"
  main msg := do OpBusChannel.pull msg
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [OpBusChannel.toRaw]
  channelsLawful := by simp only [circuit_norm, OpBusChannel]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [OpBusChannel]
  completeness := by circuit_proof_start [OpBusChannel]

def binaryEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable component
        (by simp [circuit_norm, component, circuit, binaryElaborated])
        (by simp [circuit_norm, component, circuit, binaryElaborated])
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
               component, circuit, opBusConsumer, binaryElaborated]))
        (by intro _ _; trivial)

end ZiskFv.AirsClean.Binary
