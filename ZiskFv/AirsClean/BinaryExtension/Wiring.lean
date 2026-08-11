import ZiskFv.AirsClean.BinaryExtension.Circuit
import ZiskFv.AirsClean.BinaryExtensionTableSlice
import Clean.Air.Vm

/-!
# BinaryExtension table wiring

The BinaryExtension consumer emits its eight table tuples negatively on bus
124. This local terminal ensemble joins that actual consumer to the exact
static provider slice and finishes the channel.

## Trust note

No axioms. The consumer has no membership guarantee or soundness-side
`ProverAssumptions`; exact membership is proved by `BinaryExtensionTableSlice`
and transported through the finished channel.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open Air.Flat
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableChannel)

/-- The terminal bus-124 connection for the real BinaryExtension consumer and
the exact static BinaryExtensionTable provider. -/
def binaryExtensionTableConnectionEnsemble : FormalEnsemble FGL unit :=
  SoundEnsemble.empty FGL unit
    |>.addTable tableConsumerComponent
        (by simp [circuit_norm, tableConsumerComponent, tableConsumerCircuit])
        (by
          intro channel h_finished
          change channel ∈ ([] : List (RawChannel FGL)) at h_finished
          simp at h_finished)
    |>.addTable ZiskFv.AirsClean.BinaryExtensionTableSlice.component
        (by simp [circuit_norm, ZiskFv.AirsClean.BinaryExtensionTableSlice.component,
          ZiskFv.AirsClean.BinaryExtensionTableSlice.circuit])
        (by
          intro channel h_finished
          change channel ∈ ([] : List (RawChannel FGL)) at h_finished
          simp at h_finished)
    |>.addFinishedChannel BinaryExtensionTableChannel.toRaw
    |>.toFormal (fun _ => True) (fun _ => True)
        (by
          intro _ _ table h_mem row _
          have h := EnsembleWitness.mem_allTables_component_of_mem_allTables h_mem
          clear h_mem
          simp only [circuit_norm, Ensemble.allTables] at h
          rcases h with h | h | h <;> (rw [h]; trivial))
        (by intro _ _; trivial)

theorem binaryExtensionTableConnectionEnsemble_finishes_bus124 :
    BinaryExtensionTableChannel.toRaw ∈
      binaryExtensionTableConnectionEnsemble.ensemble.channels := by
  simp [binaryExtensionTableConnectionEnsemble, SoundEnsemble.toFormal,
    SoundEnsemble.addFinishedChannel_channels, SoundEnsemble.addTable_channels]

end ZiskFv.AirsClean.BinaryExtension
