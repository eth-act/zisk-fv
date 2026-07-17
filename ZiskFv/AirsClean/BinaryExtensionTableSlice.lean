import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.BinaryExtensionTable
import ZiskFv.Channels.BinaryExtensionTable

/-!
# `BinaryExtensionTable` static provider slice

The BinaryExtensionTable channel provider is backed by the exact decoded-row
`binaryExtensionTable` model. It owns table membership; BinaryExtension
consumers only emit negative messages, and a finished channel transports this
fact.

## Trust note

No axioms. Soundness derives exact `binaryExtensionTable.Spec` membership from
the static lookup. The identical completeness-side membership premise supplies
a constructible static-table index and is not a soundness assumption.
-/

namespace ZiskFv.AirsClean.BinaryExtensionTableSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.BinaryExtensionTable
open ZiskFv.Channels.BinaryExtensionTable

@[circuit_norm]
def main (message : BinaryExtensionTableMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic binaryExtensionTable) message
  BinaryExtensionTableChannel.push message

@[reducible]
def elaborated : ElaboratedCircuit FGL BinaryExtensionTableMessage unit where
  name := "BinaryExtensionTableSlice124"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [BinaryExtensionTableChannel.toRaw]
  exposedChannels message _ :=
    expose BinaryExtensionTableChannel [BinaryExtensionTableChannel.pushed message]
  channelsLawful := by
    simp only [circuit_norm, main, BinaryExtensionTableChannel]

def circuit : GeneralFormalCircuit FGL BinaryExtensionTableMessage unit :=
  { elaborated with
    Assumptions := fun _ _ => True
    Spec := fun message _ _ => binaryExtensionTable.Spec message
    ProverAssumptions := fun message _ _ => binaryExtensionTable.Spec message
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
      · intro _
        simp [BinaryExtensionTableChannel]
    completeness := by
      circuit_proof_start [Lookup.completeness_def]
      simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions }

def component : Component FGL := { circuit }

theorem component_interactionsWith_binaryExtensionTableChannel :
    component.operations.interactionsWith BinaryExtensionTableChannel.toRaw =
      [((BinaryExtensionTableChannel.pushed component.rowInputVar).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryExtensionTableChannel.toRaw,
      [((BinaryExtensionTableChannel.pushed component.rowInputVar).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, elaborated, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.BinaryExtensionTableSlice
