import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.BinaryTable
import ZiskFv.Channels.BinaryTable

/-!
# `BinaryTable` static provider slice

The BinaryTable channel provider is backed by the exact decoded-row
`binaryTable` model. It owns table membership; Binary consumers only emit
negative messages, and a finished channel transports this fact.

## Trust note

No axioms. Soundness derives exact `binaryTable.Spec` membership from the
static lookup. The identical completeness-side membership premise supplies a
constructible static-table index and is not a soundness assumption.
-/

namespace ZiskFv.AirsClean.BinaryTableSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.BinaryTable
open ZiskFv.Channels.BinaryTable

@[circuit_norm]
def main (message : BinaryTableMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic binaryTable) message
  BinaryTableChannel.push message

@[reducible]
def elaborated : ElaboratedCircuit FGL BinaryTableMessage unit where
  name := "BinaryTableSlice125"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [BinaryTableChannel.toRaw]
  exposedChannels message _ :=
    expose BinaryTableChannel [BinaryTableChannel.pushed message]
  channelsLawful := by
    simp only [circuit_norm, main, BinaryTableChannel]

def circuit : GeneralFormalCircuit FGL BinaryTableMessage unit :=
  { elaborated with
    Assumptions := fun _ _ => True
    Spec := fun message _ _ => binaryTable.Spec message
    ProverAssumptions := fun message _ _ => binaryTable.Spec message
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
      · intro _
        simp [BinaryTableChannel]
    completeness := by
      circuit_proof_start [Lookup.completeness_def]
      simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions }

def component : Component FGL := { circuit }

theorem component_interactionsWith_binaryTableChannel :
    component.operations.interactionsWith BinaryTableChannel.toRaw =
      [((BinaryTableChannel.pushed component.rowInputVar).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨BinaryTableChannel.toRaw,
      [((BinaryTableChannel.pushed component.rowInputVar).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, elaborated, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.BinaryTableSlice
