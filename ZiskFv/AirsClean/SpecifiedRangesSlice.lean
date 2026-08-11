import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Channels.SpecifiedRanges

/-!
# `SpecifiedRanges` bus-103 static provider slice

This is the source-linked, bounded provider required for Mem's bus-103
distance range hints. It is intentionally a slice, not a claim to extract the
whole virtual `SpecifiedRanges` AIR: its membership predicate is the exact
constructive `rangeTable16` model and its range id is the manifest's bus 103.
-/

namespace ZiskFv.AirsClean.SpecifiedRangesSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.RangeTables
open ZiskFv.Channels.SpecifiedRanges

/-- The provider's static lookup is the exact 16-bit range table. -/
@[circuit_norm]
def main (value : Expression FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable16) value
  SpecifiedRangesSliceChannel.push (memDistanceMessage value)


/-- The bounded provider derives its own static membership; it carries no
caller-supplied assumption. -/
def circuit : GeneralFormalCircuit FGL field unit  where
  name := "SpecifiedRangesSlice103"
  main := main
  channelsWithRequirements := [SpecifiedRangesSliceChannel.toRaw]
  exposedChannels value _ :=
    expose SpecifiedRangesSliceChannel
      [SpecifiedRangesSliceChannel.pushed (memDistanceMessage value)]
  Assumptions := fun _ _ => True
  Spec := fun value _ _ => rangeTable16.Spec value
  ProverAssumptions := fun value _ _ => rangeTable16.Spec value
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable, rangeTable16,
        rangeStaticTable] using h_holds
    · intro _
      simpa [SpecifiedRangesSliceChannel, memDistanceMessage,
        memDistanceRangeId] using h_holds
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable, rangeTable16,
      rangeStaticTable] using h_assumptions

/-- The bus-103 provider component for the full ensemble. -/
def component : Component FGL := { circuit }

theorem component_interactionsWith_rangeChannel :
    component.operations.interactionsWith SpecifiedRangesSliceChannel.toRaw =
      [((SpecifiedRangesSliceChannel.pushed
        (memDistanceMessage component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨SpecifiedRangesSliceChannel.toRaw,
      [((SpecifiedRangesSliceChannel.pushed
        (memDistanceMessage component.rowInputVar)).toRaw)]⟩ ∈ component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.SpecifiedRangesSlice
