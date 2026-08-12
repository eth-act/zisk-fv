import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.MemAlignRomTable
import ZiskFv.Channels.MemAlignRom

/-!
# `MemAlignRom` static provider slice

The bus-133 provider is backed by the exact 256-row `memAlignRomTable` model.
It owns membership; a later MemAlign consumer emits the matching negative
message and a finished channel transports membership through balance.

`FullEnsemble` adds this provider alongside the MemAlign h998 consumer and
then finishes bus 133. On its own, the provider would be unbalanced; it never
serves as a standalone membership premise.

## Trust note

No axioms. Soundness derives exact `memAlignRomTable.Spec` membership from the
static lookup. The identical completeness-side membership premise supplies a
constructible static-table index and is not a soundness assumption.
-/

namespace ZiskFv.AirsClean.MemAlignRomSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.MemAlignRomTable
open ZiskFv.Channels.MemAlignRom

@[circuit_norm]
def main (message : MemAlignRomMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic memAlignRomTable) message
  MemAlignRomChannel.push message


def circuit : GeneralFormalCircuit FGL MemAlignRomMessage unit  where
  name := "MemAlignRomSlice133"
  main := main
  channelsWithRequirements := [MemAlignRomChannel.toRaw]
  exposedChannels message _ :=
    expose MemAlignRomChannel [MemAlignRomChannel.pushed message]
  Assumptions := fun _ _ => True
  Spec := fun message _ _ => memAlignRomTable.Spec message
  ProverAssumptions := fun message _ _ => memAlignRomTable.Spec message
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [MemAlignRomChannel]
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

def component : Component FGL := { circuit }

theorem component_interactionsWith_memAlignRomChannel :
    component.operations.interactionsWith MemAlignRomChannel.toRaw =
      [((MemAlignRomChannel.pushed component.rowInputVar).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemAlignRomChannel.toRaw,
      [((MemAlignRomChannel.pushed component.rowInputVar).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.MemAlignRomSlice
