import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Channels.MemAlignRanges

/-!
# MemAlign bus-107 byte-range provider slice

This provider is the exact static-table side of MemAlign's eight register
range checks (`mem_align.pil:113-118`, hints
#982/#984/#986/#988/#990/#992/#994/#996).  It models the upstream range
surface as `rangeTable8`: the 256 accepted byte values, not a stronger
semantic predicate or a caller promise.  The consumer's negative emissions
are matched by the finished bus-107 balance in `FullEnsemble`.
-/

namespace ZiskFv.AirsClean.MemAlignRangeSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.RangeTables
open ZiskFv.Channels.MemAlignRanges

/-- The provider's static lookup is the exact 8-bit range table. -/
@[circuit_norm]
def main (message : MemAlignRangeMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable8) message.value
  MemAlignRangeChannel.push message


/-- The bounded provider derives exact byte membership locally.  Its one
    completeness-side premise constructs the static-table witness; it is not
    a consumer or accepted-trace assumption. -/
def circuit : GeneralFormalCircuit FGL MemAlignRangeMessage unit  where
  name := "MemAlignRangeSlice107"
  main := main
  channelsWithRequirements := [MemAlignRangeChannel.toRaw]
  exposedChannels message _ :=
    expose MemAlignRangeChannel [MemAlignRangeChannel.pushed message]
  Assumptions := fun _ _ => True
  Spec := fun message _ _ => rangeTable8.Spec message.value
  ProverAssumptions := fun message _ _ => rangeTable8.Spec message.value
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable, rangeTable8,
        rangeStaticTable] using h_holds
    · intro _
      simp [MemAlignRangeChannel]
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable, rangeTable8,
      rangeStaticTable] using h_assumptions

/-- The bus-107 static provider component for the full ensemble. -/
def component : Component FGL := { circuit }

theorem component_interactionsWith_memAlignRangeChannel :
    component.operations.interactionsWith MemAlignRangeChannel.toRaw =
      [((MemAlignRangeChannel.pushed component.rowInputVar).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemAlignRangeChannel.toRaw,
      [((MemAlignRangeChannel.pushed component.rowInputVar).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.MemAlignRangeSlice
