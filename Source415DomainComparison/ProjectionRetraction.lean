import Source415DomainComparison.ForwardCompletion
import Source415DomainComparison.ReverseFields

/-! Exact execution-table retraction, not a source-commitment isomorphism.
Forward completion creates the two missing source histograms; reverse
projection discards those tables. Every original physical Table, including its
component, raw rows, and shared data, is nevertheless recovered exactly.
Nothing here equates an arbitrary committed provider raw with a chosen count.
-/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat
open PackedVirtualTableSources
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

 theorem projected_completed_table {p : Nat} {program : Program p}
    (old : OldWitness p program) (raw : Witness FGL) (index : Fin 15) :
    oldTable (projectedWitness (completedWitness old raw)) index = oldTable old index := by
  apply Table.ext_iff.mpr
  refine ⟨?_, projected_completed_rawRows old raw index, ?_⟩
  · exact (oldTable_component (projectedWitness (completedWitness old raw)) index).trans
      (oldTable_component old index).symm
  · exact (oldTable_data (projectedWitness (completedWitness old raw)) index).trans
      (oldTable_data old index).symm

end ZiskFv.AirsClean.FullEnsemble.DomainComparison

namespace ZiskFv.Compliance.DomainComparison

open Goldilocks Air.Flat
open ZiskFv.AirsClean.FullEnsemble.DomainComparison
open ZiskFv.AirsClean.PackedVirtualTableSources

 theorem accepted_roundtrip_execution_table {n : Nat} (trace : Legacy45.AcceptedZiskTrace n)
    (base : Witness FGL) (index : Fin 15) :
    oldTable (currentAcceptedToLegacy (forwardAccepted trace base)).witness index =
      oldTable trace.witness index :=
  projected_completed_table trace.witness
    (forwardRaw trace.witness trace.constraints_hold trace.channels_balanced base) index

end ZiskFv.Compliance.DomainComparison
