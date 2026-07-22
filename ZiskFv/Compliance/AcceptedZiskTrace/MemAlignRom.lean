import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance.MemAlignRomProviderMatch

/-!
# Accepted-trace MemAlign ROM membership

The h998 tuple is source-linked through MemAlign's verifier-checked cyclic
successor relation.  Its exact virtual-ROM membership is then derived from
the static bus-133 provider and finished-channel balance.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble

/-- An accepted trace derives the exact MemAlign ROM membership of every
effective MemAlign row, with `DELTA_PC` read through the D3 cyclic successor
view. This consumes only accepted constraints, finished-channel balance, and
the verifier-checked cyclic certificate. -/
theorem AcceptedZiskTrace.memAlignRomMembership
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL}
    (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component = ZiskFv.AirsClean.MemAlign.component)
    (index : Fin table.length) :
    ZiskFv.AirsClean.MemAlignRomTable.memAlignRomTable.Spec
      (ZiskFv.AirsClean.MemAlign.memAlignRomSuccessorMessage
        (ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment (table.environmentAt index))
        (ZiskFv.AirsClean.MemAlign.rowInputOfEnvironment
          (table.successorEnvironment index))) := by
  exact memAlignRomTable_spec_of_memAlign_cyclic_index trace.witness
    trace.constraints_hold trace.channels_balanced h_table h_component
    (trace.cyclic_successor_transitions_hold table h_table) index

end ZiskFv.Compliance
