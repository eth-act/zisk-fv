import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.AirsClean.FullEnsemble.Balance.MemAlignRangeProviderMatch

/-!
# Accepted-trace MemAlign byte-range membership

MemAlign's eight bus-107 Range Check consumers are source-linked in its live
component. The static `rangeTable8` provider and finished-channel balance
derive membership; no consumer or caller provides it.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel MemAlignRangeMessage)

/-- Any exact MemAlign bus-107 consumer interaction in an accepted trace has
    a byte-range fact derived from verifier constraints and channel balance.
    The component's interaction theorem fixes these consumers to hints
    #982/#984/#986/#988/#990/#992/#994/#996 at `mem_align.pil:113-118`. -/
theorem AcceptedZiskTrace.memAlignRangeMembership
    {n : Nat} (trace : AcceptedZiskTrace n)
    {table : Table FGL}
    (h_table : table ∈ trace.witness.allTables)
    {consumerMsg : MemAlignRangeMessage (Expression FGL)}
    {row : Array FGL}
    (h_interaction :
      ((MemAlignRangeChannel.emitted (-1) consumerMsg).toRaw).eval
          (table.environment row) ∈
        table.interactionsWith MemAlignRangeChannel.toRaw) :
    ZiskFv.AirsClean.RangeTables.rangeTable8.Spec
      (Eval.eval (table.environment row) consumerMsg).value := by
  exact rangeTable8_spec_of_memAlign_range_interaction trace.witness
    trace.constraints_hold trace.channels_balanced h_table h_interaction

end ZiskFv.Compliance
