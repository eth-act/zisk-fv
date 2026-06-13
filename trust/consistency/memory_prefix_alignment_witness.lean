import ZiskFv.ZiskCircuit.MemTimeline.Construction

/-!
Non-empty satisfiability witness for the P4-bound prefix-alignment residual.

The LD global-theorem instantiation uses an empty prefix because the selected
read is the first accepted memory row in that tiny witness.  This file keeps the
alignment residual from being witnessed only by that degenerate prefix shape: a
concrete store row gives a non-empty prefix whose aligned state is exactly the
state obtained by replaying that one-row prefix.
-/

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.ZiskCircuit.MemTrace
open ZiskFv.ZiskCircuit.MemTimeline

private def initialState :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  default

private def storeRow : MemoryBusEntry FGL where
  multiplicity := 1
  as := 2
  ptr := 32
  value_0 := 1
  value_1 := 0
  timestamp := 1

theorem memory_prefix_alignment_single_store_witness :
    MemoryPrefixStateAlignment initialState
      (stateAfterMemoryBusRows initialState [storeRow])
      [storeRow] := by
  rfl

#print axioms memory_prefix_alignment_single_store_witness

end ZiskFv.TrustConsistency
