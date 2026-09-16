import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Channels.SpecifiedRanges

/-!
# `SpecifiedRanges` bus-330 Arith provider slice

This is the data side of Arith's extracted range interactions.  Its row is the
exact `(range id, value)` tuple and its static lookup is the constructive
`arithRangeTable`; the channel does not add a caller-supplied range premise.
-/

namespace ZiskFv.AirsClean.ArithRangeSlice

open Goldilocks Air.Flat Circuit
open ZiskFv.AirsClean.RangeTables
open ZiskFv.Channels.SpecifiedRanges

def arithRangeMessageTable : StaticTable FGL SpecifiedRangeMessage where
  name := "arith-range-message-table"
  length := arithRangeTable.length
  row i := arithRangeMessage (arithRangeTable.row i)[0] (arithRangeTable.row i)[1]
  index msg := arithRangeTable.index #v[msg.rangeId, msg.value]
  Spec msg := ∃ i, msg = arithRangeMessage
    (arithRangeTable.row i)[0] (arithRangeTable.row i)[1]
  contains_iff := by intro msg; rfl

@[circuit_norm]
def main (message : SpecifiedRangeMessage (Expression FGL)) : Circuit FGL Unit := do
  lookup (Table.fromStatic arithRangeMessageTable) message
  ArithRangeChannel.push message

def circuit : GeneralFormalCircuit FGL SpecifiedRangeMessage unit where
  name := "SpecifiedRangesSlice330"
  main := main
  channelsWithRequirements := [ArithRangeChannel.toRaw]
  exposedChannels message _ :=
    expose ArithRangeChannel [ArithRangeChannel.pushed message]
  Assumptions := fun _ _ => True
  Spec := fun message _ _ => arithRangeMessageTable.Spec message
  ProverAssumptions := fun message _ _ => arithRangeMessageTable.Spec message
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable] using h_holds
    · intro _
      simp [arithRangeMessageTable, arithRangeMessage] at h_holds
      rcases h_holds with ⟨i, rfl, rfl⟩
      intro _
      refine ⟨i, ?_⟩
      apply Vector.ext
      intro j hj
      interval_cases j <;> rfl
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable] using h_assumptions

def component : Component FGL := { circuit }

end ZiskFv.AirsClean.ArithRangeSlice
