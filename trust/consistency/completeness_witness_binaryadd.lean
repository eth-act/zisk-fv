import ZiskFv.AirsClean.BinaryAdd.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.BinaryAdd

private def binaryAddWitnessRow : BinaryAddRow FGL :=
  binaryAddRowOf 40 2

private theorem binaryAddWitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions binaryAddWitnessRow data hint := by
  refine ⟨40, 2, by norm_num, by norm_num, ?_⟩
  rfl

theorem completeness_witness_binaryadd :
    ∃ row : BinaryAddRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  exact ⟨binaryAddWitnessRow, binaryAddWitnessProverAssumptions⟩

#print axioms completeness_witness_binaryadd

end ZiskFv.TrustConsistency
