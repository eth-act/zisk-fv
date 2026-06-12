import ZiskFv.AirsClean.Binary.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.Binary

private def binaryAndBaseIndex : BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14, by native_decide⟩

private def binaryAndFinalIndex : BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + ZiskFv.AirsClean.BinaryTable.p2_16,
    by native_decide⟩

private def binaryWitnessRow : BinaryRow FGL :=
  binaryStaticRowOf false false false false false
    binaryAndBaseIndex binaryAndBaseIndex binaryAndBaseIndex binaryAndBaseIndex
    binaryAndBaseIndex binaryAndBaseIndex binaryAndBaseIndex binaryAndFinalIndex

private theorem binaryWitnessCircuitProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions binaryWitnessRow data hint := by
  unfold binaryWitnessRow binaryStaticRowOf
  exact ⟨false, false, false, false, false, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

private theorem binaryWitnessStaticProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    staticLookupCircuit.ProverAssumptions binaryWitnessRow data hint := by
  unfold binaryWitnessRow
  refine ⟨false, false, false, false, false,
    binaryAndBaseIndex, binaryAndBaseIndex, binaryAndBaseIndex, binaryAndBaseIndex,
    binaryAndBaseIndex, binaryAndBaseIndex, binaryAndBaseIndex, binaryAndFinalIndex, ?_⟩
  repeat' constructor

theorem completeness_witness_binary :
    ∃ row : BinaryRow FGL,
      (∀ data hint, circuit.ProverAssumptions row data hint)
        ∧ (∀ data hint, staticLookupCircuit.ProverAssumptions row data hint) := by
  exact ⟨binaryWitnessRow, binaryWitnessCircuitProverAssumptions,
    binaryWitnessStaticProverAssumptions⟩

#print axioms completeness_witness_binary

end ZiskFv.TrustConsistency
