import ZiskFv.AirsClean.Binary.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.Binary

private def binaryAndBaseIndex : BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14, by
    simp [ZiskFv.AirsClean.BinaryTable.block14,
      ZiskFv.AirsClean.BinaryTable.block13, ZiskFv.AirsClean.BinaryTable.block12,
      ZiskFv.AirsClean.BinaryTable.block11, ZiskFv.AirsClean.BinaryTable.block10,
      ZiskFv.AirsClean.BinaryTable.block9, ZiskFv.AirsClean.BinaryTable.block8,
      ZiskFv.AirsClean.BinaryTable.block7, ZiskFv.AirsClean.BinaryTable.block6,
      ZiskFv.AirsClean.BinaryTable.block5, ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3, ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1, ZiskFv.AirsClean.BinaryTable.block0,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize,
      ZiskFv.AirsClean.BinaryTable.fullBlockSize,
      ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.p2_17, ZiskFv.AirsClean.BinaryTable.p2_18,
      ZiskFv.AirsClean.BinaryTable.p2_19]⟩

private def binaryAndFinalIndex : BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block14 + ZiskFv.AirsClean.BinaryTable.p2_16,
    by
      simp [ZiskFv.AirsClean.BinaryTable.block14,
        ZiskFv.AirsClean.BinaryTable.block13, ZiskFv.AirsClean.BinaryTable.block12,
        ZiskFv.AirsClean.BinaryTable.block11, ZiskFv.AirsClean.BinaryTable.block10,
        ZiskFv.AirsClean.BinaryTable.block9, ZiskFv.AirsClean.BinaryTable.block8,
        ZiskFv.AirsClean.BinaryTable.block7, ZiskFv.AirsClean.BinaryTable.block6,
        ZiskFv.AirsClean.BinaryTable.block5, ZiskFv.AirsClean.BinaryTable.block4,
        ZiskFv.AirsClean.BinaryTable.block3, ZiskFv.AirsClean.BinaryTable.block2,
        ZiskFv.AirsClean.BinaryTable.block1, ZiskFv.AirsClean.BinaryTable.block0,
        ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
        ZiskFv.AirsClean.BinaryTable.absBlockSize,
        ZiskFv.AirsClean.BinaryTable.fullBlockSize,
        ZiskFv.AirsClean.BinaryTable.tableSize,
        ZiskFv.AirsClean.BinaryTable.p2_16, ZiskFv.AirsClean.BinaryTable.p2_17,
        ZiskFv.AirsClean.BinaryTable.p2_18, ZiskFv.AirsClean.BinaryTable.p2_19]⟩

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
