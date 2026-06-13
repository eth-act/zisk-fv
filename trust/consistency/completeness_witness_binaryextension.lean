import ZiskFv.AirsClean.BinaryExtension.StaticCircuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.BinaryExtension

private def binaryExtensionIndex0 : BinaryExtensionTableIndex :=
  ⟨0, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex1 : BinaryExtensionTableIndex :=
  ⟨256, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex2 : BinaryExtensionTableIndex :=
  ⟨512, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex3 : BinaryExtensionTableIndex :=
  ⟨768, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex4 : BinaryExtensionTableIndex :=
  ⟨1024, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex5 : BinaryExtensionTableIndex :=
  ⟨1280, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex6 : BinaryExtensionTableIndex :=
  ⟨1536, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionIndex7 : BinaryExtensionTableIndex :=
  ⟨1792, by
    simp [ZiskFv.AirsClean.BinaryExtensionTable.tableSize,
      ZiskFv.AirsClean.BinaryExtensionTable.shiftBlockSize,
      ZiskFv.AirsClean.BinaryExtensionTable.sextBlockSize]⟩

private def binaryExtensionWitnessRow : BinaryExtensionRow FGL :=
  binaryExtensionStaticRowOf
    binaryExtensionIndex0 binaryExtensionIndex1 binaryExtensionIndex2 binaryExtensionIndex3
    binaryExtensionIndex4 binaryExtensionIndex5 binaryExtensionIndex6 binaryExtensionIndex7
    0 0

private theorem binaryExtensionWitnessStaticProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    staticLookupCircuit.ProverAssumptions binaryExtensionWitnessRow data hint := by
  unfold binaryExtensionWitnessRow
  refine ⟨binaryExtensionIndex0, binaryExtensionIndex1, binaryExtensionIndex2,
    binaryExtensionIndex3, binaryExtensionIndex4, binaryExtensionIndex5,
    binaryExtensionIndex6, binaryExtensionIndex7, 0, 0, ?_⟩
  repeat' apply And.intro
  all_goals rfl

private theorem binaryExtensionWitnessShiftProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    shiftStaticLookupCircuit.ProverAssumptions binaryExtensionWitnessRow data hint := by
  unfold binaryExtensionWitnessRow
  refine ⟨binaryExtensionIndex0, binaryExtensionIndex1, binaryExtensionIndex2,
    binaryExtensionIndex3, binaryExtensionIndex4, binaryExtensionIndex5,
    binaryExtensionIndex6, binaryExtensionIndex7, 0, 0, ?_⟩
  repeat' apply And.intro
  all_goals first | rfl | simp

theorem completeness_witness_binaryextension :
    ∃ row : BinaryExtensionRow FGL,
      (∀ data hint, staticLookupCircuit.ProverAssumptions row data hint)
        ∧ (∀ data hint, shiftStaticLookupCircuit.ProverAssumptions row data hint) := by
  exact ⟨binaryExtensionWitnessRow, binaryExtensionWitnessStaticProverAssumptions,
    binaryExtensionWitnessShiftProverAssumptions⟩

#print axioms completeness_witness_binaryextension

end ZiskFv.TrustConsistency
