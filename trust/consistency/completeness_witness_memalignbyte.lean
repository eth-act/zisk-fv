import ZiskFv.AirsClean.MemAlignByte.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.MemAlignByte

private def memAlignByteWitnessRow : MemAlignByteRow FGL :=
  memAlignByteRowOf false true false true 42 99 1000 2 3 4 5

private theorem memAlignByteWitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions memAlignByteWitnessRow data hint := by
  refine ⟨false, true, false, true, 42, 99, 1000, 2, 3, 4, 5,
    by norm_num, by norm_num, ?_⟩
  rfl

theorem completeness_witness_memalignbyte :
    ∃ row : MemAlignByteRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  exact ⟨memAlignByteWitnessRow, memAlignByteWitnessProverAssumptions⟩

#print axioms completeness_witness_memalignbyte

end ZiskFv.TrustConsistency
