import ZiskFv.AirsClean.MemAlignReadByte.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.MemAlignReadByte

private def memAlignReadByteWitnessRow : MemAlignReadByteRow FGL :=
  memAlignReadByteRowOf false true false 42 1000 2 3 4 5

private theorem memAlignReadByteWitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions memAlignReadByteWitnessRow data hint := by
  refine ⟨false, true, false, 42, 1000, 2, 3, 4, 5, by norm_num, ?_⟩
  rfl

theorem completeness_witness_memalignreadbyte :
    ∃ row : MemAlignReadByteRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  exact ⟨memAlignReadByteWitnessRow, memAlignReadByteWitnessProverAssumptions⟩

#print axioms completeness_witness_memalignreadbyte

end ZiskFv.TrustConsistency
