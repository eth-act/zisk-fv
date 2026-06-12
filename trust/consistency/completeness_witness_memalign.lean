import ZiskFv.AirsClean.MemAlign.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.MemAlign

private def memAlignWitnessRow : MemAlignRow FGL :=
  memAlignRowOf .prove false false false
    true false false false false false false false
    1 2 3 4 5 6 7 8
    16 0 4 9 0 123

private theorem memAlignWitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions memAlignWitnessRow data hint := by
  refine ⟨.prove, false, false, false,
    true, false, false, false, false, false, false, false,
    1, 2, 3, 4, 5, 6, 7, 8,
    16, 0, 4, 9, 0, 123, ?_⟩
  rfl

theorem completeness_witness_memalign :
    ∃ row : MemAlignRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  exact ⟨memAlignWitnessRow, memAlignWitnessProverAssumptions⟩

#print axioms completeness_witness_memalign

end ZiskFv.TrustConsistency
