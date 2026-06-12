import ZiskFv.AirsClean.ArithMul.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.ArithMul

private def arithMulWitnessFree : ArithMulFreeCols :=
  { sext := 0
    div_by_zero := 0
    div_overflow := 0
    main_div := 0
    main_mul := 0
    signed := 0
    range_ab := 0
    range_cd := 0
    op := 0
    bus_res1 := 0
    multiplicity := 0 }

private def arithMulWitnessRow : ArithMulRow FGL :=
  arithMulRowOf 6 7 arithMulWitnessFree

private theorem arithMulWitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions arithMulWitnessRow data hint := by
  refine ⟨6, 7, arithMulWitnessFree, by norm_num, by norm_num, ?_⟩
  rfl

theorem completeness_witness_arithmul :
    ∃ row : ArithMulRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  exact ⟨arithMulWitnessRow, arithMulWitnessProverAssumptions⟩

#print axioms completeness_witness_arithmul

end ZiskFv.TrustConsistency
