import ZiskFv.AirsClean.ArithDiv.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.ArithDiv

private def arithDivWitnessFree : ArithDivFreeCols :=
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

private def arithDivWitnessRow : ArithDivRow FGL :=
  arithDivRowOf 100 7 arithDivWitnessFree

private theorem arithDivWitnessProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions arithDivWitnessRow data hint := by
  refine ⟨100, 7, arithDivWitnessFree, by norm_num, by norm_num, by norm_num, ?_⟩
  rfl

theorem completeness_witness_arithdiv :
    ∃ row : ArithDivRow FGL, ∀ data hint, circuit.ProverAssumptions row data hint := by
  exact ⟨arithDivWitnessRow, arithDivWitnessProverAssumptions⟩

#print axioms completeness_witness_arithdiv

end ZiskFv.TrustConsistency
