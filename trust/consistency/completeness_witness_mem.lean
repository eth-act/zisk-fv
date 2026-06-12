import ZiskFv.AirsClean.Mem.Circuit

namespace ZiskFv.TrustConsistency

open Goldilocks
open ZiskFv.AirsClean.Mem

private def memWitnessRow : MemRow FGL :=
  memRowOf true true true false 16 9 10 8 1 2 42 43

private theorem memWitnessCircuitProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuit.ProverAssumptions memWitnessRow data hint := by
  refine ⟨true, true, true, false, 16, 9, 10, 8, 1, 2, 42, 43,
    (by intro _; rfl), (by intro _; rfl), ?_⟩
  rfl

private theorem memWitnessWithMemBusProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuitWithMemBus.ProverAssumptions memWitnessRow data hint := by
  refine ⟨true, true, true, false, 16, 9, 10, 8, 1, 2, 42, 43,
    (by intro _; rfl), (by intro _; rfl), ?_⟩
  rfl

private theorem memWitnessWithDualMemBusProverAssumptions
    (data : ProverData FGL) (hint : ProverHint FGL) :
    circuitWithDualMemBus.ProverAssumptions memWitnessRow data hint := by
  refine ⟨true, true, true, false, 16, 9, 10, 8, 1, 2, 42, 43,
    (by intro _; rfl), (by intro _; rfl), ?_⟩
  rfl

theorem completeness_witness_mem :
    ∃ row : MemRow FGL,
      (∀ data hint, circuit.ProverAssumptions row data hint) ∧
      (∀ data hint, circuitWithMemBus.ProverAssumptions row data hint) ∧
      (∀ data hint, circuitWithDualMemBus.ProverAssumptions row data hint) := by
  exact ⟨memWitnessRow,
    memWitnessCircuitProverAssumptions,
    memWitnessWithMemBusProverAssumptions,
    memWitnessWithDualMemBusProverAssumptions⟩

#print axioms completeness_witness_mem

end ZiskFv.TrustConsistency
