import ZiskFv.Compliance.DivSpinWitness.OpBusAddiX2

open Goldilocks
open Air.Flat
open ZiskFv.AirsClean.Main
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinJalOpBus_balanced :
    BalancedInteractions
      [mainOpBusInteraction (divSpinJalRow 3),
        mainOpBusInteraction (divSpinJalRow 4)] := by
  refine zeroInteractions_balanced _ ?_ ?_
  · intro interaction h_interaction
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_interaction
    rcases h_interaction with rfl | rfl <;> decide
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide

end ZiskFv.Compliance.DivSpinWitness
