import ZiskFv.Compliance.DivSpinWitness.OpBusStaticInteractions

open Goldilocks
open Air.Flat

namespace ZiskFv.Compliance.DivSpinWitness

theorem divSpinOpBusPair_balanced
    (left right : Interaction FGL)
    (h_msg_eq : right.msg = left.msg)
    (h_mult : right.mult = -left.mult) :
    BalancedInteractions [left, right] := by
  refine Air.Flat.balancedInteractions_of_present ?_ [left.msg] ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    norm_num
  · intro interaction h_interaction
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h_interaction
    rcases h_interaction with rfl | rfl
    · simp
    · simp [h_msg_eq]
  · intro msg h_present
    simp only [List.mem_singleton] at h_present
    subst msg
    simp [balanceOf, h_msg_eq, h_mult]

end ZiskFv.Compliance.DivSpinWitness
