import ZiskFv.Compliance.DivSpinWitness.MemBusPermutation

open Goldilocks
open Air.Flat
open ZiskFv.Compliance.Instantiation
open ZiskFv.Compliance.RegisterMemBusBalance

namespace ZiskFv.Compliance.DivSpinWitness

private theorem perm_filter_ne_zero_append_filter_eq_zero
    (interactions : List (Interaction FGL)) :
    List.Perm interactions
      (interactions.filter (·.mult ≠ 0) ++ interactions.filter (·.mult = 0)) := by
  induction interactions with
  | nil => simp
  | cons interaction rest ih =>
      by_cases h_zero : interaction.mult = 0
      · have h_swap : List.Perm
            ([interaction] ++ rest.filter (·.mult ≠ 0))
            (rest.filter (·.mult ≠ 0) ++ [interaction]) :=
          List.perm_append_comm
        have h_reorder := List.Perm.append h_swap
          (List.Perm.refl (rest.filter (·.mult = 0)))
        exact (List.Perm.cons interaction ih).trans <| by
          simpa [h_zero, List.append_assoc] using h_reorder
      · simpa [h_zero] using List.Perm.cons interaction ih

theorem divSpinWitness_memBus_balanced :
    BalancedInteractions divSpinMemBusInteractions := by
  have h_perm :
      List.Perm divSpinMemBusInteractions
        (divSpinMemBusCore ++ divSpinMemBusZeroResidual) := by
    exact (perm_filter_ne_zero_append_filter_eq_zero divSpinMemBusInteractions).trans <|
      List.Perm.append
        (by
          rw [divSpinMemBusNonzero_filter]
          exact divSpinMemBusNonzeroChronological_perm_core)
        List.Perm.rfl
  have h_len :
      (divSpinMemBusCore ++ divSpinMemBusZeroResidual).length < ringChar FGL ∨
        ringChar FGL = 0 := by
    left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    rw [← h_perm.length_eq]
    have h_length : divSpinMemBusInteractions.length = 92 := by
      rw [divSpinWitness_memBusInteractions]
      norm_num [divSpinBoundaryRows, divSpinMainRows,
        registerBoundaryMemBusInteractions,
        ZiskFv.Compliance.AddSpinWitness.mainValueMemBusInteractions,
        Function.comp_def]
    omega
  apply balancedInteractions_of_perm
    (balancedInteractions_append_of_balanced
      divSpinMemBusCore_balanced divSpinMemBusZeroResidual_balanced h_len)
  exact h_perm.symm

end ZiskFv.Compliance.DivSpinWitness
