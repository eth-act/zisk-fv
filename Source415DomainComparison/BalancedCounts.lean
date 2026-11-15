import ZiskFv.Compliance.RegisterPushCounting

/-! Count positions, including zero interactions in the original length bound.
The no-overflow hypothesis below is exactly Clean's existing balance field,
not a new accepted-trace premise. The result is independent of the channel.
It is groundwork for cancelling Arith's primary push against its optional
remainder pull when bounding the old Binary-family row counts by Main. -/

namespace ZiskFv.AirsClean.FullEnsemble.DomainComparison

open Goldilocks Air.Flat

private theorem sum_balanceOf_support (interactions : List (Interaction FGL))
    (support : Finset (Array FGL))
    (covers : ∀ interaction ∈ interactions, interaction.msg ∈ support) :
    (∑ message ∈ support, balanceOf interactions message) =
      (interactions.map (·.mult)).sum := by
  induction interactions with
  | nil => simp [balanceOf]
  | cons interaction tail ih =>
      have hhead := covers interaction List.mem_cons_self
      have htail : ∀ item ∈ tail, item.msg ∈ support :=
        fun item hi => covers item (List.mem_cons_of_mem _ hi)
      have hstep (message : Array FGL) :
          balanceOf (interaction :: tail) message =
            (if interaction.msg = message then interaction.mult else 0) +
              balanceOf tail message := by
        by_cases h : interaction.msg = message <;> simp [balanceOf, h]
      simp_rw [hstep]
      rw [Finset.sum_add_distrib, ih htail]
      simp [hhead]

 theorem balanced_total_multiplicity {interactions : List (Interaction FGL)}
    (h : BalancedInteractions interactions) :
    (interactions.map (·.mult)).sum = 0 := by
  let support := (interactions.map (·.msg)).toFinset
  have covers : ∀ interaction ∈ interactions, interaction.msg ∈ support := by
    intro interaction hi
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨interaction, hi, rfl⟩)
  rw [← sum_balanceOf_support interactions support covers]
  simp only [h.2, Finset.sum_const_zero]

 theorem balanced_positional_counts {interactions : List (Interaction FGL)}
    (h : BalancedInteractions interactions)
    (tri : ∀ interaction ∈ interactions,
      interaction.mult = 0 ∨ interaction.mult = 1 ∨ interaction.mult = -1) :
    interactions.countP (fun interaction => decide (interaction.mult = 1)) =
      interactions.countP (fun interaction => decide (interaction.mult = -1)) := by
  have hzero := balanced_total_multiplicity h
  rw [ZiskFv.Compliance.sum_mult_eq_pushCount_sub_pullCount tri] at hzero
  have hcast := sub_eq_zero.mp hzero
  have hlength : interactions.length < GL_prime := by
    rcases h.1 with hlength | hchar
    · simpa only [ringChar.eq FGL GL_prime] using hlength
    · exact False.elim ((by decide : GL_prime ≠ 0)
        ((ringChar.eq FGL GL_prime).symm.trans hchar))
  have hpush : interactions.countP (fun interaction => decide (interaction.mult = 1)) <
      GL_prime := lt_of_le_of_lt List.countP_le_length hlength
  have hpull : interactions.countP (fun interaction => decide (interaction.mult = -1)) <
      GL_prime := lt_of_le_of_lt List.countP_le_length hlength
  have hvalue := congrArg Fin.val hcast
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt hpush,
    Nat.mod_eq_of_lt hpull] at hvalue

end ZiskFv.AirsClean.FullEnsemble.DomainComparison
