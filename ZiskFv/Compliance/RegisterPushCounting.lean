import ZiskFv.Compliance.MainTableUniqueness

/-!
# Counting pushes against pulls on the memory bus — #330 Phase 4 S3 groundwork

`main_table_unique` and `readMessage_inj` settle *which* walk step a `mem_op = 3` read message names.
The register telescope's coverage argument needs one step more: that a register-pre **push** is
answered by exactly one pull, so two distinct active slots cannot share a register-pre message.

That is a counting statement, and the existing balance lemma does not reach it.
`no_balanced_message_with_constant_nonzero_mult` assumes every interaction at a message carries the
*same* multiplicity, which is exactly what fails here — the pushes ride at `+1` and the pulls at
`-1`. This module supplies the two-sided count instead.

## Positions, not values

`Interaction` is `⟨channel, mult, msg, _, _⟩`. Two Main rows pushing the same register-pre message
therefore produce **equal interaction values at different list positions**, so nothing about the
values distinguishes them. `balanceOf` sums over `List.filter`, and `List.countP` counts positions,
so the counting has to stay at the position level throughout; a set-valued reading of "the pushes at
this message" would silently collapse the very case the argument is about.
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean
open ZiskFv.Compliance.Instantiation (RegSlot)

/-- On a memory-bus message every Main interaction rides at `0`, `+1` or `-1`, so the balance splits
    into a push count minus a pull count. Both counts are positions in the interaction list. -/
theorem sum_mult_eq_pushCount_sub_pullCount {l : List (Interaction FGL)}
    (h : ∀ i ∈ l, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1) :
    (l.map (·.mult)).sum
      = ((l.countP (fun i => decide (i.mult = 1)) : ℕ) : FGL)
        - ((l.countP (fun i => decide (i.mult = -1)) : ℕ) : FGL) := by
  have h_zero_one : ((0 : FGL) = 1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_zero_neg : ((0 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_one_neg : ((1 : FGL) = -1) = False := by simp only [eq_iff_iff, iff_false]; decide
  have h_neg_one : (((-1 : FGL)) = 1) = False := by simp only [eq_iff_iff, iff_false]; decide
  induction l with
  | nil => simp
  | cons a t ih =>
      have h_t : ∀ i ∈ t, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1 :=
        fun i hi => h i (List.mem_cons_of_mem _ hi)
      have h_a := h a List.mem_cons_self
      rcases h_a with h_a | h_a | h_a <;>
        simp [List.countP_cons, h_a, h_zero_one, h_zero_neg, h_one_neg, h_neg_one, ih h_t] <;>
        ring

/-! ## Two rows contribute two positions

`witness.interactionsWith` is a `flatMap` over tables, and each table's is a `flatMap` over its rows,
so an emission by row `i` and an emission by row `j ≠ i` land in *different* summands. These two
lemmas are the position-level bookkeeping that turns "two rows emit this message" into
"the count is at least two" — the step a value-level reading of the interaction list cannot make. -/

private theorem one_le_countP_flatMap {α β : Type _} (P : β → Bool) (f : α → List β)
    {l : List α} {x : α} (hx : x ∈ l) (h : 0 < (f x).countP P) :
    1 ≤ (l.flatMap f).countP P := by
  obtain ⟨b, hb, hPb⟩ := List.countP_pos_iff.mp h
  exact List.countP_pos_iff.mpr ⟨b, List.mem_flatMap.mpr ⟨x, hx, hb⟩, hPb⟩

private theorem two_le_countP_flatMap {α β : Type _} (P : β → Bool) (f : α → List β) :
    ∀ (l : List α) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≠ j →
      0 < (f l[i]).countP P → 0 < (f l[j]).countP P → 2 ≤ (l.flatMap f).countP P := by
  intro l
  induction l with
  | nil => intro i j hi; simp at hi
  | cons a t ih =>
      intro i j hi hj h_ne h_i h_j
      rw [List.flatMap_cons, List.countP_append]
      match i, j with
      | 0, 0 => exact absurd rfl h_ne
      | 0, (k + 1) =>
          have h_k : k < t.length := by simpa using hj
          have h_tail := one_le_countP_flatMap P f (List.getElem_mem h_k) (by simpa using h_j)
          have h_head : 1 ≤ (f a).countP P := by simpa using h_i
          omega
      | (k + 1), 0 =>
          have h_k : k < t.length := by simpa using hi
          have h_tail := one_le_countP_flatMap P f (List.getElem_mem h_k) (by simpa using h_i)
          have h_head : 1 ≤ (f a).countP P := by simpa using h_j
          omega
      | (k + 1), (m + 1) =>
          have := ih k m (by simpa using hi) (by simpa using hj) (by omega)
            (by simpa using h_i) (by simpa using h_j)
          omega

private theorem two_le_countP_of_two_indices {β : Type _} (P : β → Bool) :
    ∀ (l : List β) (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≠ j →
      P l[i] = true → P l[j] = true → 2 ≤ l.countP P := by
  intro l
  induction l with
  | nil => intro i j hi; simp at hi
  | cons a t ih =>
      intro i j hi hj h_ne h_i h_j
      rw [List.countP_cons]
      match i, j with
      | 0, 0 => exact absurd rfl h_ne
      | 0, (k + 1) =>
          have h_k : k < t.length := by simpa using hj
          have h_tail : 1 ≤ t.countP P :=
            List.countP_pos_iff.mpr ⟨t[k], List.getElem_mem h_k, by simpa using h_j⟩
          have h_head : P a = true := by simpa using h_i
          simp only [h_head, cond_true, if_true]
          omega
      | (k + 1), 0 =>
          have h_k : k < t.length := by simpa using hi
          have h_tail : 1 ≤ t.countP P :=
            List.countP_pos_iff.mpr ⟨t[k], List.getElem_mem h_k, by simpa using h_i⟩
          have h_head : P a = true := by simpa using h_j
          simp only [h_head, cond_true, if_true]
          omega
      | (k + 1), (m + 1) =>
          have := ih k m (by simpa using hi) (by simpa using hj) (by omega)
            (by simpa using h_i) (by simpa using h_j)
          omega

/-- **Two slots of one row contribute two positions.** Main's memory-bus emission list is six
    entries — the a/b/c register-pre pushes at positions `0`, `2`, `4` and the a/b/c current pulls
    at `1`, `3`, `5` (`Main/Circuit.lean:1025`). Distinct slots therefore push at distinct
    positions, which is the half of the push count `two_le_countP_flatMap` cannot reach: it
    separates rows, not slots within a row. -/
theorem two_le_row_memBus_pushCount {length : ℕ} {program : Program length}
    (env : Environment FGL) {msg : Array FGL} {s t : RegSlot} (h_ne : s ≠ t)
    (h_s : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval env).mult = 1)
    (h_s_msg : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval env).msg = msg)
    (h_t : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (t.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (t.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval env).mult = 1)
    (h_t_msg : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (t.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (t.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval env).msg
      = msg) :
    2 ≤ (((Main.componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw env)).countP
      (fun i => decide (i.mult = 1) && decide (i.msg = msg)) := by
  rw [Operations.interactionValuesWith_eq_map,
    Main.componentWithRomMemAndOpBus_interactionsWith_memBus]
  simp only [RegSlot.selectorExpr, RegSlot.regPreMessageExpr] at h_s h_s_msg h_t h_t_msg
  simp only [List.map_cons, List.map_nil]
  cases s <;> cases t
  · exact absurd rfl h_ne
  · exact two_le_countP_of_two_indices _ _ 0 2 (by simp) (by simp) (by omega)
      (by simp [h_s, h_s_msg]) (by simp [h_t, h_t_msg])
  · exact two_le_countP_of_two_indices _ _ 0 4 (by simp) (by simp) (by omega)
      (by simp [h_s, h_s_msg]) (by simp [h_t, h_t_msg])
  · exact two_le_countP_of_two_indices _ _ 2 0 (by simp) (by simp) (by omega)
      (by simp [h_s, h_s_msg]) (by simp [h_t, h_t_msg])
  · exact absurd rfl h_ne
  · exact two_le_countP_of_two_indices _ _ 2 4 (by simp) (by simp) (by omega)
      (by simp [h_s, h_s_msg]) (by simp [h_t, h_t_msg])
  · exact two_le_countP_of_two_indices _ _ 4 0 (by simp) (by simp) (by omega)
      (by simp [h_s, h_s_msg]) (by simp [h_t, h_t_msg])
  · exact two_le_countP_of_two_indices _ _ 4 2 (by simp) (by simp) (by omega)
      (by simp [h_s, h_s_msg]) (by simp [h_t, h_t_msg])
  · exact absurd rfl h_ne

/-- Casting is injective below the modulus, which is how a field-level count equality becomes a
    `ℕ` one. -/
private lemma nat_eq_of_cast_eq {a b : ℕ} (ha : a < GL_prime) (hb : b < GL_prime)
    (h : ((a : ℕ) : FGL) = ((b : ℕ) : FGL)) : a = b := by
  have h_val := congrArg Fin.val h
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h_val

/-- **As many pushes as pulls, at every memory-bus message whose interactions ride at `0`, `±1`.**

    This is the two-sided count `no_balanced_message_with_constant_nonzero_mult` cannot express: it
    assumes one constant multiplicity, and here the pushes and the pulls carry opposite ones. The
    counts are `List.countP`, so they count *positions* — two Main rows emitting the same message
    contribute two, which is exactly the case the register-telescope argument turns on. -/
theorem pushCount_eq_pullCount_of_balanced
    {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    (h_balanced : witness.BalancedChannels) (msg : Array FGL)
    (h_tri : ∀ i ∈ witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw,
      i.msg = msg → i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1) :
    (witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => decide (i.mult = 1) && decide (i.msg = msg))
      = (witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => decide (i.mult = -1) && decide (i.msg = msg)) := by
  have h_bal := memBus_balanced_of_witness witness h_balanced
  have h_zero := h_bal.2 msg
  rw [balanceOf, sum_mult_eq_pushCount_sub_pullCount
    (fun i hi => h_tri i (List.mem_of_mem_filter hi) (by simpa using List.of_mem_filter hi))] at h_zero
  rw [List.countP_filter, List.countP_filter] at h_zero
  have h_cast : (((witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => decide (i.mult = 1) && decide (i.msg = msg)) : ℕ) : FGL)
      = (((witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => decide (i.mult = -1) && decide (i.msg = msg)) : ℕ) : FGL) :=
    sub_eq_zero.mp h_zero
  have h_bound : ∀ p : Interaction FGL → Bool,
      (witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => p i && decide (i.msg = msg)) < GL_prime := by
    intro p
    rcases count_lt_ringChar_of_balancedInteractions (msg := msg) h_bal with h | h
    · rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime] at h
      refine lt_of_le_of_lt (List.countP_mono_left ?_) h
      intro a _ h_a
      simpa using (Bool.and_eq_true _ _ |>.mp h_a).2
    · exact absurd (h.symm.trans (ringChar.eq FGL GL_prime)) (by decide)
  exact nat_eq_of_cast_eq (h_bound _) (h_bound _) h_cast

end ZiskFv.Compliance
