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

private theorem countP_le_countP_flatMap {α β : Type _} (P : β → Bool) (f : α → List β)
    {l : List α} {x : α} (hx : x ∈ l) : (f x).countP P ≤ (l.flatMap f).countP P := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
      rw [List.flatMap_cons, List.countP_append]
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := ih hx'
        omega

private theorem one_le_countP_of_index {β : Type _} (P : β → Bool) (l : List β) (i : ℕ)
    (hi : i < l.length) (h : P l[i] = true) : 0 < l.countP P :=
  List.countP_pos_iff.mpr ⟨l[i], List.getElem_mem hi, h⟩

/-- One active slot pushes at one position of its row's emission list. -/
theorem one_le_row_memBus_pushCount {length : ℕ} {program : Program length}
    (env : Environment FGL) {msg : Array FGL} (s : RegSlot)
    (h_s : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval env).mult = 1)
    (h_s_msg : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval env).msg
      = msg) :
    0 < (((Main.componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw env)).countP
      (fun i => decide (i.mult = 1) && decide (i.msg = msg)) := by
  rw [Operations.interactionValuesWith_eq_map,
    Main.componentWithRomMemAndOpBus_interactionsWith_memBus]
  simp only [List.map_cons, List.map_nil]
  cases s
  · simp only [RegSlot.selectorExpr, RegSlot.regPreMessageExpr] at h_s h_s_msg
    exact one_le_countP_of_index _ _ 0 (by simp) (by simp [h_s, h_s_msg])
  · simp only [RegSlot.selectorExpr, RegSlot.regPreMessageExpr] at h_s h_s_msg
    exact one_le_countP_of_index _ _ 2 (by simp) (by simp [h_s, h_s_msg])
  · simp only [RegSlot.selectorExpr, RegSlot.regPreMessageExpr] at h_s h_s_msg
    exact one_le_countP_of_index _ _ 4 (by simp) (by simp [h_s, h_s_msg])

/-- **Two distinct active register slots of the witness push at two distinct positions.**

    The two halves meet here: different rows are separated by `two_le_countP_flatMap`, two slots of
    one row by `two_le_row_memBus_pushCount`, and `countP_le_countP_flatMap` lifts a single table's
    count to the whole witness. -/
theorem two_le_witness_pushCount {length : ℕ} {program : Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {table : Table FGL} (h_table : table ∈ witness.allTables)
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    {i j : ℕ} (hi : i < table.table.length) (hj : j < table.table.length)
    {s t : RegSlot} (h_ne : i ≠ j ∨ (i = j ∧ s ≠ t)) {msg : Array FGL}
    (h_s : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment table.table[i])).mult = 1)
    (h_s_msg : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment table.table[i])).msg = msg)
    (h_t : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (t.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (t.regPreMessageExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment table.table[j])).mult = 1)
    (h_t_msg : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (t.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (t.regPreMessageExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment table.table[j])).msg = msg) :
    2 ≤ (witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun k => decide (k.mult = 1) && decide (k.msg = msg)) := by
  have h_lift : (table.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun k => decide (k.mult = 1) && decide (k.msg = msg))
      ≤ (witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun k => decide (k.mult = 1) && decide (k.msg = msg)) := by
    rw [EnsembleWitness.interactionsWith]
    exact countP_le_countP_flatMap (fun k => decide (k.mult = 1) && decide (k.msg = msg))
      (fun x => x.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw) h_table
  have h_table_count : 2 ≤ (table.interactionsWith
      ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun k => decide (k.mult = 1) && decide (k.msg = msg)) := by
    rw [Table.interactionsWith, h_component]
    rcases h_ne with h_rows | ⟨h_ij, h_slots⟩
    · exact two_le_countP_flatMap _ _ table.table i j hi hj h_rows
        (one_le_row_memBus_pushCount _ s h_s h_s_msg)
        (one_le_row_memBus_pushCount _ t h_t h_t_msg)
    · subst h_ij
      refine le_trans ?_ (countP_le_countP_flatMap
        (fun k => decide (k.mult = 1) && decide (k.msg = msg))
        (fun row => (Main.componentWithRomMemAndOpBus length program).operations.interactionValuesWith
          ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw (table.environment row))
        (List.getElem_mem hi))
      exact two_le_row_memBus_pushCount _ h_slots h_s h_s_msg h_t h_t_msg
  omega

/-! ## The pull side: at most one position

The push side counts *up* — two witnesses give two positions. The pull side has to count *down*:
no message may be pulled twice. Both conditions are needed, and they are proved by opposite
arguments, so the bookkeeping is separate. This is the general form; the register instance supplies
its two hypotheses from `readMessage_inj` (only one row can pull a given read message) and from the
three slots' timestamps differing within a row. -/

private theorem countP_le_one_flatMap {α β : Type _} (P : β → Bool) (f : α → List β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).countP P ≤ 1) →
      (∀ i j, ∀ (hi : i < l.length) (hj : j < l.length),
        0 < (f l[i]).countP P → 0 < (f l[j]).countP P → i = j) →
      (l.flatMap f).countP P ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
      intro h_row h_uniq
      rw [List.flatMap_cons, List.countP_append]
      have h_a : (f a).countP P ≤ 1 := h_row a List.mem_cons_self
      by_cases h_pos : 0 < (f a).countP P
      · have h_tail_zero : (t.flatMap f).countP P = 0 := by
          by_contra h_c
          obtain ⟨b, hb, hPb⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero h_c)
          obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.mp hb
          obtain ⟨k, h_k⟩ := List.mem_iff_getElem?.mp hx
          have h_k_lt : k < t.length := by
            by_contra h_ge
            rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h_ge)] at h_k
            simp at h_k
          have h_get : t[k] = x := by
            have := h_k
            rw [List.getElem?_eq_getElem h_k_lt] at this
            exact Option.some.inj this
          have := h_uniq 0 (k + 1) (by simp) (by simpa using h_k_lt) (by simpa using h_pos)
            (by simpa [h_get] using List.countP_pos_iff.mpr ⟨b, hbx, hPb⟩)
          omega
        omega
      · have h_a_zero : (f a).countP P = 0 := by omega
        have := ih (fun x hx => h_row x (List.mem_cons_of_mem _ hx))
          (fun i j hi hj h_i h_j => by
            have := h_uniq (i + 1) (j + 1) (by simpa using hi) (by simpa using hj)
              (by simpa using h_i) (by simpa using h_j)
            omega)
        omega

private theorem countP_le_one_of_unique_index {β : Type _} (P : β → Bool) :
    ∀ (l : List β), (∀ i j, ∀ (hi : i < l.length) (hj : j < l.length),
      P l[i] = true → P l[j] = true → i = j) → l.countP P ≤ 1 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h_uniq
      rw [List.countP_cons]
      by_cases h_a : P a = true
      · have h_tail : t.countP P = 0 := by
          by_contra h_c
          obtain ⟨b, hb, hPb⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero h_c)
          obtain ⟨k, h_k⟩ := List.mem_iff_getElem?.mp hb
          have h_k_lt : k < t.length := by
            by_contra h_ge
            rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h_ge)] at h_k
            simp at h_k
          have h_get : t[k] = b := by
            have h' := h_k
            rw [List.getElem?_eq_getElem h_k_lt] at h'
            exact Option.some.inj h'
          have := h_uniq 0 (k + 1) (by simp) (by simpa using h_k_lt) (by simpa using h_a)
            (by simpa [h_get] using hPb)
          omega
        simp [h_a, h_tail]
      · have := ih (fun i j hi hj h_i h_j => by
          have := h_uniq (i + 1) (j + 1) (by simpa using hi) (by simpa using hj)
            (by simpa using h_i) (by simpa using h_j)
          omega)
        simp only [Bool.not_eq_true] at h_a
        simp [h_a] <;> omega

/-- **One row pulls a given message at most once.** Of Main's six memory-bus emissions the three
    register-pre pushes ride at a boolean selector, so never at `-1`; the three current accesses
    carry timestamps `1 + 4k`, `2 + 4k`, `3 + 4k`, so at most one can match a fixed message. This
    is the first of `countP_le_one_flatMap`'s two hypotheses, at the register instance. -/
theorem row_memBus_pullCount_le_one {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    (h_constraints : table.Constraints) {row : Array FGL} (h_row : row ∈ table.table)
    {msg : Array FGL} :
    ((Main.componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw (table.environment row)).countP
      (fun i => decide (i.mult = -1) && decide (i.msg = msg)) ≤ 1 := by
  have h_push : ∀ s : RegSlot,
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment row)).mult ≠ -1 := by
    intro s h_c
    rcases main_regPre_mult_zero_or_one h_component h_constraints h_row s with h | h <;>
      · rw [h] at h_c
        revert h_c
        decide
  have h_pull_ne : ∀ s t : RegSlot, s ≠ t →
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
          (s.memMult (Main.componentWithRomMemAndOpBus length program).rowInputVar)
          (s.memMessageExpr
            (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment row)).msg
      ≠ (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
          (t.memMult (Main.componentWithRomMemAndOpBus length program).rowInputVar)
          (t.memMessageExpr
            (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment row)).msg := by
    intro s t h_st h_c
    have h_eq := memBusMessage_eq_of_eval_emitted_provider_msg_eq h_c
    rw [RegSlot.eval_memMessageExpr, RegSlot.eval_memMessageExpr] at h_eq
    have h_ts := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_eq
    rw [RegSlot.readMessage_timestamp, RegSlot.readMessage_timestamp] at h_ts
    obtain ⟨index, h_index, h_step⟩ := exists_main_step_index_of_mem h_component h_row
    refine h_st (slotOffset_inj ?_)
    rw [readTimestamp_eq_offset_of_main_step h_step s,
      readTimestamp_eq_offset_of_main_step h_step t] at h_ts
    have hv := congrArg Fin.val h_ts
    rw [slot_timestamp_val (slotOffset_le_three s) h_index,
      slot_timestamp_val (slotOffset_le_three t) h_index] at hv
    omega
  have h_a := h_push RegSlot.a
  have h_b := h_push RegSlot.b
  have h_c := h_push RegSlot.c
  have h_ab := h_pull_ne RegSlot.a RegSlot.b (by decide)
  have h_ac := h_pull_ne RegSlot.a RegSlot.c (by decide)
  have h_bc := h_pull_ne RegSlot.b RegSlot.c (by decide)
  simp only [RegSlot.selectorExpr, RegSlot.regPreMessageExpr] at h_a h_b h_c
  simp only [RegSlot.memMult, RegSlot.memMessageExpr] at h_ab h_ac h_bc
  rw [Operations.interactionValuesWith_eq_map,
    Main.componentWithRomMemAndOpBus_interactionsWith_memBus]
  refine countP_le_one_of_unique_index _ _ ?_
  intro i j hi hj h_i h_j
  simp only [List.length_map, List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp_all [Bool.and_eq_true, decide_eq_true_iff]

/-- **A pull in a Main row is one of the three current accesses.** The three register-pre pushes
    ride at a boolean selector, so a `-1` interaction can only be a current access. This is the
    extraction step the table-level bound needs: it turns "some position matched" into "this slot's
    read message is the message". -/
theorem exists_regSlot_of_row_pull {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    (h_constraints : table.Constraints) {row : Array FGL} (h_row : row ∈ table.table)
    {msg : Array FGL}
    (h_pos : 0 < ((Main.componentWithRomMemAndOpBus length program).operations.interactionValuesWith
        ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw (table.environment row)).countP
      (fun i => decide (i.mult = -1) && decide (i.msg = msg))) :
    ∃ s : RegSlot,
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
          (s.memMult (Main.componentWithRomMemAndOpBus length program).rowInputVar)
          (s.memMessageExpr
            (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment row)).msg = msg := by
  have h_push : ∀ s : RegSlot,
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus length program).rowInputVar)
        (s.regPreMessageExpr
          (Main.componentWithRomMemAndOpBus length program).rowInputVar)).toRaw).eval
        (table.environment row)).mult ≠ -1 := by
    intro s h_c
    rcases main_regPre_mult_zero_or_one h_component h_constraints h_row s with h | h <;>
      · rw [h] at h_c
        revert h_c
        decide
  rw [Operations.interactionValuesWith_eq_map,
    Main.componentWithRomMemAndOpBus_interactionsWith_memBus] at h_pos
  have h_a := h_push RegSlot.a
  have h_b := h_push RegSlot.b
  have h_c := h_push RegSlot.c
  simp only [RegSlot.selectorExpr, RegSlot.regPreMessageExpr] at h_a h_b h_c
  obtain ⟨x, h_x, h_px⟩ := List.countP_pos_iff.mp h_pos
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h_x
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_px
  rcases h_x with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h_px.1 h_a
  · exact ⟨RegSlot.a, h_px.2⟩
  · exact absurd h_px.1 h_b
  · exact ⟨RegSlot.b, h_px.2⟩
  · exact absurd h_px.1 h_c
  · exact ⟨RegSlot.c, h_px.2⟩

/-- **The Main table pulls a given message at most once.** Row-level from
    `row_memBus_pullCount_le_one`; across rows because equal read messages force equal timestamps,
    and a timestamp names the row index (`slot_index_eq_of_readTimestamp_eq`). -/
theorem mainTable_pullCount_le_one {n : ℕ} (trace : AcceptedZiskTrace n) {table : Table FGL}
    (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      Main.componentWithRomMemAndOpBus trace.programLength trace.program)
    {msg : Array FGL} :
    (table.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun i => decide (i.mult = -1) && decide (i.msg = msg)) ≤ 1 := by
  have h_constraints := trace.constraints_hold table h_table
  rw [Table.interactionsWith, h_component]
  refine countP_le_one_flatMap _ _ table.table (fun arr h_arr => ?_) (fun i j hi hj h_i h_j => ?_)
  · exact row_memBus_pullCount_le_one h_component h_constraints h_arr
  · have h_i_lt : i < table.table.length := by simpa using hi
    have h_j_lt : j < table.table.length := by simpa using hj
    obtain ⟨s, h_s⟩ :=
      exists_regSlot_of_row_pull h_component h_constraints (List.getElem_mem h_i_lt) h_i
    obtain ⟨t, h_t⟩ :=
      exists_regSlot_of_row_pull h_component h_constraints (List.getElem_mem h_j_lt) h_j
    have h_raw := h_s.trans h_t.symm
    have h_eq := memBusMessage_eq_of_eval_emitted_provider_msg_eq h_raw
    rw [RegSlot.eval_memMessageExpr, RegSlot.eval_memMessageExpr] at h_eq
    have h_ts := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h_eq
    rw [RegSlot.readMessage_timestamp, RegSlot.readMessage_timestamp] at h_ts
    have h_ri := mainTableRowAtOrZero_get trace.program table ⟨i, h_i_lt⟩
    have h_rj := mainTableRowAtOrZero_get trace.program table ⟨j, h_j_lt⟩
    simp only [List.get_eq_getElem] at h_ri h_rj
    rw [← h_ri, ← h_rj] at h_ts
    exact (slot_index_eq_of_readTimestamp_eq h_component h_i_lt h_j_lt h_ts).2

/-- Casting is injective below the modulus, which is how a field-level count equality becomes a
    `ℕ` one. -/
private lemma nat_eq_of_cast_eq {a b : ℕ} (ha : a < GL_prime) (hb : b < GL_prime)
    (h : ((a : ℕ) : FGL) = ((b : ℕ) : FGL)) : a = b := by
  have h_val := congrArg Fin.val h
  rwa [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h_val

/-- **The boundary table pulls a given message at most once.** Each row emits one pull, the boot,
    and one push, the reload. Two boot pulls carrying the same message name the same register — and
    since the fidelity repair the register *is* the row index, so they are the same row.

    This half was false before `reg` became component-owned data: two boundary rows could then carry
    the same register, and one message could be pulled twice.

    The table is destructured up front. `Table.table` is a `match` on `component.fixedColumns`, so
    rewriting with `h_component` under it hits "motive is not type correct"; after `subst` the match
    computes and the effective rows are `rfl`. Same pattern as
    `mainTableRowAtOrZero_segment_l1_eq_fixedAt`. -/
theorem registerBoundaryTable_pullCount_le_one
    {table : Table FGL} (h_component : table.component = RegisterBoundary.component)
    {msg : Array FGL} :
    (table.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun i => decide (i.mult = -1) && decide (i.msg = msg)) ≤ 1 := by
  cases table with
  | mk component rawRows data raw_uniform_width fixed_domain =>
  change component = RegisterBoundary.component at h_component
  subst component
  have h_rowList : ∀ env : Environment FGL,
      RegisterBoundary.component.operations.interactionValuesWith
          ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw env
        = [ (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted (-1)
              (RegisterBoundary.bootMessageExpr
                RegisterBoundary.component.rowInputVar)).toRaw).eval env)
          , (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted 1
              (RegisterBoundary.reloadMessageExpr
                RegisterBoundary.component.rowInputVar)).toRaw).eval env) ] := by
    intro env
    rw [Operations.interactionValuesWith_eq_map,
      RegisterBoundary.component_interactionsWith_memBus]
    rfl
  have h_reload_mult : ∀ env : Environment FGL,
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted 1
        (RegisterBoundary.reloadMessageExpr
          RegisterBoundary.component.rowInputVar)).toRaw).eval env).mult = 1 := fun _ => rfl
  have h_tableRows :
      (Table.table ⟨RegisterBoundary.component, rawRows, data, raw_uniform_width, fixed_domain⟩)
        = rawRows.mapIdx
          (fun idx raw => RegisterBoundary.registerBoundaryFixedColumns.materialize idx raw) := rfl
  rw [Table.interactionsWith]
  refine countP_le_one_flatMap _ _ _ (fun arr _ => ?_) (fun i j hi hj h_i h_j => ?_)
  · rw [h_rowList]
    refine countP_le_one_of_unique_index _ _ (fun a b ha hb h_a h_b => ?_)
    have h2a : a < 2 := by simpa using ha
    have h2b : b < 2 := by simpa using hb
    interval_cases a <;> interval_cases b <;>
      first
        | rfl
        | (exfalso
           simp only [List.getElem_cons_zero, List.getElem_cons_succ, Bool.and_eq_true,
             decide_eq_true_iff] at h_a h_b
           first
             | exact absurd (h_b.1.symm.trans (h_reload_mult _)) (by decide)
             | exact absurd (h_a.1.symm.trans (h_reload_mult _)) (by decide))
  · have h_boot : ∀ (k : ℕ) (hk : k < rawRows.length),
        0 < (RegisterBoundary.component.operations.interactionValuesWith
              ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw
              (Environment.fromArray
                (RegisterBoundary.registerBoundaryFixedColumns.materialize k rawRows[k]) data)).countP
            (fun i => decide (i.mult = -1) && decide (i.msg = msg)) →
          (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted (-1)
            (RegisterBoundary.bootMessageExpr
              RegisterBoundary.component.rowInputVar)).toRaw).eval
            (Environment.fromArray
              (RegisterBoundary.registerBoundaryFixedColumns.materialize k rawRows[k]) data)).msg
            = msg := by
      intro k hk h_pos
      rw [h_rowList] at h_pos
      obtain ⟨x, h_x, h_px⟩ := List.countP_pos_iff.mp h_pos
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_x
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h_px
      rcases h_x with rfl | rfl
      · exact h_px.2
      · exact absurd (h_px.1.symm.trans (h_reload_mult _)) (by decide)
    simp only [h_tableRows, List.length_mapIdx] at hi hj
    simp only [h_tableRows, List.getElem_mapIdx] at h_i h_j
    have h_i_lt : i < rawRows.length := hi
    have h_j_lt : j < rawRows.length := hj
    have h_bi := h_boot i h_i_lt h_i
    have h_bj := h_boot j h_j_lt h_j
    have h_eq := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_bi.trans h_bj.symm)
    rw [RegisterBoundary.eval_bootMessageExpr, RegisterBoundary.eval_bootMessageExpr] at h_eq
    have h_ptr := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.ptr h_eq
    simp only [RegisterBoundary.bootMessage] at h_ptr
    rw [RegisterBoundary.reg_of_materialize, RegisterBoundary.reg_of_materialize] at h_ptr
    have h_cap : rawRows.length ≤ RegisterBoundary.registerBoundaryCapacity :=
      fixed_domain RegisterBoundary.registerBoundaryFixedColumns rfl
    have h_i31 : i < 31 := by
      simp only [RegisterBoundary.registerBoundaryCapacity] at h_cap; omega
    have h_j31 : j < 31 := by
      simp only [RegisterBoundary.registerBoundaryCapacity] at h_cap; omega
    simp only [IndexedFixedColumns.fixedAt,
      RegisterBoundary.registerBoundaryFixedColumns,
      RegisterBoundary.registerBoundaryFixedValues,
      RegisterBoundary.registerBoundaryCapacity, Nat.mod_eq_of_lt h_i31,
      Nat.mod_eq_of_lt h_j31, dif_pos] at h_ptr
    have h_prime : GL_prime = 18446744069414584321 := rfl
    have h_nat := nat_eq_of_cast_eq (a := i + 1) (b := j + 1) (by omega) (by omega) h_ptr
    omega

/-- A Main table with a pull at a message has a row and slot whose current access carries it. -/
theorem exists_mainRead_of_table_pull {n : ℕ} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      Main.componentWithRomMemAndOpBus trace.programLength trace.program)
    {msg : Array FGL}
    (h_pos : 0 < (table.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun i => decide (i.mult = -1) && decide (i.msg = msg))) :
    ∃ (index : ℕ), ∃ h : index < table.table.length, ∃ s : RegSlot,
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
          (s.memMult (Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar)
          (s.memMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
            trace.program).rowInputVar)).toRaw).eval
        (table.environment (table.table[index]'h))).msg = msg := by
  rw [Table.interactionsWith, h_component] at h_pos
  obtain ⟨x, h_x, h_px⟩ := List.countP_pos_iff.mp h_pos
  obtain ⟨arr, h_arr, h_xarr⟩ := List.mem_flatMap.mp h_x
  obtain ⟨index, h_index, rfl⟩ := List.getElem_of_mem h_arr
  refine ⟨index, h_index, ?_⟩
  exact exists_regSlot_of_row_pull h_component (trace.constraints_hold table h_table)
    (List.getElem_mem h_index)
    (List.countP_pos_iff.mpr ⟨x, h_xarr, h_px⟩)

/-- A boundary table with a pull at a message has a row whose boot carries it. -/
theorem exists_boot_of_table_pull {n : ℕ} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_component : table.component = RegisterBoundary.component)
    {msg : Array FGL}
    (h_pos : 0 < (table.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun i => decide (i.mult = -1) && decide (i.msg = msg))) :
    ∃ (index : ℕ), ∃ h : index < table.table.length,
      (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted (-1)
          (RegisterBoundary.bootMessageExpr
            RegisterBoundary.component.rowInputVar)).toRaw).eval
        (table.environment (table.table[index]'h))).msg = msg := by
  have h_rowList : ∀ env : Environment FGL,
      RegisterBoundary.component.operations.interactionValuesWith
          ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw env
        = [ (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted (-1)
              (RegisterBoundary.bootMessageExpr
                RegisterBoundary.component.rowInputVar)).toRaw).eval env)
          , (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted 1
              (RegisterBoundary.reloadMessageExpr
                RegisterBoundary.component.rowInputVar)).toRaw).eval env) ] := by
    intro env
    rw [Operations.interactionValuesWith_eq_map,
      RegisterBoundary.component_interactionsWith_memBus]
    rfl
  rw [Table.interactionsWith, h_component] at h_pos
  obtain ⟨x, h_x, h_px⟩ := List.countP_pos_iff.mp h_pos
  obtain ⟨arr, h_arr, h_xarr⟩ := List.mem_flatMap.mp h_x
  obtain ⟨index, h_index, rfl⟩ := List.getElem_of_mem h_arr
  refine ⟨index, h_index, ?_⟩
  rw [h_rowList] at h_xarr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_xarr
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_px
  rcases h_xarr with rfl | rfl
  · exact h_px.2
  · exfalso
    have h_one : (1 : FGL) = -1 := h_px.1
    exact absurd h_one (by decide)

/-- **A Main current access is never the boundary boot pull.** The boot sits at timestamp `0`; a
    Main read sits at `offset + 4 * index` with `offset ∈ {1, 2, 3}`, so its `val` is at least one.
    This is what stops the Main and boundary tables from both contributing a pull at one message. -/
theorem mainRead_ne_boot {length : ℕ} {program : Program length} {table : Table FGL}
    (h_component : table.component = Main.componentWithRomMemAndOpBus length program)
    {index : ℕ} (h_index : index < table.table.length) (s : RegSlot)
    (row : RegisterBoundary.RegisterBoundaryRow FGL)
    (h : s.readMessage (mainTableRowAtOrZero program table index)
      = RegisterBoundary.bootMessage row) :
    False := by
  have h_ts := congrArg ZiskFv.Channels.MemoryBus.MemBusMessage.timestamp h
  rw [RegSlot.readMessage_timestamp] at h_ts
  have h_step := mainRowAt_main_step h_component h_index
  rw [readTimestamp_eq_offset_of_main_step h_step s] at h_ts
  have h_val := congrArg Fin.val h_ts
  rw [slot_timestamp_val (slotOffset_le_three s)
    (main_index_lt_mainFixedCapacity h_component h_index)] at h_val
  have h_pos : 1 ≤ slotOffset s := by cases s <;> decide
  simp only [RegisterBoundary.bootMessage] at h_val
  omega

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

/-- **The witness pulls a `mem_op = 3` message at most once.**

    Every table contributes at most one: Main and `RegisterBoundary` by their own bounds, every
    other component nothing at all (`memBus_mem_op_three_table_component`). And no two tables both
    contribute — two Mains or two boundaries are the same position in `allTables` by the width
    profile, and a Main and a boundary cannot both match because a boot pull sits at timestamp `0`
    while a Main read sits at `offset + 4 * index`.

    This is the bound push-injectivity consumes: a register-pre push rides at `+1`, balance forces
    as many pulls as pushes, and there is at most one pull. -/
theorem witness_pullCount_le_one {n : ℕ} (trace : AcceptedZiskTrace n)
    {refEnv : Environment FGL} {refMult : Expression FGL}
    {refMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_ref_op : (eval refEnv refMsg).mem_op = 3) :
    (trace.witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
      (fun i => decide (i.mult = -1) &&
        decide (i.msg = (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted refMult
          refMsg).toRaw).eval refEnv).msg)) ≤ 1 := by
  set msg := (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted refMult refMsg).toRaw).eval
    refEnv).msg with h_msgdef
  have h_cls : ∀ tbl ∈ trace.witness.allTables,
      0 < (tbl.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => decide (i.mult = -1) && decide (i.msg = msg)) →
      tbl.component = Main.componentWithRomMemAndOpBus trace.programLength trace.program
        ∨ tbl.component = RegisterBoundary.component := by
    intro tbl h_tbl h_pos
    obtain ⟨x, h_x, h_px⟩ := List.countP_pos_iff.mp h_pos
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h_px
    refine memBus_mem_op_three_table_component trace.constraints_hold trace.spec_holds h_ref_op
      h_tbl h_x h_px.2 ?_ ?_
    · rw [h_px.1]; decide
    · rw [h_px.1]; decide
  rw [EnsembleWitness.interactionsWith]
  refine countP_le_one_flatMap _ _ trace.witness.allTables (fun tbl h_tbl => ?_)
    (fun a b ha hb h_a h_b => ?_)
  · by_cases h_pos : 0 < (tbl.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw).countP
        (fun i => decide (i.mult = -1) && decide (i.msg = msg))
    · rcases h_cls tbl h_tbl h_pos with h_main | h_bd
      · exact mainTable_pullCount_le_one trace h_tbl h_main
      · exact registerBoundaryTable_pullCount_le_one h_bd
    · omega
  · rcases h_cls _ (List.getElem_mem ha) h_a with h_ma | h_ba <;>
      rcases h_cls _ (List.getElem_mem hb) h_b with h_mb | h_bb
    · rw [allTables_index_eq_main trace.witness ha h_ma,
        allTables_index_eq_main trace.witness hb h_mb]
    · exfalso
      obtain ⟨ia, hia, s, h_sa⟩ := exists_mainRead_of_table_pull trace (List.getElem_mem ha) h_ma h_a
      obtain ⟨ib, hib, h_sb⟩ := exists_boot_of_table_pull trace h_bb h_b
      have h_eq := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_sa.trans h_sb.symm)
      rw [RegSlot.eval_memMessageExpr, RegisterBoundary.eval_bootMessageExpr] at h_eq
      have h_ri := mainTableRowAtOrZero_get trace.program _ ⟨ia, hia⟩
      simp only [List.get_eq_getElem] at h_ri
      rw [← h_ri] at h_eq
      exact mainRead_ne_boot h_ma hia s _ h_eq
    · exfalso
      obtain ⟨ib, hib, s, h_sb⟩ := exists_mainRead_of_table_pull trace (List.getElem_mem hb) h_mb h_b
      obtain ⟨ia, hia, h_sa⟩ := exists_boot_of_table_pull trace h_ba h_a
      have h_eq := memBusMessage_eq_of_eval_emitted_provider_msg_eq (h_sb.trans h_sa.symm)
      rw [RegSlot.eval_memMessageExpr, RegisterBoundary.eval_bootMessageExpr] at h_eq
      have h_ri := mainTableRowAtOrZero_get trace.program _ ⟨ib, hib⟩
      simp only [List.get_eq_getElem] at h_ri
      rw [← h_ri] at h_eq
      exact mainRead_ne_boot h_mb hib s _ h_eq
    · rw [allTables_index_eq_registerBoundary trace.witness ha h_ba,
        allTables_index_eq_registerBoundary trace.witness hb h_bb]

/-- **Every interaction at a `mem_op = 3` message rides at `0`, `+1` or `-1`.** The side condition
    `pushCount_eq_pullCount_of_balanced` asks for. Anything outside `{0, 1}` is, by the
    classification, a Main current access or the boot pull — and `mem_op = 3` forces the Main slot's
    selector, hence its `-1`. -/
theorem memBus_memOp3_mult_trichotomy {n : ℕ} (trace : AcceptedZiskTrace n)
    {refEnv : Environment FGL} {refMult : Expression FGL}
    {refMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_ref_op : (eval refEnv refMsg).mem_op = 3)
    {i : Interaction FGL}
    (h_i : i ∈ trace.witness.interactionsWith ZiskFv.Channels.MemoryBus.MemBusChannel.toRaw)
    (h_msg : i.msg = (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted refMult
      refMsg).toRaw).eval refEnv).msg) :
    i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1 := by
  by_cases h0 : i.mult = 0
  · exact Or.inl h0
  by_cases h1 : i.mult = 1
  · exact Or.inr (Or.inl h1)
  refine Or.inr (Or.inr ?_)
  rcases memBus_mem_op_three_counterpart trace.constraints_hold trace.spec_holds h_ref_op h_i
      h_msg h0 h1 with
    ⟨tbl, h_tbl, h_comp, r, h_r, t, h_eval⟩ | ⟨btbl, h_btbl, h_bcomp, br, h_br, h_eval⟩
  · have h_raw : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (t.memMult (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)
        (t.memMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)).toRaw).eval (tbl.environment r)).msg
        = (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted refMult refMsg).toRaw).eval
          refEnv).msg := by
      rw [← h_eval]; exact h_msg
    have h_meq := memBusMessage_eq_of_eval_emitted_provider_msg_eq h_raw
    have h_op : (eval (tbl.environment r)
        (t.memMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)).mem_op = 3 := by
      rw [h_meq]; exact h_ref_op
    have h_sel := regSlot_selector_of_mem_op_three h_comp
      (trace.constraints_hold tbl h_tbl) h_r t h_op
    rw [h_eval]
    exact (regSlot_mem_pull_of_selector trace.channels_balanced trace.constraints_hold
      trace.spec_holds h_tbl h_comp h_r t h_sel).1
  · rw [h_eval]; rfl

/-- **Push-injectivity: two distinct active register slots cannot share a register-pre message.**

    Balance forces as many pushes as pulls at that message
    (`pushCount_eq_pullCount_of_balanced`); two distinct slots would give two push positions
    (`two_le_witness_pushCount`); and there is at most one pull position
    (`witness_pullCount_le_one`). So `2 ≤ 1`.

    This is the fact the register telescope's chain merge rests on: `pred` — the slot whose read
    answers a given register-pre push — is injective, so two access chains for one register cannot
    stay disjoint. -/
theorem regPreMessage_inj {n : ℕ} (trace : AcceptedZiskTrace n)
    {table : Table FGL} (h_table : table ∈ trace.witness.allTables)
    (h_component : table.component =
      Main.componentWithRomMemAndOpBus trace.programLength trace.program)
    {i j : ℕ} (hi : i < table.table.length) (hj : j < table.table.length) {s t : RegSlot}
    (h_sel_i : s.selector (eval (table.environment (table.table[i]'hi))
      (Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1)
    (h_sel_j : t.selector (eval (table.environment (table.table[j]'hj))
      (Main.componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar) = 1)
    (h_msg : (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (s.selectorExpr (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)
        (s.regPreMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)).toRaw).eval (table.environment (table.table[i]'hi))).msg
      = (((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
        (t.selectorExpr (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)
        (t.regPreMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
          trace.program).rowInputVar)).toRaw).eval (table.environment (table.table[j]'hj))).msg) :
    i = j ∧ s = t := by
  by_contra h_ne
  have h_ne' : i ≠ j ∨ (i = j ∧ s ≠ t) := by
    by_cases h_ij : i = j
    · exact Or.inr ⟨h_ij, fun h_st => h_ne ⟨h_ij, h_st⟩⟩
    · exact Or.inl h_ij
  have h_mult_i := regSlot_regPre_mult_one (table := table)
    (row := table.table[i]'hi) s h_sel_i
  have h_mult_j := regSlot_regPre_mult_one (table := table)
    (row := table.table[j]'hj) t h_sel_j
  have h_ref_op : (eval (table.environment (table.table[i]'hi))
      (s.regPreMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar)).mem_op = 3 :=
    RegSlot.eval_regPreMessageExpr_mem_op s _ _
  have h_two := two_le_witness_pushCount h_table h_component hi hj h_ne'
    h_mult_i rfl h_mult_j h_msg.symm
  have h_eq := pushCount_eq_pullCount_of_balanced (witness := trace.witness)
    trace.channels_balanced
    ((((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted
      (s.selectorExpr (Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar)
      (s.regPreMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar)).toRaw).eval (table.environment (table.table[i]'hi))).msg)
    (fun k h_k h_kmsg => memBus_memOp3_mult_trichotomy trace
      (refEnv := table.environment (table.table[i]'hi))
      (refMult := s.selectorExpr (Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar)
      (refMsg := s.regPreMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
        trace.program).rowInputVar) h_ref_op h_k h_kmsg)
  have h_one := witness_pullCount_le_one trace
    (refEnv := table.environment (table.table[i]'hi))
    (refMult := s.selectorExpr (Main.componentWithRomMemAndOpBus trace.programLength
      trace.program).rowInputVar)
    (refMsg := s.regPreMessageExpr (Main.componentWithRomMemAndOpBus trace.programLength
      trace.program).rowInputVar) h_ref_op
  omega

end ZiskFv.Compliance
