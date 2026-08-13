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
