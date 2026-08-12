import Clean.Air.Balance

/-!
# Spike S0.1 (#330) — multiplicity-gated channel consistency

Question: our MemBus emissions are selector-gated, so an inactive access emits at
multiplicity `0`. Clean charges `Requirements` at every `mult ≠ -1`, which includes `0`,
so a non-trivial typed-channel `Guarantees` would oblige every inactive push to prove a
fact about a garbage message.

A message-content guard cannot fix this: `aRegPreMessageExpr` hardcodes `mem_op := 3`
while carrying `a_src_reg` as its multiplicity, so an inactive register-preload push still
presents `mem_op = 3`.

So the guard must be on multiplicity. A typed `Channel` cannot express that
(`Channel.Guarantees` takes only `(message, data)`), so this spike tests a `RawChannel`
with a multiplicity-aware `Requirements`.

Such a channel is NOT `Normal` — `Normal.grts_of_reqs` is stated for every `mult ≠ -1`, so
a `mult = 0` push cannot transfer — hence `consistent_of_normal` does not apply. But
`exists_push_of_pull` returns a counterpart with `b.mult ≠ -1 ∧ b.mult ≠ 0`, which is
exactly the extra hypothesis the gated form needs.
-/

namespace Spike330

variable {F : Type} [Field F] [DecidableEq F]

/-- Multiplicity-gated raw channel: a push at multiplicity `0` — an inactive,
    selector-gated emission — owes nothing. -/
def gated (arity : ℕ) (P : Vector F arity → ProverData F → Prop) : RawChannel F where
  name := "gated"
  arity := arity
  Guarantees mult msg data := mult = -1 → P msg data
  Requirements mult msg data := mult ≠ -1 → mult ≠ 0 → P msg data

/-- **S0.1.** Balance + gated `Requirements` on all interactions ⟹ `Guarantees` on all
    interactions. Mirrors `consistent_of_normal`, but takes the counterpart's `mult ≠ 0`
    from `exists_push_of_pull` instead of going through `Normal`. -/
theorem gated_consistent (arity : ℕ) (P : Vector F arity → ProverData F → Prop) :
    (gated (F := F) arity P).Consistent := by
  constructor
  intro interactions data balance reqs a a_mem
  have a_channel_eq := (reqs a a_mem).left
  simp only [Interaction.Guarantees]
  intro _a_assume
  have a_msg_size : a.msg.size = (gated (F := F) arity P).arity := by
    rw [a.same_size, a_channel_eq]
  suffices h : (gated (F := F) arity P).Guarantees a.mult ⟨a.msg, a_msg_size⟩ data by
    convert h
  intro a_mult
  obtain ⟨b, b_mem, b_msg_eq, b_mult_ne_neg_one, b_mult_ne_zero⟩ :=
    exists_push_of_pull interactions balance a a_mem a_mult
  have b_channel_eq := (reqs b b_mem).left
  have b_reqs := (reqs b b_mem).right
  have b_msg_size : b.msg.size = (gated (F := F) arity P).arity := by
    rw [b.same_size, b_channel_eq]
  have hb : (gated (F := F) arity P).Requirements b.mult ⟨b.msg, b_msg_size⟩ data := by
    simp only [Interaction.Requirements, Interaction.msgVector] at b_reqs
    convert b_reqs
    exact b_channel_eq.symm
  have hP := hb b_mult_ne_neg_one b_mult_ne_zero
  convert hP using 2
  exact b_msg_eq.symm

end Spike330

#print axioms Spike330.gated_consistent
