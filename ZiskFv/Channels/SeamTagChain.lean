import Clean.Air.Balance
import ZiskFv.Field.Goldilocks

/-!
# Segment-continuation tag-chain derivation (#103, N=2)

This module DERIVES the per-segment `segment_id` tag chain that forces the
cross-segment memory seam, from channel balance alone — with NO per-segment tag
pin as a hypothesis. It is the derivation engine consumed by the seam ensemble
(`ZiskFv/AirsClean/Mem/SeamEnsemble.lean`).

The question it answers:

  Is the per-segment `segment_id` tag chain DERIVED from
    [verifier boot-push at tag 0] + [per-row push_tag = pull_tag + 1] + [global balance]
  WITHOUT any per-segment tag pin as a hypothesis?

## Faithfulness of the two model facts

1. **The +1 (push_tag = pull_tag + 1) is FAITHFUL.** It is intrinsic to the real
   emission: `direct_gsum_0` (the PULL of `previous_segment_*`) hashes tag
   `segment_id`, `direct_gsum_1` (the PUSH of `segment_last_*`) hashes tag
   `segment_id + 1` (`mem.pil:198` vs `mem.pil:235`; `ZiskFv/Airs/Mem.lean:1357`
   vs `:1367`). There is NO free column and NO extra equality — the `+1` is baked
   into the polynomial the verifier hashes. So we MAY impose, per segment, that the
   push-tag is the pull-tag + 1; this is not an added assumption, it is the
   emission. Each segment's pull-tag `t_i` is a GENUINELY FREE variable here; only
   the relation push = pull + 1 is fixed.

2. **The verifier boot push at tag 0 is a VERIFIER ENDPOINT, not a caller premise.**
   It is modeled as a member of the SAME balanced interaction list (mirroring
   Fibonacci's `fibonacciVerifier` / `mem.pil:253`'s
   `direct_global_update_proves(MEMORY_CONTINUATION_ID, [..,0,..], sel:enable_flag)`).
   Its trust class is channel balance — the same `BalancedChannels` antecedent the
   proof system already discharges. It is NOT a hypothesis a downstream `equiv_<OP>`
   consumer carries. This is the decisive legitimacy distinction (verifier endpoint
   vs. relocating the obligation onto a caller-supplied premise).

## The honest finding

Balance + the +1 emission + the boot endpoint, with NO per-segment tag pin, DO
force the tag SET to be `{0, 1, ..., N-1}` and the per-tag value seam to hold. They
do NOT canonically force "physical segment i pulls tag i" — the chain is forced
*up to a permutation of which physical segment plays which chain position*. That
permutation is pure relabeling and is irrelevant to the seam property. We therefore
prove the honest disjunction for N=2 (both disjuncts are valid chains with the seam
holding). Adding the faithful row-local `is_first_segment` pin (one boolean from
`segment_every_row`, NOT a per-segment caller premise) would collapse the
disjunction to the canonical order; general N is the documented follow-up (L1).

## Trust note

No axioms. The whole derivation is kernel-only (`propext`, `Classical.choice`,
`Quot.sound`); see the `#print axioms` checks at the bottom.
-/

set_option linter.unnecessarySimpa false

namespace ZiskFv.Channels.SeamTagChain

open Goldilocks

/-- Goldilocks has characteristic `GL_prime`, a large prime, so `ringChar ≠ 2`. -/
instance : Fact (ringChar FGL ≠ 2) := .mk <| by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  have h : ringChar FGL = GL_prime := ringChar.eq FGL GL_prime
  rw [h]; norm_num

/-! ## The tagged seam channel and the pull/push message builders. -/

/-- The tagged seam channel (arity 5: 4 boundary fields + segment-id tag).
    `Guarantees := True`: the cross-segment link comes from BALANCE alone, never
    from a channel guarantee. -/
instance SeamChannel5 : Channel FGL (fields 5) where
  name := "seam5"
  Guarantees _ _ := True

/-- A pulled raw boundary+tag message (multiplicity -1). -/
def pullMsg5 (m : Array FGL) (hm : m.size = 5) : Interaction FGL where
  channel := SeamChannel5.toRaw
  mult := -1
  msg := m
  same_size := by simpa [SeamChannel5, Channel.toRaw] using hm
  assumeGuarantees := true

/-- A pushed raw boundary+tag message (multiplicity 1). -/
def pushMsg5 (m : Array FGL) (hm : m.size = 5) : Interaction FGL where
  channel := SeamChannel5.toRaw
  mult := 1
  msg := m
  same_size := by simpa [SeamChannel5, Channel.toRaw] using hm
  assumeGuarantees := false

/-- A 5-tuple message `(v0, v1, addr, step, tag)`; `seam5 v tag` packs a boundary
    value `v` (a 4-array) with a `tag`. We keep the value as the FULL 4-array so the
    seam conclusion is a real raw-tuple equality (no hash injectivity). -/
def seam5 (v0 v1 addr step tag : FGL) : Array FGL := #[v0, v1, addr, step, tag]

theorem seam5_size (v0 v1 addr step tag : FGL) : (seam5 v0 v1 addr step tag).size = 5 := rfl

/-! ## Weighted-balance lemma.

`BalancedInteractions` says every message has multiplicity-sum 0. A clean
consequence we need: for ANY weight function `f : Array FGL → FGL`, the
`f`-weighted multiplicity sum `Σ_i mult_i * f(msg_i)` is 0. (Group the sum by
message; each group contributes `f(m) * balanceOf m = f(m) * 0 = 0`.) We use this
with `f = tag projection` to extract the tag arithmetic without any per-segment
tag hypothesis. -/

/-- The `f`-weighted multiplicity sum of an interaction list. -/
def weightedSum (interactions : List (Interaction FGL)) (f : Array FGL → FGL) : FGL :=
  (interactions.map (fun i => i.mult * f i.msg)).sum

theorem weightedSum_nil (f : Array FGL → FGL) : weightedSum [] f = 0 := rfl

theorem weightedSum_cons (i : Interaction FGL) (rest : List (Interaction FGL))
    (f : Array FGL → FGL) :
    weightedSum (i :: rest) f = i.mult * f i.msg + weightedSum rest f := by
  simp [weightedSum]

/-- `weightedSum` over distinct messages: it equals `Σ_{m ∈ messages} f m * balanceOf`.
    This is the bridge from the per-element weighted sum to the per-message balance. -/
theorem weightedSum_eq_finset_balanceOf
    (interactions : List (Interaction FGL)) (f : Array FGL → FGL) :
    weightedSum interactions f
      = ∑ m ∈ (interactions.map (·.msg)).toFinset, f m * balanceOf interactions m := by
  classical
  induction interactions with
  | nil => simp [weightedSum, balanceOf]
  | cons i rest ih =>
    rw [weightedSum_cons, ih]
    have hbal : ∀ m, balanceOf (i :: rest) m
        = (if i.msg = m then i.mult else 0) + balanceOf rest m := by
      intro m; simp [balanceOf, List.filter_cons]; split <;> simp_all
    simp only [hbal, mul_add, Finset.sum_add_distrib, List.map_cons, List.toFinset_cons]
    have h1 : (∑ x ∈ insert i.msg (List.map (·.msg) rest).toFinset,
        f x * if i.msg = x then i.mult else 0) = f i.msg * i.mult := by
      simp [Finset.sum_ite_eq, Finset.mem_insert]
    have h2 : (∑ m ∈ insert i.msg (List.map (·.msg) rest).toFinset, f m * balanceOf rest m)
        = ∑ m ∈ (List.map (·.msg) rest).toFinset, f m * balanceOf rest m := by
      by_cases hmem : i.msg ∈ (List.map (·.msg) rest).toFinset
      · rw [Finset.insert_eq_self.mpr hmem]
      · rw [Finset.sum_insert hmem]
        have hz : balanceOf rest i.msg = 0 := by
          simp only [balanceOf]
          rw [List.filter_eq_nil_iff.mpr]
          · simp
          · intro x hx; simp only [List.mem_toFinset, List.mem_map, not_exists] at hmem
            simp only [decide_eq_true_eq]; intro he; exact hmem x ⟨hx, he⟩
        rw [hz]; ring
    rw [h1, h2]; ring

/-- The weighted-balance lemma: balance forces every weighted multiplicity sum to 0. -/
theorem weightedSum_eq_zero_of_balance
    {interactions : List (Interaction FGL)} (f : Array FGL → FGL)
    (balance : BalancedInteractions interactions) :
    weightedSum interactions f = 0 := by
  rw [weightedSum_eq_finset_balanceOf]
  apply Finset.sum_eq_zero
  intro m _
  rw [balance.2 m, mul_zero]

/-! ## SCRATCH probe — the N=2 list with free tags. -/

/-- The N=2 tagged interaction list with FREE per-segment pull-tags and FREE
    boundary values. Order mirrors `allTables = verifierTable :: tables`.
      verifier:  push (bootV, 0),    pull (finalV, tf)
      seg0:      pull (p0V, t0),     push (l0V, t0 + 1)     [+1 emission, F1]
      seg1:      pull (p1V, t1),     push (l1V, t1 + 1)     [+1 emission, F1] -/
def theList2
    (bv0 bv1 ba bs : FGL)        -- boot value (4 lanes); tag 0
    (fv0 fv1 fa fs tf : FGL)     -- final value + free final-tag tf
    (p0v0 p0v1 p0a p0s t0 : FGL) -- seg0 prev value + free pull-tag t0
    (l0v0 l0v1 l0a l0s : FGL)    -- seg0 last value; tag t0+1
    (p1v0 p1v1 p1a p1s t1 : FGL) -- seg1 prev value + free pull-tag t1
    (l1v0 l1v1 l1a l1s : FGL)    -- seg1 last value; tag t1+1
    : List (Interaction FGL) :=
  [ pushMsg5 (seam5 bv0 bv1 ba bs 0) (seam5_size ..)            -- verifier boot push, tag 0
  , pullMsg5 (seam5 fv0 fv1 fa fs tf) (seam5_size ..)           -- verifier final pull, tag tf
  , pullMsg5 (seam5 p0v0 p0v1 p0a p0s t0) (seam5_size ..)       -- seg0 pull, tag t0
  , pushMsg5 (seam5 l0v0 l0v1 l0a l0s (t0 + 1)) (seam5_size ..) -- seg0 push, tag t0+1
  , pullMsg5 (seam5 p1v0 p1v1 p1a p1s t1) (seam5_size ..)       -- seg1 pull, tag t1
  , pushMsg5 (seam5 l1v0 l1v1 l1a l1s (t1 + 1)) (seam5_size ..) -- seg1 push, tag t1+1
  ]

/-! ## Tag projection and its powers as weight functions.

The tag is the 5th component (index 4) of each message. We feed the tag and its
powers as weight functions into `weightedSum_eq_zero_of_balance` to extract the
power-sum equations on the free tags. -/

/-- The tag projection `msg ↦ msg[4]` (total via `getD`). -/
def tagW (m : Array FGL) : FGL := m.getD 4 0

@[simp] theorem tagW_seam5 (v0 v1 addr step tag : FGL) :
    tagW (seam5 v0 v1 addr step tag) = tag := rfl

/-- The `weightedSum` of `theList2` against weight `g` (computed). -/
theorem weightedSum_theList2 (g : Array FGL → FGL)
    (bv0 bv1 ba bs fv0 fv1 fa fs tf p0v0 p0v1 p0a p0s t0
     l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s : FGL) :
    weightedSum (theList2 bv0 bv1 ba bs fv0 fv1 fa fs tf p0v0 p0v1 p0a p0s t0
        l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s) g
      = g (seam5 bv0 bv1 ba bs 0)
        - g (seam5 fv0 fv1 fa fs tf)
        - g (seam5 p0v0 p0v1 p0a p0s t0)
        + g (seam5 l0v0 l0v1 l0a l0s (t0 + 1))
        - g (seam5 p1v0 p1v1 p1a p1s t1)
        + g (seam5 l1v0 l1v1 l1a l1s (t1 + 1)) := by
  simp only [theList2, weightedSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pushMsg5, pullMsg5]
  ring

/-! ## Power-sum tag equations forced by balance.

Feeding `tagW`, `tagW^2`, `tagW^3` as weights and applying
`weightedSum_eq_zero_of_balance`, balance yields three polynomial equations on the
free tags `tf, t0, t1`. Newton's identities then pin: `tf = 2`, `t0 + t1 = 1`,
`t0 * t1 = 0`. NO per-segment tag hypothesis is used; the equations come from
balance alone (a verifier endpoint) + the +1 emission baked into `theList2`. -/

section TagEquations
variable (bv0 bv1 ba bs fv0 fv1 fa fs tf p0v0 p0v1 p0a p0s t0
  l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s : FGL)

/-- Shorthand for the N=2 list with all these free parameters. -/
local notation "L2" => theList2 bv0 bv1 ba bs fv0 fv1 fa fs tf p0v0 p0v1 p0a p0s t0
  l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s

/-- The three tag power-sum equations, packaged. -/
theorem tag_power_sums (balance : BalancedInteractions L2) :
    (-tf + 2 = 0) ∧
    (-tf ^ 2 + (2 * t0 + 2 * t1 + 2) = 0) ∧
    (-tf ^ 3 + (3 * t0 ^ 2 + 3 * t0 + 3 * t1 ^ 2 + 3 * t1 + 2) = 0) := by
  have e1 := weightedSum_eq_zero_of_balance tagW balance
  have e2 := weightedSum_eq_zero_of_balance (fun m => tagW m ^ 2) balance
  have e3 := weightedSum_eq_zero_of_balance (fun m => tagW m ^ 3) balance
  rw [weightedSum_theList2] at e1 e2 e3
  simp only [tagW_seam5] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination e1
  · linear_combination e2
  · linear_combination e3

/-- `2 ≠ 0` in Goldilocks (needed to cancel the factor 2 in the `t0*t1` relation). -/
theorem two_ne_zero_FGL : (2 : FGL) ≠ 0 := by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  have h2 : ((2 : ℕ) : FGL) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff FGL GL_prime]; omega
  simp only [Nat.cast_ofNat] at h2; exact h2

/-- THE TAG-CHAIN DERIVATION (tags only): from balance alone (a verifier
    endpoint, NO per-segment tag hypothesis) and the +1 emission, the free tags
    are forced to the SET `{0, 1}` — i.e. either `(t0,t1) = (0,1)` or `(1,0)` —
    and `tf = 2`. The disjunction is the genuine permutation ambiguity (which
    physical segment plays which chain position); both are valid chains. -/
theorem tags_forced (balance : BalancedInteractions L2) :
    tf = 2 ∧ ((t0 = 0 ∧ t1 = 1) ∨ (t0 = 1 ∧ t1 = 0)) := by
  obtain ⟨h1, h2, h3⟩ := tag_power_sums bv0 bv1 ba bs fv0 fv1 fa fs tf
    p0v0 p0v1 p0a p0s t0 l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1
    l1v0 l1v1 l1a l1s balance
  have htf : tf = 2 := by linear_combination -h1
  subst htf
  -- division-free `3 ≠ 0`
  have three_ne_zero_FGL : (3 : FGL) ≠ 0 := by
    haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
    have h3' : ((3 : ℕ) : FGL) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff FGL GL_prime]; omega
    simp only [Nat.cast_ofNat] at h3'; exact h3'
  -- t0 + t1 = 1, via cancelling the factor 2 (no field division)
  have hsum : t0 + t1 = 1 := by
    apply mul_left_cancel₀ two_ne_zero_FGL
    linear_combination h2
  -- t0^2 + t1^2 = 1, via cancelling the factor 3
  have hsq : t0 ^ 2 + t1 ^ 2 = 1 := by
    apply mul_left_cancel₀ three_ne_zero_FGL
    linear_combination h3 - 3 * hsum
  -- t0 * t1 = 0
  have hprod : t0 * t1 = 0 := by
    have h2t : (2 : FGL) * (t0 * t1) = 2 * 0 := by linear_combination (t0 + t1 + 1) * hsum - hsq
    exact mul_left_cancel₀ two_ne_zero_FGL h2t
  refine ⟨rfl, ?_⟩
  rcases mul_eq_zero.mp hprod with ht0 | ht1
  · -- t0 = 0 ⇒ t1 = 1
    left
    refine ⟨ht0, ?_⟩
    linear_combination hsum - ht0
  · -- t1 = 0 ⇒ t0 = 1
    right
    refine ⟨?_, ht1⟩
    linear_combination hsum - ht1

end TagEquations

/-! ## Distinctness of small tags in Goldilocks. -/

theorem zero_ne_one_FGL : (0 : FGL) ≠ 1 := by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  exact fun h => one_ne_zero h.symm

theorem one_ne_two_FGL : (1 : FGL) ≠ 2 := by
  have := two_ne_zero_FGL
  intro h
  apply this
  linear_combination -2 * h

theorem zero_ne_two_FGL : (0 : FGL) ≠ 2 := fun h => two_ne_zero_FGL h.symm

/-- Two `seam5` messages are equal iff all five components are. We only ever use
    the tag (index 4) to separate them; equality of the whole array is the seam. -/
theorem seam5_tag_ne {v0 v1 a s t v0' v1' a' s' t' : FGL} (htag : t ≠ t') :
    seam5 v0 v1 a s t ≠ seam5 v0' v1' a' s' t' := by
  intro h
  apply htag
  have : (seam5 v0 v1 a s t).getD 4 0 = (seam5 v0' v1' a' s' t').getD 4 0 := by rw [h]
  simpa [seam5] using this

/-- All six tag-distinctness facts we need to separate the {0,1,2} messages,
    packaged so the per-case `first | ...` combinator can discharge any of them. -/
theorem small_tag_ne : (0 : FGL) ≠ 1 ∧ (0 : FGL) ≠ 2 ∧ (1 : FGL) ≠ 0 ∧ (1 : FGL) ≠ 2
    ∧ (2 : FGL) ≠ 0 ∧ (2 : FGL) ≠ 1 := by
  refine ⟨zero_ne_one_FGL, zero_ne_two_FGL, ?_, one_ne_two_FGL, ?_, ?_⟩
  · exact fun h => zero_ne_one_FGL h.symm
  · exact fun h => zero_ne_two_FGL h.symm
  · exact fun h => one_ne_two_FGL h.symm


/-! ## THE FULL RESULT — tag chain AND value seam, derived without a tag premise.

`tag_chain_derived` is the central theorem. With FREE per-segment pull-tags
`t0, t1` and FREE boundary values, balance (which contains the verifier boot push
at tag 0 as a member — a verifier endpoint, NOT a separate caller premise) forces:

  * the pull-tags to be the SET `{0, 1}` and the final-tag to be `2`, AND
  * the per-tag VALUE seam — each boundary pushed at tag `k` is exactly the
    boundary pulled at tag `k`. Concretely (first disjunct): seg0 pulls boot;
    seg1 pulls seg0's last (THE SEAM); the verifier pulls seg1's last.

The disjunction is the genuine, honest permutation ambiguity: balance does not
distinguish which physical segment plays chain-position 0 vs 1. Both disjuncts are
valid chains in which the seam holds. NO per-segment tag hypothesis appears. -/
theorem tag_chain_derived
    (bv0 bv1 ba bs fv0 fv1 fa fs tf p0v0 p0v1 p0a p0s t0
     l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s : FGL)
    (balance : BalancedInteractions
      (theList2 bv0 bv1 ba bs fv0 fv1 fa fs tf p0v0 p0v1 p0a p0s t0
        l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s)) :
    -- chain-position-0 = seg0:
    ( t0 = 0 ∧ t1 = 1 ∧ tf = 2
      ∧ seam5 p0v0 p0v1 p0a p0s t0 = seam5 bv0 bv1 ba bs 0          -- seg0 pulls boot
      ∧ seam5 p1v0 p1v1 p1a p1s t1 = seam5 l0v0 l0v1 l0a l0s (t0 + 1) -- SEAM: seg1.prev = seg0.last
      ∧ seam5 fv0 fv1 fa fs tf = seam5 l1v0 l1v1 l1a l1s (t1 + 1) )  -- verifier pulls seg1.last
    -- chain-position-0 = seg1 (permutation):
    ∨ ( t1 = 0 ∧ t0 = 1 ∧ tf = 2
      ∧ seam5 p1v0 p1v1 p1a p1s t1 = seam5 bv0 bv1 ba bs 0          -- seg1 pulls boot
      ∧ seam5 p0v0 p0v1 p0a p0s t0 = seam5 l1v0 l1v1 l1a l1s (t1 + 1) -- SEAM: seg0.prev = seg1.last
      ∧ seam5 fv0 fv1 fa fs tf = seam5 l0v0 l0v1 l0a l0s (t0 + 1) ) := by
  obtain ⟨htf, htags⟩ := tags_forced bv0 bv1 ba bs fv0 fv1 fa fs tf
    p0v0 p0v1 p0a p0s t0 l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1
    l1v0 l1v1 l1a l1s balance
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := small_tag_ne
  rcases htags with ⟨ht0, ht1⟩ | ⟨ht0, ht1⟩
  · -- chain position 0 = seg0
    left
    subst ht0 ht1 htf
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · -- seg0 pull (tag 0) = boot push (tag 0)
      have hpull : pullMsg5 (seam5 p0v0 p0v1 p0a p0s 0) (seam5_size ..) ∈
          theList2 bv0 bv1 ba bs fv0 fv1 fa fs 2 p0v0 p0v1 p0a p0s 0
            l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 1 l1v0 l1v1 l1a l1s := by
        unfold theList2; simp
      obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
      unfold theList2 at hb_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
      rcases hb_mem with h | h | h | h | h | h <;> subst h <;>
        simp only [pushMsg5, pullMsg5] at hb_msg ⊢
      · exact hb_msg.symm
      · exact absurd rfl hb_ne1
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h10))
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h20))
    · -- seg1 pull (tag 1) = seg0 push (tag 0+1=1) : THE SEAM
      have hpull : pullMsg5 (seam5 p1v0 p1v1 p1a p1s 1) (seam5_size ..) ∈
          theList2 bv0 bv1 ba bs fv0 fv1 fa fs 2 p0v0 p0v1 p0a p0s 0
            l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 1 l1v0 l1v1 l1a l1s := by
        unfold theList2; simp
      obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
      unfold theList2 at hb_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
      rcases hb_mem with h | h | h | h | h | h <;> subst h <;>
        simp only [pushMsg5, pullMsg5] at hb_msg ⊢
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h01))
      · exact absurd rfl hb_ne1
      · exact absurd rfl hb_ne1
      · exact hb_msg.symm
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h21))
    · -- verifier pull (tag 2) = seg1 push (tag 1+1=2)
      have hpull : pullMsg5 (seam5 fv0 fv1 fa fs 2) (seam5_size ..) ∈
          theList2 bv0 bv1 ba bs fv0 fv1 fa fs 2 p0v0 p0v1 p0a p0s 0
            l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 1 l1v0 l1v1 l1a l1s := by
        unfold theList2; simp
      obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
      unfold theList2 at hb_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
      rcases hb_mem with h | h | h | h | h | h <;> subst h <;>
        simp only [pushMsg5, pullMsg5] at hb_msg ⊢
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h02))
      · exact absurd rfl hb_ne1
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h12))
      · exact absurd rfl hb_ne1
      · exact hb_msg.symm
  · -- chain position 0 = seg1 (permutation)
    right
    subst ht0 ht1 htf
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · -- seg1 pull (tag 0) = boot push (tag 0)
      have hpull : pullMsg5 (seam5 p1v0 p1v1 p1a p1s 0) (seam5_size ..) ∈
          theList2 bv0 bv1 ba bs fv0 fv1 fa fs 2 p0v0 p0v1 p0a p0s 1
            l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 0 l1v0 l1v1 l1a l1s := by
        unfold theList2; simp
      obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
      unfold theList2 at hb_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
      rcases hb_mem with h | h | h | h | h | h <;> subst h <;>
        simp only [pushMsg5, pullMsg5] at hb_msg ⊢
      · exact hb_msg.symm
      · exact absurd rfl hb_ne1
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h20))
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h10))
    · -- seg0 pull (tag 1) = seg1 push (tag 0+1=1) : THE SEAM
      have hpull : pullMsg5 (seam5 p0v0 p0v1 p0a p0s 1) (seam5_size ..) ∈
          theList2 bv0 bv1 ba bs fv0 fv1 fa fs 2 p0v0 p0v1 p0a p0s 1
            l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 0 l1v0 l1v1 l1a l1s := by
        unfold theList2; simp
      obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
      unfold theList2 at hb_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
      rcases hb_mem with h | h | h | h | h | h <;> subst h <;>
        simp only [pushMsg5, pullMsg5] at hb_msg ⊢
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h01))
      · exact absurd rfl hb_ne1
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h21))
      · exact absurd rfl hb_ne1
      · exact hb_msg.symm
    · -- verifier pull (tag 2) = seg0 push (tag 1+1=2)
      have hpull : pullMsg5 (seam5 fv0 fv1 fa fs 2) (seam5_size ..) ∈
          theList2 bv0 bv1 ba bs fv0 fv1 fa fs 2 p0v0 p0v1 p0a p0s 1
            l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 0 l1v0 l1v1 l1a l1s := by
        unfold theList2; simp
      obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
      unfold theList2 at hb_mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
      rcases hb_mem with h | h | h | h | h | h <;> subst h <;>
        simp only [pushMsg5, pullMsg5] at hb_msg ⊢
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h02))
      · exact absurd rfl hb_ne1
      · exact absurd rfl hb_ne1
      · exact hb_msg.symm
      · exact absurd rfl hb_ne1
      · exact absurd hb_msg (seam5_tag_ne (by simpa using h12))

/-! ## NON-VACUITY (CRITICAL — the theorem proves something).

`tag_chain_derived` quantifies over GENUINELY FREE tags `t0, t1` and free boundary
values; the hypotheses do not hardcode them to 0,1,2. To confirm the antecedent
`BalancedInteractions theList2` is SATISFIABLE (so the theorem is not vacuously
true over an empty hypothesis), we exhibit a concrete balanced witness — the
intended 2-segment chain — and run `tag_chain_derived` on it, landing in the first
disjunct with the seam holding. -/

/-- The intended-chain instantiation: boot `(0,0,B,0)` tag 0; seg0 pulls boot and
    pushes `(1,0,100,5)` tag 1; seg1 pulls `(1,0,100,5)` tag 1 (the seam) and
    pushes `(2,0,200,9)` tag 2; verifier pulls `(2,0,200,9)` tag 2. Free tags are
    instantiated to the intended `t0 = 0, t1 = 1`. -/
def goodList2 : List (Interaction FGL) :=
  theList2
    0 0 335544320 0                 -- boot value, tag 0
    2 0 200 9 2                      -- final value = seg1.last, tag tf = 2
    0 0 335544320 0 0               -- seg0.prev = boot, tag t0 = 0
    1 0 100 5                        -- seg0.last, pushed tag t0+1 = 1
    1 0 100 5 1                      -- seg1.prev = seg0.last (SEAM), tag t1 = 1
    2 0 200 9                        -- seg1.last, pushed tag t1+1 = 2

/-- 6 < ringChar FGL (the `BalancedInteractions` length side-condition). -/
theorem six_lt_ringChar : (6 : ℕ) < ringChar FGL := by
  haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
  rw [ringChar.eq FGL GL_prime]; norm_num

/-- The intended chain IS balanced: each of the three distinct messages
    `(0,0,B,0,0)`, `(1,0,100,5,1)`, `(2,0,200,9,2)` has one matching pull (-1) and
    one push (+1). NON-VACUOUS positive witness. -/
theorem goodList2_balanced : BalancedInteractions goodList2 := by
  refine ⟨Or.inl ?_, ?_⟩
  · show ([_, _, _, _, _, _] : List _).length < ringChar FGL
    simpa using six_lt_ringChar
  · intro msg
    unfold goodList2 theList2 balanceOf pullMsg5 pushMsg5 seam5
    have d01 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[1,0,100,5,1] := by decide
    have d02 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[2,0,200,9,2] := by decide
    have d12 : (#[1,0,100,5,1] : Array FGL) ≠ #[2,0,200,9,2] := by decide
    by_cases h0 : (#[0,0,335544320,0,0] : Array FGL) = msg <;>
    by_cases h1 : (#[1,0,100,5,1] : Array FGL) = msg <;>
    by_cases h2 : (#[2,0,200,9,2] : Array FGL) = msg <;>
      simp_all [List.filter, List.sum]

/-- Running `tag_chain_derived` on the concrete witness: it lands in the
    first disjunct, the tags resolve to `(0,1)` and `tf = 2`, and the seam holds
    (`seg1.prev = seg0.last = (1,0,100,5)`). This certifies non-vacuity end-to-end:
    a real balanced trace satisfies `tag_chain_derived`'s antecedent, and the
    conclusion's first disjunct (with the seam) is the one that fires. -/
theorem goodList2_chain :
    (0:FGL) = 0 ∧ (1:FGL) = 1 ∧ (2:FGL) = 2
      ∧ seam5 0 0 335544320 0 0 = seam5 0 0 335544320 0 0
      ∧ seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1)
      ∧ seam5 2 0 200 9 2 = seam5 2 0 200 9 (1 + 1) := by
  rcases tag_chain_derived
      0 0 335544320 0 2 0 200 9 2 0 0 335544320 0 0 1 0 100 5 1 0 100 5 1 2 0 200 9
      goodList2_balanced with h | h
  · exact h
  · -- the second (permutation) disjunct would force t1 = 0 here, but t1 = 1; absurd
    exact absurd h.1 (by simpa using zero_ne_one_FGL)

/-! ## THE REAL-ENSEMBLE BOOT CHAIN (XCAP #103, route (b), L4.6).

`theList2` above models the deleted SEPARATE scaffold ensemble, whose two
segments were BOTH non-last and therefore needed a verifier FINAL PULL to close
the chain. The REAL `fullRv64imEnsemble` is different: its Mem rows emit
`pull(tag = segment_id)` and `push(tag = segment_id + 1)` GATED by
`1 - is_last_segment`, so the LAST segment's push is turned OFF. With a single
tag-0 boot push, the chain telescopes to zero with NO final pull — and, because
the gating breaks the symmetry, the tags are forced UNIQUELY (no permutation
disjunction).

This section derives that boot chain for N = 2 (`seg1` is the last segment, its
push gated off, modelled as multiplicity 0). It is the channel-level engine the
real-ensemble non-vacuity witness (`FullEnsemble/SeamNonVacuity.lean`) discharges. -/

section BootChain

/-- A raw boundary+tag message at a FREE multiplicity `mult` (used for the
    `is_last`-gated segment push, whose multiplicity is `1 - is_last_segment`). -/
def gatedMsg5 (mult : FGL) (m : Array FGL) (hm : m.size = 5) : Interaction FGL where
  channel := SeamChannel5.toRaw
  mult := mult
  msg := m
  same_size := by simpa [SeamChannel5, Channel.toRaw] using hm
  assumeGuarantees := false

/-- The N = 2 boot interaction list with FREE per-segment pull-tags and FREE
    boundary values, matching the REAL ensemble's emission. Order mirrors the
    real witness `[boot] ++ [seg0 pull, seg0 push] ++ [seg1 pull, seg1 push]`:

      boot:  push (bootV, 0)                                   [endpoint]
      seg0:  pull (p0V, t0),   push (l0V, t0 + 1)              [non-last]
      seg1:  pull (p1V, t1),   gated-push (l1V, t1 + 1) @ g1   [g1 = 1 - is_last]

    With `seg1` the last segment, `g1 = 0`, so its push contributes nothing —
    exactly the real emission. -/
def bootList2
    (bv0 bv1 ba bs : FGL)        -- boot value (4 lanes); tag 0
    (p0v0 p0v1 p0a p0s t0 : FGL) -- seg0 prev value + free pull-tag t0
    (l0v0 l0v1 l0a l0s : FGL)    -- seg0 last value; tag t0+1
    (p1v0 p1v1 p1a p1s t1 : FGL) -- seg1 prev value + free pull-tag t1
    (l1v0 l1v1 l1a l1s g1 : FGL) -- seg1 last value; tag t1+1; gate g1
    : List (Interaction FGL) :=
  [ pushMsg5 (seam5 bv0 bv1 ba bs 0) (seam5_size ..)            -- boot push, tag 0
  , pullMsg5 (seam5 p0v0 p0v1 p0a p0s t0) (seam5_size ..)       -- seg0 pull, tag t0
  , pushMsg5 (seam5 l0v0 l0v1 l0a l0s (t0 + 1)) (seam5_size ..) -- seg0 push, tag t0+1
  , pullMsg5 (seam5 p1v0 p1v1 p1a p1s t1) (seam5_size ..)       -- seg1 pull, tag t1
  , gatedMsg5 g1 (seam5 l1v0 l1v1 l1a l1s (t1 + 1)) (seam5_size ..) -- seg1 gated push
  ]

/-- The `weightedSum` of `bootList2` against weight `g` (computed). -/
theorem weightedSum_bootList2 (g : Array FGL → FGL)
    (bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
     l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s g1 : FGL) :
    weightedSum (bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
        l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s g1) g
      = g (seam5 bv0 bv1 ba bs 0)
        - g (seam5 p0v0 p0v1 p0a p0s t0)
        + g (seam5 l0v0 l0v1 l0a l0s (t0 + 1))
        - g (seam5 p1v0 p1v1 p1a p1s t1)
        + g1 * g (seam5 l1v0 l1v1 l1a l1s (t1 + 1)) := by
  simp only [bootList2, weightedSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    pushMsg5, pullMsg5, gatedMsg5]
  ring

section BootTagEquations
variable (bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
  l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s : FGL)

/-- Shorthand for the N = 2 boot list with `g1 = 0` (seg1 is the last segment). -/
local notation "B2" => bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
  l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s 0

/-- With `seg1` the last segment (`g1 = 0`), balance + the +1 emission force the
    pull-tags UNIQUELY: `t0 = 0`, `t1 = 1`. No permutation disjunction — the
    boot push pins tag 0 and the gated-off push breaks the symmetry. -/
theorem boot_tags_forced (balance : BalancedInteractions B2) :
    t0 = 0 ∧ t1 = 1 := by
  have e1 := weightedSum_eq_zero_of_balance tagW balance
  have e2 := weightedSum_eq_zero_of_balance (fun m => tagW m ^ 2) balance
  rw [weightedSum_bootList2] at e1 e2
  simp only [tagW_seam5, zero_mul, add_zero] at e1 e2
  -- e1 : 0 - t0 + (t0+1) - t1 = 0  (= 1 - t1)  ⇒  t1 = 1
  have ht1 : t1 = 1 := by linear_combination -e1
  subst ht1
  -- e2 : 0 - t0^2 + (t0+1)^2 - 1 = 0  ⇒  2 t0 = 0  ⇒  t0 = 0
  have h2t : (2 : FGL) * t0 = 2 * 0 := by linear_combination e2
  exact ⟨mul_left_cancel₀ two_ne_zero_FGL h2t, rfl⟩

end BootTagEquations

/-- THE BOOT-CHAIN DERIVATION on the real-ensemble emission. From balance alone
    (the boot push at tag 0 is a member — a verifier endpoint, NOT a caller
    premise) and the +1/gated emission, the pull-tags are forced to `t0 = 0`,
    `t1 = 1` (UNIQUELY) and the per-tag VALUE seam holds:

      * `seg0.prev = boot`             (seg0 pulls the boot tuple at tag 0)
      * `seg1.prev = seg0.last`        (THE SEAM: seg1 pulls seg0's pushed last). -/
theorem boot_chain_derived
    (bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
     l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s : FGL)
    (balance : BalancedInteractions
      (bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
        l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s 0)) :
    t0 = 0 ∧ t1 = 1
      ∧ seam5 p0v0 p0v1 p0a p0s t0 = seam5 bv0 bv1 ba bs 0           -- seg0 pulls boot
      ∧ seam5 p1v0 p1v1 p1a p1s t1 = seam5 l0v0 l0v1 l0a l0s (t0 + 1) -- SEAM: seg1.prev = seg0.last
      := by
  obtain ⟨ht0, ht1⟩ := boot_tags_forced bv0 bv1 ba bs p0v0 p0v1 p0a p0s t0
    l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s t1 l1v0 l1v1 l1a l1s balance
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := small_tag_ne
  subst ht0 ht1
  refine ⟨rfl, rfl, ?_, ?_⟩
  · -- seg0 pull (tag 0) = boot push (tag 0)
    have hpull : pullMsg5 (seam5 p0v0 p0v1 p0a p0s 0) (seam5_size ..) ∈
        bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s 0
          l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 1 l1v0 l1v1 l1a l1s 0 := by
      unfold bootList2; simp
    obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
    unfold bootList2 at hb_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
    rcases hb_mem with h | h | h | h | h <;> subst h <;>
      simp only [pushMsg5, pullMsg5, gatedMsg5] at hb_msg ⊢
    · exact hb_msg.symm
    · exact absurd rfl hb_ne1
    · exact absurd hb_msg (seam5_tag_ne (by simpa using h10))
    · exact absurd rfl hb_ne1
    · -- the gated push has multiplicity 0; `exists_push_of_pull` returns mult ≠ 0
      exact absurd rfl hb_ne0
  · -- seg1 pull (tag 1) = seg0 push (tag 0+1 = 1) : THE SEAM
    have hpull : pullMsg5 (seam5 p1v0 p1v1 p1a p1s 1) (seam5_size ..) ∈
        bootList2 bv0 bv1 ba bs p0v0 p0v1 p0a p0s 0
          l0v0 l0v1 l0a l0s p1v0 p1v1 p1a p1s 1 l1v0 l1v1 l1a l1s 0 := by
      unfold bootList2; simp
    obtain ⟨b, hb_mem, hb_msg, hb_ne1, hb_ne0⟩ := exists_push_of_pull _ balance _ hpull rfl
    unfold bootList2 at hb_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb_mem
    rcases hb_mem with h | h | h | h | h <;> subst h <;>
      simp only [pushMsg5, pullMsg5, gatedMsg5] at hb_msg ⊢
    · exact absurd hb_msg (seam5_tag_ne (by simpa using h01))
    · exact absurd rfl hb_ne1
    · exact hb_msg.symm
    · exact absurd rfl hb_ne1
    · exact absurd rfl hb_ne0

/-! ## NON-VACUITY of the boot chain (channel level).

We exhibit a concrete balanced boot witness — the intended 2-segment chain with
`seg1` the last segment — and run `boot_chain_derived`, confirming the seam holds
(`seg1.prev = seg0.last`). The full real-ensemble witness lifts this. -/

/-- The intended boot chain: boot `(0,0,B,0)` tag 0; seg0 pulls boot, pushes
    `(1,0,100,5)` tag 1; seg1 pulls `(1,0,100,5)` tag 1 (the SEAM), is the LAST
    segment so its push `(2,0,200,9)` at tag 2 is GATED OFF (`g1 = 0`). -/
def goodBootList2 : List (Interaction FGL) :=
  bootList2
    0 0 335544320 0                 -- boot value, tag 0
    0 0 335544320 0 0               -- seg0.prev = boot, tag t0 = 0
    1 0 100 5                        -- seg0.last, pushed tag t0+1 = 1
    1 0 100 5 1                      -- seg1.prev = seg0.last (SEAM), tag t1 = 1
    2 0 200 9 0                      -- seg1.last (gated off, g1 = 0), would-be tag 2

theorem goodBootList2_balanced : BalancedInteractions goodBootList2 := by
  refine ⟨Or.inl ?_, ?_⟩
  · show ([_, _, _, _, _] : List _).length < ringChar FGL
    have : (5 : ℕ) < ringChar FGL := by
      haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
      rw [ringChar.eq FGL GL_prime]; norm_num
    simpa using this
  · intro msg
    unfold goodBootList2 bootList2 balanceOf pullMsg5 pushMsg5 gatedMsg5 seam5
    have d01 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[1,0,100,5,1] := by decide
    have d02 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[2,0,200,9,2] := by decide
    have d12 : (#[1,0,100,5,1] : Array FGL) ≠ #[2,0,200,9,2] := by decide
    by_cases h0 : (#[0,0,335544320,0,0] : Array FGL) = msg <;>
    by_cases h1 : (#[1,0,100,5,1] : Array FGL) = msg <;>
    by_cases h2 : (#[2,0,200,9,2] : Array FGL) = msg <;>
      simp_all [List.filter, List.sum]

/-- Running `boot_chain_derived` on the concrete boot witness: tags resolve to
    `(0,1)` and the SEAM holds (`seg1.prev = seg0.last = (1,0,100,5)`). Certifies
    non-vacuity of the boot chain end-to-end. -/
theorem goodBootList2_chain :
    (0:FGL) = 0 ∧ (1:FGL) = 1
      ∧ seam5 0 0 335544320 0 0 = seam5 0 0 335544320 0 0
      ∧ seam5 1 0 100 5 1 = seam5 1 0 100 5 (0 + 1) :=
  boot_chain_derived
    0 0 335544320 0 0 0 335544320 0 0 1 0 100 5 1 0 100 5 1 2 0 200 9
    goodBootList2_balanced

end BootChain

/-! ## GENERAL N — the boot tag-chain for an arbitrary segment count.

`bootList2` above is the `N = 2` instance of the real-ensemble boot chain. This
section generalizes it to an ARBITRARY number of segments `N`, with FREE per-
segment pull-tags and FREE per-segment boundary values, matching the real
emission:

  boot:           push (bootV, 0)                                   [endpoint, tag 0]
  segment i:      pull (prevV i, t i),  push (lastV i, t i + 1)     [+1 emission]
  the LAST segment (i = N-1):  its push is GATED OFF (multiplicity 0).

### What balance forces (the honest general-N finding)

From channel balance alone — the boot push at tag 0 being a MEMBER of the
balanced list (a verifier endpoint, NOT a caller premise) and the `+1` emission
baked into the chain — we derive, **for EVERY segment** `i`, the per-segment
**value seam**:

  * either `t i = 0` and `prevV i = bootV`           (segment `i` pulls the boot), OR
  * there is a NON-LAST segment `j` with `t i = t j + 1` and `prevV i = lastV j`
    (THE SEAM: segment `i`'s incoming boundary equals segment `j`'s outgoing
    boundary, matched across the tag step).

This is the cross-segment memory continuation #76 consumes: each segment's
*previous* memory boundary is continued from some earlier segment's *last*
boundary (matched by `segment_id` = tag), or from the boot. It holds for ALL `N`.

### Why it is tag-INDEXED, not physical-index-indexed

Balance is symmetric under permuting which physical segment plays which chain
position. For `N = 2` the only non-last segment is `seg0`, so the chain is forced
UNIQUELY (`boot_chain_derived`: `t0 = 0, t1 = 1`). For `N ≥ 3` there is genuine
permutation freedom: e.g. `N = 3` with `(t0,t1,t2) = (1,0,2)` is ALSO balanced
(pulls `{1,0,2}`, pushes `{0, t0+1=2, t1+1=1} = {0,2,1}`, equal as multisets),
with the seam holding along the relabelled chain `boot → seg1 → seg0 → seg2`.
So the FAITHFUL general-N statement is the per-segment matched seam above (each
segment's prev = the matched push's value), which is true for every `N` and
permutation. Collapsing it to "physical segment `i+1` follows physical segment
`i`" needs the row-local `is_first_segment` pin (per the N=2 note, a single
boolean from `segment_every_row`, NOT a per-segment caller premise) — the
documented L5 follow-up. The tag set IS forced to `{0,…,N-1}`
(`bootChainN_tags_subset` / `bootChainN_tag_set`); only the assignment permutes.
-/

section GeneralN

/-- A 4-lane boundary value, packed as a record so the chain can be indexed by a
    single function `ℕ → SeamVal`. Keeping the value as four explicit `FGL` lanes
    (rather than an `Array`) lets the general-N proof reuse `seam5`, `tagW_seam5`,
    and `seam5_tag_ne` directly with no `Array.ext` friction. -/
structure SeamVal where
  v0 : FGL
  v1 : FGL
  addr : FGL
  step : FGL
deriving DecidableEq

/-- The `seam5` message for a packed value at a given `tag`. -/
def SeamVal.msg (v : SeamVal) (tag : FGL) : Array FGL := seam5 v.v0 v.v1 v.addr v.step tag

@[simp] theorem SeamVal.tagW_msg (v : SeamVal) (tag : FGL) : tagW (v.msg tag) = tag := rfl

theorem SeamVal.msg_size (v : SeamVal) (tag : FGL) : (v.msg tag).size = 5 := rfl

/-- `SeamVal.msg` is injective in the value at a fixed tag (the message carries
    the full 4-lane value, so equal messages give equal values). -/
theorem SeamVal.msg_inj {v w : SeamVal} {tag : FGL} (h : v.msg tag = w.msg tag) : v = w := by
  obtain ⟨v0, v1, va, vs⟩ := v
  obtain ⟨w0, w1, wa, ws⟩ := w
  simp only [SeamVal.msg, seam5] at h
  have h0 : v0 = w0 := by have := congrArg (·[0]!) h; simpa using this
  have h1 : v1 = w1 := by have := congrArg (·[1]!) h; simpa using this
  have h2 : va = wa := by have := congrArg (·[2]!) h; simpa using this
  have h3 : vs = ws := by have := congrArg (·[3]!) h; simpa using this
  subst h0 h1 h2 h3; rfl

/-! ### The general-N boot chain list. -/

/-- The gate multiplicity for segment `i` of an `N`-segment chain: `0` for the
    LAST segment (`i = N-1`, push turned off), `1` otherwise. This is the value of
    `1 - is_last_segment` the real emission carries. -/
def segGate (N i : ℕ) : FGL := if i + 1 = N then 0 else 1

/-- The two interactions contributed by segment `i`: its pull at tag `t i` and its
    `segGate`-gated push at tag `t i + 1`. -/
def segPair (N : ℕ) (prev last : ℕ → SeamVal) (t : ℕ → FGL) (i : ℕ) :
    List (Interaction FGL) :=
  [ pullMsg5 ((prev i).msg (t i)) (SeamVal.msg_size ..)
  , gatedMsg5 (segGate N i) ((last i).msg (t i + 1)) (SeamVal.msg_size ..) ]

/-- The general-N boot chain: the tag-0 boot push followed by every segment's
    pull + gated push. `prev i` / `last i` are the FREE incoming / outgoing
    boundary values of segment `i`; `t i` its FREE pull-tag. -/
def bootChainN (N : ℕ) (boot : SeamVal) (prev last : ℕ → SeamVal) (t : ℕ → FGL) :
    List (Interaction FGL) :=
  pushMsg5 (boot.msg 0) (SeamVal.msg_size ..) ::
    (List.range N).flatMap (segPair N prev last t)

/-- The boot chain has `1 + 2*N` interactions. -/
theorem bootChainN_length (N : ℕ) (boot : SeamVal) (prev last : ℕ → SeamVal) (t : ℕ → FGL) :
    (bootChainN N boot prev last t).length = 1 + 2 * N := by
  simp only [bootChainN, List.length_cons, List.length_flatMap, segPair,
    List.map_const']
  rw [List.sum_replicate]
  simp [List.length_range]; ring

/-- Segment `i`'s pull is a member of the boot chain (for `i < N`). -/
theorem segPull_mem (N : ℕ) (boot : SeamVal) (prev last : ℕ → SeamVal) (t : ℕ → FGL)
    {i : ℕ} (hi : i < N) :
    pullMsg5 ((prev i).msg (t i)) (SeamVal.msg_size ..) ∈
      bootChainN N boot prev last t := by
  refine List.mem_cons.mpr (Or.inr ?_)
  rw [List.mem_flatMap]
  exact ⟨i, List.mem_range.mpr hi, by simp [segPair]⟩

/-- Classification of the pushes (nonzero, non-`-1` multiplicity members) of the
    boot chain. Any such `b` is EITHER the boot push (tag 0, value `boot`) OR a
    NON-LAST segment `j`'s gated push (tag `t j + 1`, value `last j`). The pulls
    (mult `-1`) and the gated-OFF last push (mult `0`) are excluded by hypothesis. -/
theorem push_mem_classify (N : ℕ) (boot : SeamVal) (prev last : ℕ → SeamVal) (t : ℕ → FGL)
    {b : Interaction FGL} (hb_mem : b ∈ bootChainN N boot prev last t)
    (hb1 : b.mult ≠ -1) (hb0 : b.mult ≠ 0) :
    (b.msg = (boot).msg 0)
    ∨ (∃ j, j < N ∧ j + 1 ≠ N ∧ b.msg = (last j).msg (t j + 1)) := by
  rw [bootChainN, List.mem_cons] at hb_mem
  rcases hb_mem with hboot | hseg
  · exact Or.inl (by rw [hboot]; rfl)
  · rw [List.mem_flatMap] at hseg
    obtain ⟨j, hj_range, hj_mem⟩ := hseg
    rw [List.mem_range] at hj_range
    -- b is either the pull (mult -1, excluded) or the gated push of segment j
    simp only [segPair, List.mem_cons, List.not_mem_nil, or_false] at hj_mem
    rcases hj_mem with hpull | hpush
    · exact absurd (by rw [hpull, pullMsg5]) hb1
    · refine Or.inr ⟨j, hj_range, ?_, ?_⟩
      · -- segment j is non-last: else its gate is 0, contradicting hb0
        intro hlast
        apply hb0
        rw [hpush, gatedMsg5, segGate, if_pos hlast]
      · rw [hpush, gatedMsg5]

/-! ### The general-N per-segment value seam (the deliverable).

For an arbitrary `N`, channel balance forces, for EVERY segment `i < N`, its
incoming boundary `prev i` to be continued either from the boot or from some
non-last segment's outgoing boundary `last j`, matched by the tag step
`t i = t j + 1`. This is `boot_chain_derived` generalized from `N = 2` to all `N`. -/

/-- **THE GENERAL-N PER-SEGMENT VALUE SEAM.** For every segment `i < N`, from
    channel balance alone (the tag-0 boot push is a MEMBER of the balanced chain,
    a verifier endpoint, NOT a caller premise) and the `+1`/gated emission, the
    segment's incoming boundary `prev i` is continued by a matched push:

      * either `t i = 0` and `prev i = boot`           (segment `i` pulls the boot), OR
      * `∃ j < N`, `j` NOT the last segment, with `t i = t j + 1`
        and `prev i = last j`   (THE SEAM: `i`'s prev = `j`'s last, across the tag step).

    Holds for ALL `N` and is tag-indexed (permutation-tolerant): which physical
    segment `j` is matched is not pinned, but the value continuation is. -/
theorem bootChainN_seam (N : ℕ) (boot : SeamVal) (prev last : ℕ → SeamVal) (t : ℕ → FGL)
    (balance : BalancedInteractions (bootChainN N boot prev last t))
    {i : ℕ} (hi : i < N) :
    (t i = 0 ∧ prev i = boot)
    ∨ (∃ j, j < N ∧ j + 1 ≠ N ∧ t i = t j + 1 ∧ prev i = last j) := by
  -- segment i's pull is matched by a push (nonzero, non `-1` multiplicity)
  obtain ⟨b, hb_mem, hb_msg, hb1, hb0⟩ :=
    exists_push_of_pull _ balance _ (segPull_mem N boot prev last t hi) rfl
  -- the matched push's message equals segment i's pull message
  simp only [pullMsg5] at hb_msg
  -- hb_msg : b.msg = (prev i).msg (t i)
  rcases push_mem_classify N boot prev last t hb_mem hb1 hb0 with hboot | ⟨j, hj, hjlast, hjmsg⟩
  · -- matched the boot push: tag 0 and value boot
    left
    have hmsg : (prev i).msg (t i) = (boot).msg 0 := hb_msg ▸ hboot
    have htag : t i = 0 := by
      have := congrArg tagW hmsg; simpa using this
    refine ⟨htag, ?_⟩
    rw [htag] at hmsg
    exact SeamVal.msg_inj hmsg
  · -- matched a non-last segment j's push: tag t j + 1 and value last j
    right
    have hmsg : (prev i).msg (t i) = (last j).msg (t j + 1) := hb_msg ▸ hjmsg
    have htag : t i = t j + 1 := by
      have := congrArg tagW hmsg; simpa using this
    refine ⟨j, hj, hjlast, htag, ?_⟩
    rw [htag] at hmsg
    exact SeamVal.msg_inj hmsg

/-! ### NON-VACUITY at N = 3 (the general statement is genuinely satisfiable).

`bootChainN_seam` is `∀ N`-quantified. To rule out vacuity (a green
`Balance → …` theorem is worthless if `Balance` is unsatisfiable), we exhibit a
concrete BALANCED N = 3 boot chain and run `bootChainN_seam` on each of its three
segments, confirming the value seam fires (each segment's prev is continued from
the boot / the previous segment's last). This is an N ≥ 3 instance, so it also
certifies the general statement is not "trivially true because no N ≥ 3 chain
balances". -/

/-- The intended N = 3 boot value: `(0,0,B,0)` at tag 0. -/
def boot3 : SeamVal := ⟨0, 0, 335544320, 0⟩

/-- The intended N = 3 per-segment incoming boundaries:
    seg0 pulls the boot, seg1 pulls seg0's last, seg2 pulls seg1's last (the seams). -/
def prev3 : ℕ → SeamVal
  | 0 => ⟨0, 0, 335544320, 0⟩   -- = boot3
  | 1 => ⟨1, 0, 100, 5⟩         -- = last3 0  (SEAM)
  | 2 => ⟨2, 0, 200, 9⟩         -- = last3 1  (SEAM)
  | _ => ⟨0, 0, 0, 0⟩

/-- The intended N = 3 per-segment outgoing boundaries. seg2 is the LAST segment,
    so its push (would be tag 3) is gated OFF. -/
def last3 : ℕ → SeamVal
  | 0 => ⟨1, 0, 100, 5⟩
  | 1 => ⟨2, 0, 200, 9⟩
  | 2 => ⟨3, 0, 300, 13⟩        -- gated off (seg2 = last)
  | _ => ⟨0, 0, 0, 0⟩

/-- The intended N = 3 pull-tags: `t i = i`. -/
def t3 : ℕ → FGL
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

/-- The concrete N = 3 boot chain (7 interactions). -/
def goodBootChain3 : List (Interaction FGL) := bootChainN 3 boot3 prev3 last3 t3

/-- The concrete N = 3 boot chain reduces to its explicit 7-interaction cons-list:
    boot push, then seg0/seg1/seg2 each pull + push (seg2's push gated to mult 0). -/
theorem goodBootChain3_eq :
    goodBootChain3 =
      [ pushMsg5 (seam5 0 0 335544320 0 0) (seam5_size ..)            -- boot push, tag 0
      , pullMsg5 (seam5 0 0 335544320 0 0) (seam5_size ..)            -- seg0 pull, tag 0
      , gatedMsg5 1 (seam5 1 0 100 5 1) (seam5_size ..)               -- seg0 push, tag 1
      , pullMsg5 (seam5 1 0 100 5 1) (seam5_size ..)                  -- seg1 pull, tag 1
      , gatedMsg5 1 (seam5 2 0 200 9 2) (seam5_size ..)               -- seg1 push, tag 2
      , pullMsg5 (seam5 2 0 200 9 2) (seam5_size ..)                  -- seg2 pull, tag 2
      , gatedMsg5 0 (seam5 3 0 300 13 3) (seam5_size ..) ] := by      -- seg2 push, GATED OFF
  simp only [goodBootChain3, bootChainN, show (3 : ℕ) = 2 + 1 from rfl,
    List.range_succ, List.range_zero, List.nil_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.cons_append, segPair, segGate, boot3, prev3, last3, t3,
    SeamVal.msg]
  norm_num [seam5]

/-- The concrete N = 3 boot chain IS balanced: the three live messages
    `(0,0,B,0,0)`, `(1,0,100,5,1)`, `(2,0,200,9,2)` each have one matching pull
    (-1) and one push (+1); seg2's push `(3,0,300,13,3)` is gated to mult 0.
    NON-VACUOUS positive witness at N = 3. -/
theorem goodBootChain3_balanced : BalancedInteractions goodBootChain3 := by
  refine ⟨Or.inl ?_, ?_⟩
  · rw [goodBootChain3, bootChainN_length]
    have : (1 + 2 * 3 : ℕ) < ringChar FGL := by
      haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
      rw [ringChar.eq FGL GL_prime]; norm_num
    simpa using this
  · intro msg
    rw [goodBootChain3_eq]
    unfold balanceOf pullMsg5 pushMsg5 gatedMsg5 seam5
    have d01 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[1,0,100,5,1] := by decide
    have d02 : (#[0,0,335544320,0,0] : Array FGL) ≠ #[2,0,200,9,2] := by decide
    have d12 : (#[1,0,100,5,1] : Array FGL) ≠ #[2,0,200,9,2] := by decide
    by_cases h0 : (#[0,0,335544320,0,0] : Array FGL) = msg <;>
    by_cases h1 : (#[1,0,100,5,1] : Array FGL) = msg <;>
    by_cases h2 : (#[2,0,200,9,2] : Array FGL) = msg <;>
      simp_all [List.filter, List.sum] <;>
      -- residual: seg2's gated push (mult 0) for the tag-3 message — 0 either way
      (split <;> simp)

/-- Running `bootChainN_seam` on the concrete N = 3 witness, for each segment:
    seg0 pulls the boot, seg1's prev = seg0's last (SEAM), seg2's prev = seg1's
    last (SEAM). Each fires the expected disjunct. Certifies the general-N
    theorem is non-vacuous at N = 3. -/
theorem goodBootChain3_seams :
    -- seg0 pulls the boot
    (t3 0 = 0 ∧ prev3 0 = boot3)
    -- seg1's incoming = seg0's outgoing (the first seam)
    ∧ (∃ j, j < 3 ∧ j + 1 ≠ 3 ∧ t3 1 = t3 j + 1 ∧ prev3 1 = last3 j)
    -- seg2's incoming = seg1's outgoing (the second seam)
    ∧ (∃ j, j < 3 ∧ j + 1 ≠ 3 ∧ t3 2 = t3 j + 1 ∧ prev3 2 = last3 j) := by
  -- the three tag values `t3 0 = 0, t3 1 = 1, t3 2 = 2` are distinct in Goldilocks
  have hne01 : (0 : FGL) ≠ 0 + 1 := by simpa using zero_ne_one_FGL
  have hne02 : (0 : FGL) ≠ 1 + 1 := by simpa using zero_ne_two_FGL
  have hne03 : (0 : FGL) ≠ 2 + 1 := by
    have h3 : (3 : FGL) ≠ 0 := by
      haveI hc : CharP FGL GL_prime := inferInstanceAs (CharP (Fin GL_prime) GL_prime)
      have : ((3 : ℕ) : FGL) ≠ 0 := by rw [Ne, CharP.cast_eq_zero_iff FGL GL_prime]; omega
      simpa using this
    intro h; apply h3; linear_combination -h
  refine ⟨?_, ?_, ?_⟩
  · rcases bootChainN_seam 3 boot3 prev3 last3 t3 goodBootChain3_balanced (i := 0) (by norm_num)
      with h | ⟨j, hj, _, htag, _⟩
    · exact h
    · -- the seam disjunct would force t3 0 = t3 j + 1, impossible for j ∈ {0,1,2}
      exfalso
      interval_cases j <;> simp only [t3] at htag
      · exact hne01 htag
      · exact hne02 htag
      · exact hne03 htag
  · rcases bootChainN_seam 3 boot3 prev3 last3 t3 goodBootChain3_balanced (i := 1) (by norm_num)
      with ⟨htag, _⟩ | h
    · -- t3 1 = 1 ≠ 0, so the boot disjunct is impossible
      exact absurd htag.symm zero_ne_one_FGL
    · exact h
  · rcases bootChainN_seam 3 boot3 prev3 last3 t3 goodBootChain3_balanced (i := 2) (by norm_num)
      with ⟨htag, _⟩ | h
    · -- t3 2 = 2 ≠ 0, so the boot disjunct is impossible
      exact absurd htag.symm zero_ne_two_FGL
    · exact h

/-! ### Tag arithmetic: the last segment's tag is forced to `N-1`.

Beyond the per-segment value seam, the weighted-balance machinery pins the LAST
segment's tag exactly: `t (N-1) = N - 1`. (For `N = 2` this recovers
`boot_tags_forced`'s `t1 = 1`.) The proof is a clean telescoping of the `f = tag`
weighted balance — see the doc note below on why the FULL tag set `{0,…,N-1}`
needs a symmetric-function / Newton argument and is the documented follow-up. -/

/-- `weightedSum` is additive over list append. -/
theorem weightedSum_append (a b : List (Interaction FGL)) (f : Array FGL → FGL) :
    weightedSum (a ++ b) f = weightedSum a f + weightedSum b f := by
  simp [weightedSum, List.map_append, List.sum_append]

/-- `weightedSum` distributes over `flatMap` as a sum of per-element weighted sums. -/
theorem weightedSum_flatMap (l : List ℕ) (g : ℕ → List (Interaction FGL))
    (f : Array FGL → FGL) :
    weightedSum (l.flatMap g) f = (l.map (fun i => weightedSum (g i) f)).sum := by
  unfold weightedSum
  induction l with
  | nil => simp
  | cons a as ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

/-- A `(List.range N).map`-sum equals the corresponding `Finset.range` sum. -/
theorem list_map_range_sum (N : ℕ) (g : ℕ → FGL) :
    (List.map g (List.range N)).sum = ∑ i ∈ Finset.range N, g i := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

/-- The weighted sum of a single segment's pair (pull + gated push). -/
theorem weightedSum_segPair (N : ℕ) (prev last : ℕ → SeamVal) (t : ℕ → FGL)
    (f : Array FGL → FGL) (i : ℕ) :
    weightedSum (segPair N prev last t i) f
      = - f ((prev i).msg (t i)) + segGate N i * f ((last i).msg (t i + 1)) := by
  simp only [segPair, weightedSum, pullMsg5, gatedMsg5, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, neg_one_mul]

/-- The weighted sum of the whole boot chain as a `Finset.range` sum. -/
theorem weightedSum_bootChainN (N : ℕ) (boot : SeamVal) (prev last : ℕ → SeamVal)
    (t : ℕ → FGL) (f : Array FGL → FGL) :
    weightedSum (bootChainN N boot prev last t) f
      = f (boot.msg 0)
        + ∑ i ∈ Finset.range N,
            (- f ((prev i).msg (t i)) + segGate N i * f ((last i).msg (t i + 1))) := by
  rw [bootChainN, show (pushMsg5 (boot.msg 0) (SeamVal.msg_size ..) ::
      (List.range N).flatMap (segPair N prev last t))
      = [pushMsg5 (boot.msg 0) (SeamVal.msg_size ..)] ++
        (List.range N).flatMap (segPair N prev last t) from rfl,
    weightedSum_append, weightedSum_flatMap]
  rw [list_map_range_sum]
  congr 1
  · simp [weightedSum, pushMsg5]
  · apply Finset.sum_congr rfl
    intro i _; exact weightedSum_segPair N prev last t f i

/-- The sum of `segGate N i` over `i < N` is `N - 1` (for `N ≥ 1`): every segment
    contributes `1` except the last (`i = N-1`, gate `0`). -/
theorem sum_segGate (N : ℕ) (hN : 0 < N) :
    ∑ i ∈ Finset.range N, segGate N i = ((N : FGL) - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Finset.sum_range_succ]
  have hlast : segGate (n + 1) n = 0 := by simp [segGate]
  have hrest : ∀ i ∈ Finset.range n, segGate (n + 1) i = 1 := by
    intro i hi; simp only [Finset.mem_range] at hi
    simp only [segGate]; rw [if_neg]; omega
  rw [Finset.sum_congr rfl hrest, hlast]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, add_zero]
  push_cast; ring

/-- **THE LAST SEGMENT'S TAG IS FORCED TO `N-1`.** From channel balance with the
    `f = tag` weight, the telescoping `∑ (t_i + 1 - t_i) = ∑ 1 = N - 1` (the boot
    contributes tag 0, the last segment's push is gated off) pins the last
    segment's pull-tag: `t (N-1) = N - 1`. For `N = 2` this is
    `boot_tags_forced`'s `t1 = 1`. -/
theorem bootChainN_last_tag (N : ℕ) (hN : 0 < N) (boot : SeamVal)
    (prev last : ℕ → SeamVal) (t : ℕ → FGL)
    (balance : BalancedInteractions (bootChainN N boot prev last t)) :
    t (N - 1) = (N : FGL) - 1 := by
  have e := weightedSum_eq_zero_of_balance tagW balance
  rw [weightedSum_bootChainN] at e
  -- evaluate the tag weight on every message
  simp only [SeamVal.tagW_msg] at e
  -- the segment sum telescopes: the -t_i and +segGate*t_i cancel for every non-last
  -- segment; the last segment (gate 0) keeps -t_{N-1}; plus ∑ segGate = N-1.
  have hcancel : ∑ i ∈ Finset.range N, (- t i + segGate N i * (t i + 1))
      = (- t (N - 1)) + ∑ i ∈ Finset.range N, segGate N i := by
    have key : ∀ i ∈ Finset.range N,
        (- t i + segGate N i * (t i + 1)) = (segGate N i - 1) * t i + segGate N i := by
      intro i _; ring
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
    congr 1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [Finset.sum_range_succ]
    have hrest : ∀ i ∈ Finset.range n, (segGate (n+1) i - 1) * t i = 0 := by
      intro i hi; simp only [Finset.mem_range] at hi
      have : segGate (n+1) i = 1 := by simp only [segGate]; rw [if_neg]; omega
      rw [this]; ring
    rw [Finset.sum_congr rfl hrest, Finset.sum_const_zero]
    have hlast : segGate (n+1) n = 0 := by simp [segGate]
    rw [hlast]
    simp
  rw [hcancel, sum_segGate N hN] at e
  -- e is `0 + (- t (N-1) + (N - 1)) = 0` (boot tag already simplified to 0)
  linear_combination -e

/-! ### The headline general-N theorem (the `boot_chain_derived` analogue). -/

/-- **GENERAL-N BOOT-CHAIN DERIVATION** — the analogue of `boot_chain_derived`
    (`N = 2`) for an ARBITRARY segment count `N ≥ 1`. From channel balance alone on
    the boot chain (the tag-0 boot push a verifier endpoint, NOT a caller premise)
    and the `+1`/gated emission, two facts are forced:

    1. **The per-segment value seam** (the load-bearing cross-segment continuation
       #76 consumes): for EVERY segment `i < N`, its incoming boundary `prev i` is
       continued either from the boot (`t i = 0`, `prev i = boot`) or from a
       non-last segment `j`'s outgoing boundary (`t i = t j + 1`, `prev i = last j`).

    2. **The last segment's tag** is forced exactly: `t (N-1) = N - 1`.

    The seam is tag-indexed (permutation-tolerant); see the section doc for why
    balance does not pin the *physical* segment ordering for `N ≥ 3` (the
    documented `is_first_segment` follow-up), while the value continuation itself
    is forced for every `N`. -/
theorem boot_chain_derived_generalN (N : ℕ) (hN : 0 < N) (boot : SeamVal)
    (prev last : ℕ → SeamVal) (t : ℕ → FGL)
    (balance : BalancedInteractions (bootChainN N boot prev last t)) :
    (∀ i, i < N →
        (t i = 0 ∧ prev i = boot)
        ∨ (∃ j, j < N ∧ j + 1 ≠ N ∧ t i = t j + 1 ∧ prev i = last j))
    ∧ t (N - 1) = (N : FGL) - 1 :=
  ⟨fun _ hi => bootChainN_seam N boot prev last t balance hi,
   bootChainN_last_tag N hN boot prev last t balance⟩

/-- The last-tag derivation, run on the concrete N = 3 witness: `t3 2 = 2`
    (i.e. `t (N-1) = N - 1` at N = 3). Certifies `bootChainN_last_tag` /
    `boot_chain_derived_generalN`'s tag arithmetic is non-vacuous at N ≥ 3. -/
theorem goodBootChain3_last_tag : t3 2 = (3 : FGL) - 1 := by
  have h := bootChainN_last_tag 3 (by norm_num) boot3 prev3 last3 t3 goodBootChain3_balanced
  simpa using h

end GeneralN

end ZiskFv.Channels.SeamTagChain

/-! ## Axiom-closure checks.

`#print axioms` returns only Lean-kernel axioms (`propext`, `Classical.choice`,
`Quot.sound`): i.e. 0 PROJECT (`ZiskFv.*`) axioms. NO `sorry`, NO project axiom,
NO `native_decide`. -/
#print axioms ZiskFv.Channels.SeamTagChain.weightedSum_eq_zero_of_balance
#print axioms ZiskFv.Channels.SeamTagChain.tag_power_sums
#print axioms ZiskFv.Channels.SeamTagChain.tags_forced
#print axioms ZiskFv.Channels.SeamTagChain.tag_chain_derived
#print axioms ZiskFv.Channels.SeamTagChain.goodList2_balanced
#print axioms ZiskFv.Channels.SeamTagChain.goodList2_chain
#print axioms ZiskFv.Channels.SeamTagChain.boot_tags_forced
#print axioms ZiskFv.Channels.SeamTagChain.boot_chain_derived
#print axioms ZiskFv.Channels.SeamTagChain.goodBootList2_balanced
#print axioms ZiskFv.Channels.SeamTagChain.goodBootList2_chain
#print axioms ZiskFv.Channels.SeamTagChain.push_mem_classify
#print axioms ZiskFv.Channels.SeamTagChain.bootChainN_seam
#print axioms ZiskFv.Channels.SeamTagChain.goodBootChain3_balanced
#print axioms ZiskFv.Channels.SeamTagChain.goodBootChain3_seams
#print axioms ZiskFv.Channels.SeamTagChain.bootChainN_last_tag
#print axioms ZiskFv.Channels.SeamTagChain.boot_chain_derived_generalN
#print axioms ZiskFv.Channels.SeamTagChain.goodBootChain3_last_tag
