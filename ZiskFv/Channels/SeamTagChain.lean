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
