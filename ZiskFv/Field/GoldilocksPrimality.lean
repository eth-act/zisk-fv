import Mathlib
import Mathlib.Tactic.NormNum.Prime

/-!
# Pratt primality certificates

A self-contained certificate checker for primality based on Lucas's converse of
Fermat's little theorem (mathlib's `lucas_primality`). Given a number `p`, a
base `a`, and a complete factorisation `p - 1 = ∏ qᵢ^eᵢ` together with
recursive Pratt certificates for each `qᵢ`, the verifier checks

* `a^(p-1) ≡ 1 (mod p)`
* `a^((p-1)/qᵢ) ≢ 1 (mod p)` for every `qᵢ`

and certifies that `p` is prime.

This is used to prove `Nat.Prime 18446744069414584321` (Goldilocks) by
normalizing a concrete certificate, avoiding a large direct primality
decision on `p`.
-/

namespace ZiskFv

/-- Fast modular exponentiation: `powMod a n p = a^n % p`, computed by
square-and-multiply with intermediate reduction so values stay small. -/
def powMod (a : ℕ) : ℕ → ℕ → ℕ
  | 0, p => 1 % p
  | n + 1, p =>
      let half := powMod a ((n + 1) / 2) p
      let sq := (half * half) % p
      if (n + 1) % 2 = 0 then sq else (sq * a) % p
termination_by n _ => n
decreasing_by
  · simp_wf; omega

/-- `powMod` equals the naive `a^n % p`. -/
lemma powMod_eq (a : ℕ) : ∀ n p : ℕ, powMod a n p = a ^ n % p
  | 0, p => by simp [powMod]
  | n + 1, p => by
      unfold powMod
      simp only
      have ih := powMod_eq a ((n + 1) / 2) p
      rw [ih]
      set k := (n + 1) / 2 with hk_def
      have hsq :
          a ^ k % p * (a ^ k % p) % p = a ^ (2 * k) % p := by
        rw [two_mul, pow_add, ← Nat.mul_mod]
      split_ifs with h
      · -- (n+1) even.
        have hdiv : 2 * k = n + 1 := by
          have : (n + 1) % 2 = 0 := h
          omega
        rw [hsq, hdiv]
      · -- (n+1) odd.
        have hdiv : 2 * k + 1 = n + 1 := by
          have : (n + 1) % 2 = 1 := by omega
          omega
        calc a ^ k % p * (a ^ k % p) % p * a % p
            = a ^ (2 * k) % p * a % p := by rw [hsq]
          _ = a ^ (2 * k) * a % p := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
          _ = a ^ (2 * k + 1) % p := by rw [pow_succ]
          _ = a ^ (n + 1) % p := by rw [hdiv]

/-- A Pratt primality certificate for a natural number.

Two constructors:

* `small p` — defers to mathlib's `Nat.decidablePrime`; in the concrete
  Goldilocks certificate these are the small primes 2, 3, 5, 17, 257, 65537.
* `step p a factors` — the recursive Lucas certificate:
  `factors = [(q₁, e₁, c₁), …, (qₖ, eₖ, cₖ)]`, with each `cᵢ : Pratt` a
  sub-certificate whose top-level prime equals `qᵢ`. -/
inductive Pratt where
  | small (p : ℕ) : Pratt
  | step (p a : ℕ) (factors : List (ℕ × ℕ × Pratt)) : Pratt
  deriving Repr

namespace Pratt

/-- The prime candidate a certificate is claiming. -/
def prime : Pratt → ℕ
  | .small p => p
  | .step p _ _ => p

/-- Boolean verifier. Returns `true` iff the certificate is valid. Recurses
into each sub-certificate, so sub-primes are themselves certified. -/
def verify : Pratt → Bool
  | .small p => decide (Nat.Prime p)
  | .step p a factors =>
      p > 1 &&
      -- Every listed exponent is positive.
      factors.attach.all (fun ⟨⟨_, e, _⟩, _⟩ => decide (e ≥ 1)) &&
      -- Every sub-certificate's top-level prime matches and verifies.
      factors.attach.all (fun ⟨⟨q, _, sub⟩, _⟩ => decide (sub.prime = q) && verify sub) &&
      -- The listed primes multiply to `p - 1`.
      decide ((factors.map (fun ⟨q, e, _⟩ => q ^ e)).prod = p - 1) &&
      -- Fermat: `a^(p-1) ≡ 1 (mod p)`.
      decide (powMod a (p - 1) p = 1 % p) &&
      -- Lucas: for every `qᵢ`, `a^((p-1)/qᵢ) ≢ 1 (mod p)`.
      factors.all (fun ⟨q, _, _⟩ => decide (powMod a ((p - 1) / q) p ≠ 1 % p))
termination_by c => sizeOf c
decreasing_by
  all_goals {
    simp_wf
    rename_i hmem
    have h1 := List.sizeOf_lt_of_mem hmem
    simp [Prod.mk.sizeOf_spec] at h1
    omega
  }

/-! ### Correctness -/

/-- A prime dividing `∏ q^e` over a list of *primes* must equal one of them. -/
private lemma prime_dvd_list_prod_pow
    (qs : List (ℕ × ℕ)) (q' : ℕ) (hq' : Nat.Prime q')
    (hqs : ∀ qe ∈ qs, Nat.Prime qe.1)
    (hdvd : q' ∣ (qs.map (fun ⟨q, e⟩ => q ^ e)).prod) :
    ∃ qe ∈ qs, qe.1 = q' := by
  induction qs with
  | nil =>
      simp at hdvd
      exact absurd hdvd hq'.one_lt.ne'
  | cons head tail ih =>
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases (Nat.Prime.dvd_mul hq').mp hdvd with h1 | h2
      · refine ⟨head, List.mem_cons_self, ?_⟩
        have hhead_prime : Nat.Prime head.1 := hqs head List.mem_cons_self
        exact ((Nat.prime_dvd_prime_iff_eq hq' hhead_prime).mp
          (hq'.dvd_of_dvd_pow h1)).symm
      · have : ∀ qe ∈ tail, Nat.Prime qe.1 := fun qe hmem =>
          hqs qe (List.mem_cons_of_mem _ hmem)
        obtain ⟨qe, hmem, heq⟩ := ih this h2
        exact ⟨qe, List.mem_cons_of_mem _ hmem, heq⟩

/-- Main correctness theorem. -/
lemma verify_correct : ∀ c : Pratt, c.verify = true → Nat.Prime c.prime
  | .small p, h => by
      unfold verify at h
      simp only [prime]
      exact of_decide_eq_true h
  | .step p a factors, h => by
      simp only [verify, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, List.mem_attach, forall_const,
        Subtype.forall, prime] at h
      obtain ⟨⟨⟨⟨⟨hp1, he_pos⟩, hsubs⟩, hprod⟩, hfermat⟩, hlucas⟩ := h
      -- Unpack `hsubs` into: each sub-cert's prime matches and verifies.
      have hsubs_detail :
          ∀ qe ∈ factors, qe.2.2.prime = qe.1 ∧ qe.2.2.verify = true := by
        intro qe hmem
        obtain ⟨q, e, sub⟩ := qe
        have := hsubs ⟨q, e, sub⟩ hmem
        simp at this
        exact this
      -- Each listed prime is actually prime (recursion).
      have hqs_prime : ∀ qe ∈ factors, Nat.Prime qe.1 := by
        intro qe hmem
        obtain ⟨hprime_eq, hverify⟩ := hsubs_detail qe hmem
        have hrec := verify_correct qe.2.2 hverify
        rw [hprime_eq] at hrec
        exact hrec
      -- Apply Lucas's converse.
      apply lucas_primality p (a : ZMod p)
      · -- Cast Fermat condition into ZMod p.
        rw [powMod_eq] at hfermat
        have h1 : ((a ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [ZMod.natCast_eq_natCast_iff]
          change _ % p = _ % p
          exact hfermat
        push_cast at h1
        exact h1
      · intro q hq hqdvd
        have hq_nat : Nat.Prime q := hq
        -- `q ∣ ∏ qᵢ^eᵢ`, so `q` equals some `qᵢ`.
        have hdvd_prod :
            q ∣ (factors.map (fun qe : ℕ × ℕ × Pratt => qe.1 ^ qe.2.1)).prod := by
          rw [hprod]; exact hqdvd
        obtain ⟨qe_pair, hmem_pair, heq_q⟩ :=
          prime_dvd_list_prod_pow
            (factors.map (fun qe : ℕ × ℕ × Pratt => (qe.1, qe.2.1)))
            q hq_nat
            (by
              intro pair hpair
              simp only [List.mem_map] at hpair
              obtain ⟨qe, hmem', hpair_eq⟩ := hpair
              rw [← hpair_eq]
              exact hqs_prime qe hmem')
            (by
              rw [List.map_map]
              simp only [Function.comp_def]
              exact hdvd_prod)
        simp only [List.mem_map] at hmem_pair
        obtain ⟨qe, hmem, hpair_eq⟩ := hmem_pair
        -- Derive `qe.1 = q`.
        have hqe_eq : qe.1 = q := by
          have : qe_pair.1 = qe.1 := by rw [← hpair_eq]
          rw [← this]; exact heq_q
        -- Lucas non-triviality at this factor.
        have hne := hlucas qe hmem
        rw [powMod_eq] at hne
        intro heq1
        apply hne
        have hcast : ((a ^ ((p - 1) / qe.1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          rw [hqe_eq]
          push_cast
          exact heq1
        rw [ZMod.natCast_eq_natCast_iff] at hcast
        change _ % p = _ % p at hcast
        exact hcast
termination_by c _ => sizeOf c
decreasing_by
  · simp_wf
    have h1 := List.sizeOf_lt_of_mem hmem
    obtain ⟨q', e', sub'⟩ := qe
    simp [Prod.mk.sizeOf_spec] at h1
    simp
    omega

end Pratt

end ZiskFv
