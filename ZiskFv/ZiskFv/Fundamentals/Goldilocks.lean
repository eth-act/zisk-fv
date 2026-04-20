import Mathlib

/-!
Goldilocks field scaffold for ZisK circuits: `p = 2^64 - 2^32 + 1`. Minimum
required to instantiate extracted constraints and prove the Phase 0 spike
lemma — parallels `OpenvmFv/Fundamentals/BabyBear.lean`. Extend with inverses,
coercions, NoZeroDivisors etc. as later phases need them.
-/

notation "GL_prime" => 18446744069414584321
@[simp] lemma GL_eq : GL_prime = 18446744069414584321 := rfl

namespace Goldilocks

notation "FGL" => Fin GL_prime

lemma prime_GoldilocksPrime : Nat.Prime GL_prime := by native_decide

instance Fact_GLPrime : Fact (Nat.Prime GL_prime) := ⟨prime_GoldilocksPrime⟩
instance : NeZero GL_prime := by constructor; decide
instance : Field FGL := ZMod.instField GL_prime

end Goldilocks
