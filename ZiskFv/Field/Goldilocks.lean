import Mathlib
import ZiskFv.Field.GoldilocksPrimality

/-!
Goldilocks field scaffold for ZisK circuits: `p = 2^64 - 2^32 + 1`.

Parallels `OpenvmFv/Fundamentals/BabyBear.lean`. Provides the `Field FGL`
instance plus `BitVec`/`Fin` coercions and the U64 lane/chunk helpers.
-/

notation "GL_prime" => 18446744069414584321
@[simp] lemma GL_eq : GL_prime = 18446744069414584321 := rfl

namespace Goldilocks

notation "FGL" => Fin GL_prime
@[simp] lemma F_eq : FGL = Fin GL_prime := rfl

/-- Pratt primality certificate for Goldilocks `p = 2^64 - 2^32 + 1`.

`p - 1 = 2^32 · 3 · 5 · 17 · 257 · 65537`, and `7` is a primitive root mod `p`.

Each prime factor is ≤ 65537 and handled by a `.small` sub-certificate; the
proof below unfolds the concrete verifier and discharges the arithmetic with
`norm_num`. -/
def goldilocks_pratt : ZiskFv.Pratt :=
  .step 18446744069414584321 7
    [ (2,     32, .small 2)
    , (3,      1, .small 3)
    , (5,      1, .small 5)
    , (17,     1, .small 17)
    , (257,    1, .small 257)
    , (65537,  1, .small 65537)
    ]

lemma prime_GoldilocksPrime : Nat.Prime GL_prime :=
  ZiskFv.Pratt.verify_correct goldilocks_pratt (by
    norm_num [goldilocks_pratt, ZiskFv.Pratt.verify, ZiskFv.Pratt.prime, ZiskFv.powMod])

instance Fact_GLPrime : Fact (Nat.Prime GL_prime) := ⟨prime_GoldilocksPrime⟩
instance : NeZero GL_prime := by constructor; decide

instance : NatCast FGL where
  natCast := (Lean.Grind.Fin.instCommRingFinOfNeZeroNat GL_prime).toCommSemiring.toSemiring.natCast.natCast

instance : Field FGL := ZMod.instField GL_prime
-- `NoZeroDivisors FGL` is derivable from the `Field` instance via
-- `Field → DivisionRing → GroupWithZero → NoZeroDivisors` in mathlib; no
-- explicit declaration needed. BabyBear.lean supplies one for instance-search
-- speed, but it is not load-bearing.

section coercions

/-- Opcode byte → field element. -/
instance : Coe (BitVec 8) FGL where
  coe b := ⟨ b.toNat, by omega ⟩

instance : Coe FGL (BitVec 8) where
  coe f := { toFin := ⟨ f.val % 256, by omega ⟩ }

/-- 16-bit limb → field element (used by `c_chunks[i]`). -/
instance : Coe (BitVec 16) FGL where
  coe b := ⟨ b.toNat, by omega ⟩

instance : Coe FGL (BitVec 16) where
  coe f := { toFin := ⟨ f.val % 65536, by omega ⟩ }

/-- 32-bit lane → field element (used by `a[i]`, `b[i]`, `c[i]` in Main,
    and by BinaryAdd's full 32-bit operand limbs). -/
instance : Coe (BitVec 32) FGL where
  coe b := ⟨ b.toNat, by omega ⟩

instance : Coe FGL (BitVec 32) where
  coe f := { toFin := ⟨ f.val % 4294967296, by omega ⟩ }

end coercions

section U64

/-- ZisK's BinaryAdd represents a 64-bit value as four 16-bit chunks
    `c_chunks[0..3]` in little-endian order. Mirrors openvm-fv's `isU32` on
    4 × 8-bit chunks. -/
@[simp, grind]
def isU64_chunks (v : Vector FGL 4) : Prop :=
  v[0].val < 65536 ∧ v[1].val < 65536 ∧ v[2].val < 65536 ∧ v[3].val < 65536

/-- A ZisK Main-row 64-bit value is split into two 32-bit lanes
    `(lo, hi)` — `a[0]`/`a[1]` in the Main AIR. -/
@[simp, grind]
def isU64_lanes (lo hi : FGL) : Prop :=
  lo.val < 4294967296 ∧ hi.val < 4294967296

/-- Reassemble the 4×16 chunk representation into a `BitVec 64`. -/
@[simp]
def chunks_to_bv64 (v : Vector FGL 4) : BitVec 64 :=
  let c0 : BitVec 64 := ⟨⟨v[0].val % 65536, by omega⟩⟩
  let c1 : BitVec 64 := ⟨⟨v[1].val % 65536, by omega⟩⟩
  let c2 : BitVec 64 := ⟨⟨v[2].val % 65536, by omega⟩⟩
  let c3 : BitVec 64 := ⟨⟨v[3].val % 65536, by omega⟩⟩
  c0 ||| (c1 <<< 16) ||| (c2 <<< 32) ||| (c3 <<< 48)

/-- Reassemble the 2×32 lane representation into a `BitVec 64`. -/
@[simp]
def lanes_to_bv64 (lo hi : FGL) : BitVec 64 :=
  let l : BitVec 64 := ⟨⟨lo.val % 4294967296, by omega⟩⟩
  let h : BitVec 64 := ⟨⟨hi.val % 4294967296, by omega⟩⟩
  l ||| (h <<< 32)

end U64

/-- Sanity check: basic ring identities should close in `FGL`. The Field
    instance reaches `ring` via the global instance — do NOT shadow it with
    a `[Field FGL]` variable in any downstream proof, or `ring` will see a
    dummy instance and fail. -/
example (a b c : FGL) : (a + b) * c = a * c + b * c := by ring

end Goldilocks
