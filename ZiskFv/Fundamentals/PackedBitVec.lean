import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction

/-!
Field → `BitVec 64` lift used by the MUL / MULHU / MULW equivalence
theorems to express the 8-byte register-write value
`U64.toBV #v[e.x0, ..., e.x7]` in terms of an `FGL`-packed byte
expression `x0 + x1*256 + … + x7*256^7`.

Provided lemmas:

1. `u64_toBV_toNat` — `(U64.toBV v).toNat` as the little-endian
   byte-sum (mirrors openvm-fv's `U32.toBV_toNat`).
2. `fgl_byte_coe_toBV8_toNat` — under `x.val < 256`, the
   `FGL → BitVec 8` coercion is a no-op at `.toNat`.
3. `u64_toBV_of_bytes_toNat` — composition of 1 and 2.
4. `fgl_packed_bytes_nat_cast` — the packed FGL expression equals
   the Nat byte-sum cast to FGL.
5. `fgl_packed_bytes_val_of_lt_prime` — under a no-wraparound bound,
   `.val` equals the Nat byte-sum exactly.
6. `u64_toBV_eq_ofNat_fgl_val` — final bridge composing the above.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.PackedBitVec

open Goldilocks

/-! ## Part 1 — `U64.toBV` vs. little-endian byte-sum

Mirrors openvm-fv's `U32.toBV_toNat` / `U64.toBV_toNat` pattern from
`Fundamentals/U32.lean:195`. The idiom is: iterate `BitVec.toNat_append`
+ `Nat.shiftLeft_add_eq_or_of_lt` (which rewrites `|||` to `+` when the
shifted operand's bit-range is disjoint), then close by `omega`. -/

/-- `(U64.toBV v).toNat` equals the little-endian byte-sum of `v`'s
    bytes. Each byte contributes `256^i` to the sum at position `i`. -/
lemma u64_toBV_toNat (v : U64) :
    (U64.toBV v).toNat =
      v[0].toNat
      + v[1].toNat * 256
      + v[2].toNat * 65536
      + v[3].toNat * 16777216
      + v[4].toNat * 4294967296
      + v[5].toNat * 1099511627776
      + v[6].toNat * 281474976710656
      + v[7].toNat * 72057594037927936 := by
  simp only [U64.toBV]
  iterate 7 rw [BitVec.toNat_append,
                ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
                Nat.shiftLeft_eq]
  omega

/-! ## Part 2 — byte coercions

The `FGL → BitVec 8` coercion in `Fundamentals/Goldilocks.lean:59` is
`coe f := { toFin := ⟨ f.val % 256, _ ⟩ }` — i.e. `BitVec.ofNat 8 f.val`.
Under the byte range `f.val < 256`, the `mod 256` is a no-op. -/

/-- Under `x.val < 256`, the `FGL → BitVec 8` coercion preserves
    `.toNat`. -/
lemma fgl_byte_coe_toBV8_toNat {x : FGL} (h : x.val < 256) :
    ((x : BitVec 8)).toNat = x.val := by
  -- `Coe FGL (BitVec 8) := { coe f := { toFin := ⟨ f.val % 256, _ ⟩ } }`.
  show x.val % 256 = x.val
  exact Nat.mod_eq_of_lt h

/-! ## Part 3 — composed `U64.toBV` over field bytes

The form `h_rd_match` uses: `U64.toBV #v[e.x0, ..., e.x7]` where
`e.xᵢ : FGL` are memory-bus byte lanes that go through the
`FGL → BitVec 8` coercion. Under byte ranges, this equals the
Nat-level byte-sum. -/

/-- **Byte-sum of `U64.toBV` over FGL bytes.** Given byte range
    hypotheses `xᵢ.val < 256`, the `U64.toBV` of the coerced bytes
    reduces at `.toNat` to the little-endian Nat byte-sum. -/
lemma u64_toBV_of_bytes_toNat
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256) :
    (U64.toBV
        #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
           (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]).toNat
      = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936 := by
  rw [u64_toBV_toNat]
  -- Vector indexing into the `#v[...]` literal reduces by rfl.
  show (x0 : BitVec 8).toNat + (x1 : BitVec 8).toNat * 256
        + (x2 : BitVec 8).toNat * 65536 + (x3 : BitVec 8).toNat * 16777216
        + (x4 : BitVec 8).toNat * 4294967296 + (x5 : BitVec 8).toNat * 1099511627776
        + (x6 : BitVec 8).toNat * 281474976710656
        + (x7 : BitVec 8).toNat * 72057594037927936 = _
  rw [fgl_byte_coe_toBV8_toNat h0, fgl_byte_coe_toBV8_toNat h1,
      fgl_byte_coe_toBV8_toNat h2, fgl_byte_coe_toBV8_toNat h3,
      fgl_byte_coe_toBV8_toNat h4, fgl_byte_coe_toBV8_toNat h5,
      fgl_byte_coe_toBV8_toNat h6, fgl_byte_coe_toBV8_toNat h7]

/-! ## Part 4 — FGL-packed byte expression vs. Nat cast

The field-level packed expression `x0 + x1*256 + … + x7*256^7 : FGL`
can be rewritten as the Nat-level sum cast to FGL. Used by callers to
bridge between the Bridge 2 field identity and the BitVec conclusion. -/

/-- **FGL-packed byte expression equals Nat cast.** The field-level
    packed expression `x0 + x1*256 + … + x7*256^7 : FGL` is
    algebraically equal to `((x0.val + x1.val*256 + …) : ℕ) : FGL`.

    Reason: `(x : FGL) = ((x.val : ℕ) : FGL)` (by `ZMod.natCast_val`
    on the prime-power `ZMod GL_prime`), and the Nat-cast distributes
    over `+` and `*` in `FGL`. -/
lemma fgl_packed_bytes_nat_cast
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL) :
    (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
      + x4 * 4294967296 + x5 * 1099511627776
      + x6 * 281474976710656 + x7 * 72057594037927936 : FGL)
    = ((x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
        + x4.val * 4294967296 + x5.val * 1099511627776
        + x6.val * 281474976710656 + x7.val * 72057594037927936 : ℕ) : FGL) := by
  push_cast
  rfl

/-! ## Part 5 — BitVec from FGL, under no-wraparound bound

When the byte-sum is below `GL_prime`, `(fgl_packed : FGL).val` equals
the Nat byte-sum exactly (no mod-p wrap). -/

/-- **FGL-packed value equals Nat sum (no wraparound).** When the Nat
    byte-sum is below `GL_prime`, the `.val` of the FGL-packed
    expression equals the Nat byte-sum exactly.

    Derivation: rewrite via `fgl_packed_bytes_nat_cast` to expose the
    Nat cast, then `ZMod.val_natCast` + `Nat.mod_eq_of_lt` close the
    residual `mod GL_prime`. -/
lemma fgl_packed_bytes_val_of_lt_prime
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h_bound :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
      + x4.val * 4294967296 + x5.val * 1099511627776
      + x6.val * 281474976710656 + x7.val * 72057594037927936 < GL_prime) :
    (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
      + x4 * 4294967296 + x5 * 1099511627776
      + x6 * 281474976710656 + x7 * 72057594037927936 : FGL).val
    = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
      + x4.val * 4294967296 + x5.val * 1099511627776
      + x6.val * 281474976710656 + x7.val * 72057594037927936 := by
  rw [fgl_packed_bytes_nat_cast]
  -- Goal: `((sum : ℕ) : FGL).val = sum`. Use Fin.val_natCast + mod.
  rw [Fin.val_natCast]
  exact Nat.mod_eq_of_lt h_bound

/-! ## Part 6 — final BitVec bridge

Compose parts 3 and 5: given byte ranges and a no-wraparound bound,
`U64.toBV #v[x0..x7] = BitVec.ofNat 64 (fgl_packed.val)`. -/

/-- **Final bridge.** Given byte ranges and the no-wraparound bound,
    `U64.toBV` of the coerced bytes equals `BitVec.ofNat 64` of the
    FGL-packed byte expression's `.val`. -/
lemma u64_toBV_eq_ofNat_fgl_val
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_bound :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
      + x4.val * 4294967296 + x5.val * 1099511627776
      + x6.val * 281474976710656 + x7.val * 72057594037927936 < GL_prime) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
    = BitVec.ofNat 64
        (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
          + x4 * 4294967296 + x5 * 1099511627776
          + x6 * 281474976710656 + x7 * 72057594037927936 : FGL).val := by
  apply BitVec.eq_of_toNat_eq
  rw [u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4 h5 h6 h7]
  rw [fgl_packed_bytes_val_of_lt_prime _ _ _ _ _ _ _ _ h_bound]
  rw [BitVec.toNat_ofNat]
  -- Close `sum = sum % 2^64`; sum < GL_prime < 2^64.
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## Part 7 — 4-byte specializations

Restricted-half companions of `fgl_packed_bytes_val_of_lt_prime`.
Used by `Circuit/LoadDerivation.lean` (originally inlined as
`fgl_packed_4bytes_val_of_byte_range` / `four_bytes_eq_of_packed_eq`)
and by `Airs/MemoryBus/MemAlignBridge.lean`. -/

/-- 4-byte specialization of `fgl_packed_bytes_val_of_lt_prime`: the
    `.val` of an FGL 4-byte packed sum equals the Nat byte sum when
    each byte is `< 256` (sum bounded by `2^32 - 1 < GL_prime`). -/
lemma fgl_packed_4bytes_val_of_byte_range
    (x0 x1 x2 x3 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256)
    (h2 : x2.val < 256) (h3 : x3.val < 256) :
    (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216 : FGL).val
    = x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216 := by
  have h_cast :
      (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216 : FGL)
      = ((x0.val + x1.val * 256 + x2.val * 65536
            + x3.val * 16777216 : ℕ) : FGL) := by
    push_cast
    rfl
  rw [h_cast, Fin.val_natCast]
  apply Nat.mod_eq_of_lt
  omega

/-- Per-byte FGL equality from packed FGL equality on a 4-byte half. -/
lemma four_bytes_eq_of_packed_eq
    (a0 a1 a2 a3 b0 b1 b2 b3 : FGL)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256)
    (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256)
    (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (h_eq : a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
          = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  have h_val_a := fgl_packed_4bytes_val_of_byte_range a0 a1 a2 a3 ha0 ha1 ha2 ha3
  have h_val_b := fgl_packed_4bytes_val_of_byte_range b0 b1 b2 b3 hb0 hb1 hb2 hb3
  have h_val_eq :
      a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      = b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216 := by
    rw [← h_val_a, ← h_val_b, h_eq]
  clear h_eq h_val_a h_val_b
  have hE0 : a0.val = b0.val := by omega
  have hE1 : a1.val = b1.val := by omega
  have hE2 : a2.val = b2.val := by omega
  have hE3 : a3.val = b3.val := by omega
  exact ⟨Fin.ext hE0, Fin.ext hE1, Fin.ext hE2, Fin.ext hE3⟩

/-- Specialization: 4-byte packed sum equals zero iff each byte is zero
    (under byte ranges). -/
lemma four_bytes_zero_of_packed_zero
    (x0 x1 x2 x3 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256)
    (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h_zero : x0 + x1 * 256 + x2 * 65536 + x3 * 16777216 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  have h_packed :
      x0 + x1 * 256 + x2 * 65536 + x3 * 16777216
      = (0 : FGL) + 0 * 256 + 0 * 65536 + 0 * 16777216 := by
    rw [h_zero]; ring
  have z0 : (0 : FGL).val < 256 := by decide
  have := four_bytes_eq_of_packed_eq
    x0 x1 x2 x3 0 0 0 0 h0 h1 h2 h3 z0 z0 z0 z0 h_packed
  exact this

/-- Specialization: a 4-byte packed value `< 256` forces high 3 bytes
    to zero. Used to discharge "low byte only" constraints on a 32-bit
    value (e.g. MemAlignByte's bus_byte slot < 256 ⇒ e.x1..3 = 0). -/
lemma four_bytes_high_three_zero_of_packed_lt_256
    (x0 x1 x2 x3 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256)
    (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h_lt : (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216 : FGL).val < 256) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  rw [fgl_packed_4bytes_val_of_byte_range _ _ _ _ h0 h1 h2 h3] at h_lt
  have hE1 : x1.val = 0 := by omega
  have hE2 : x2.val = 0 := by omega
  have hE3 : x3.val = 0 := by omega
  exact ⟨Fin.ext hE1, Fin.ext hE2, Fin.ext hE3⟩

/-- Specialization: a 4-byte packed value `< 65536` forces high 2 bytes
    to zero. Used for MemAlign's value_0 < 2^16 (width=2) case. -/
lemma four_bytes_high_two_zero_of_packed_lt_65536
    (x0 x1 x2 x3 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256)
    (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h_lt : (x0 + x1 * 256 + x2 * 65536 + x3 * 16777216 : FGL).val < 65536) :
    x2 = 0 ∧ x3 = 0 := by
  rw [fgl_packed_4bytes_val_of_byte_range _ _ _ _ h0 h1 h2 h3] at h_lt
  have hE2 : x2.val = 0 := by omega
  have hE3 : x3.val = 0 := by omega
  exact ⟨Fin.ext hE2, Fin.ext hE3⟩

end ZiskFv.PackedBitVec
