import Mathlib
import ZiskFv.Field.Goldilocks

/-!
# Chunk ↔ byte conversion helpers for memory-bus messages

ZisK's PIL memory bus carries 32-bit chunks (`value[0]`, `value[1]`),
but Sail's memory model is byte-addressed (`SailSpec/BusEffect.lean`
splats individual bytes into `state.mem[ptr + i]?`). The bridge from
chunk-shaped bus messages to Sail's byte-addressed semantics happens
here.

`byteOf f i` projects the `i`-th byte of `f.val` (treating `f` as a
nat in `[0, 2^64)` and reading the byte at offset `i`). For a chunk
`f` with `f.val < 2^32`, the first four byte projections (`i ∈ 0..3`)
recover the standard little-endian byte decomposition of `f`.

`bytes_of_chunk_packing` is the standard byte-pack identity:
`f = byteOf f 0 + byteOf f 1 * 256 + byteOf f 2 * 65536 + byteOf f 3 * 16777216`
for any `f : FGL` with `f.val < 2^32`. This is the chunk↔bytes
"packing equation" that previously lived as a row constraint on Mem
in the C8 Phase 1 design.

## Trust note

No axioms. Pure definitional + Nat-arithmetic content.
-/

namespace ZiskFv.Channels.MemoryBusBytes

open Goldilocks

/-- The byte witness for byte index `i` of a Goldilocks field
    element `f`, defined as `(f.val / 256^i) % 256` lifted back to
    the field. -/
@[reducible]
def byteOf (f : FGL) (i : ℕ) : FGL := ((f.val / 256 ^ i) % 256 : ℕ)

/-- `(byteOf f i).val < 256` — the byte projection is always a byte.
    Follows from `Nat.mod_lt` lifted through the natCast. -/
lemma byteOf_val_lt_256 (f : FGL) (i : ℕ) :
    (byteOf f i).val < 256 := by
  show (((f.val / 256 ^ i) % 256 : ℕ) : FGL).val < 256
  have h_mod_lt : (f.val / 256 ^ i) % 256 < 256 := Nat.mod_lt _ (by decide)
  have h_lt_p : (f.val / 256 ^ i) % 256 < GL_prime := by
    exact Nat.lt_of_lt_of_le h_mod_lt (by decide)
  rw [Fin.val_natCast, Nat.mod_eq_of_lt h_lt_p]
  exact h_mod_lt

/-- The standard chunk → 4-byte packing identity: a 32-bit chunk
    equals the sum of its four byte projections weighted by the
    little-endian byte positions. -/
lemma bytes_of_chunk_packing (f : FGL) (h : f.val < 4294967296) :
    f = byteOf f 0 + byteOf f 1 * 256
        + byteOf f 2 * 65536 + byteOf f 3 * 16777216 := by
  -- The proof shows the field equation by lifting through .val.
  -- LHS.val = f.val. RHS.val = b0 + b1*256 + b2*65536 + b3*16777216
  -- where bi = (f.val / 256^i) % 256. Standard byte-pack identity
  -- for any nat below 2^32.
  apply Fin.ext
  show f.val
    = (byteOf f 0 + byteOf f 1 * 256
        + byteOf f 2 * 65536 + byteOf f 3 * 16777216 : FGL).val
  have h0 : (byteOf f 0).val = f.val % 256 := by
    show (((f.val / 256 ^ 0) % 256 : ℕ) : FGL).val = f.val % 256
    have h_lt : (f.val / 256 ^ 0) % 256 < GL_prime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt h_lt]
    simp
  have h1 : (byteOf f 1).val = (f.val / 256) % 256 := by
    show (((f.val / 256 ^ 1) % 256 : ℕ) : FGL).val = (f.val / 256) % 256
    have h_lt : (f.val / 256 ^ 1) % 256 < GL_prime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt h_lt]
    simp
  have h2 : (byteOf f 2).val = (f.val / 65536) % 256 := by
    show (((f.val / 256 ^ 2) % 256 : ℕ) : FGL).val = (f.val / 65536) % 256
    have h_lt : (f.val / 256 ^ 2) % 256 < GL_prime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt h_lt]
    show (f.val / 256 ^ 2) % 256 = (f.val / 65536) % 256
    norm_num
  have h3 : (byteOf f 3).val = (f.val / 16777216) % 256 := by
    show (((f.val / 256 ^ 3) % 256 : ℕ) : FGL).val = (f.val / 16777216) % 256
    have h_lt : (f.val / 256 ^ 3) % 256 < GL_prime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt h_lt]
    show (f.val / 256 ^ 3) % 256 = (f.val / 16777216) % 256
    norm_num
  -- Combine: lift the FGL addition/multiplication to .val (no wrap).
  have hb0_lt : (byteOf f 0).val < 256 := byteOf_val_lt_256 f 0
  have hb1_lt : (byteOf f 1).val < 256 := byteOf_val_lt_256 f 1
  have hb2_lt : (byteOf f 2).val < 256 := byteOf_val_lt_256 f 2
  have hb3_lt : (byteOf f 3).val < 256 := byteOf_val_lt_256 f 3
  -- Move the RHS to nat-level with mod-of-lt at each layer.
  simp only [Fin.val_add, Fin.val_mul]
  have h256_val : ((256 : FGL) : Fin GL_prime).val = 256 :=
    Nat.mod_eq_of_lt (by decide)
  have h65536_val : ((65536 : FGL) : Fin GL_prime).val = 65536 :=
    Nat.mod_eq_of_lt (by decide)
  have h16777216_val : ((16777216 : FGL) : Fin GL_prime).val = 16777216 :=
    Nat.mod_eq_of_lt (by decide)
  rw [h256_val, h65536_val, h16777216_val]
  have hm1 : (byteOf f 1).val * 256 < GL_prime := by
    have : (byteOf f 1).val * 256 < 256 * 256 :=
      Nat.mul_lt_mul_of_pos_right hb1_lt (by decide)
    omega
  have hm2 : (byteOf f 2).val * 65536 < GL_prime := by
    have : (byteOf f 2).val * 65536 < 256 * 65536 :=
      Nat.mul_lt_mul_of_pos_right hb2_lt (by decide)
    omega
  have hm3 : (byteOf f 3).val * 16777216 < GL_prime := by
    have : (byteOf f 3).val * 16777216 < 256 * 16777216 :=
      Nat.mul_lt_mul_of_pos_right hb3_lt (by decide)
    omega
  rw [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hm3]
  have hs1 : (byteOf f 0).val + (byteOf f 1).val * 256 < GL_prime := by omega
  rw [Nat.mod_eq_of_lt hs1]
  have hs2 : (byteOf f 0).val + (byteOf f 1).val * 256
              + (byteOf f 2).val * 65536 < GL_prime := by omega
  rw [Nat.mod_eq_of_lt hs2]
  have hs3 : (byteOf f 0).val + (byteOf f 1).val * 256
              + (byteOf f 2).val * 65536
              + (byteOf f 3).val * 16777216 < GL_prime := by omega
  rw [Nat.mod_eq_of_lt hs3]
  rw [h0, h1, h2, h3]
  -- f.val = (f.val % 256) + ((f.val/256) % 256)*256 + ... + ((f.val/16777216) % 256)*16777216
  -- Standard nat fact for f.val < 2^32.
  omega

end ZiskFv.Channels.MemoryBusBytes
