import Mathlib
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Bits.PackedBitVec

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

/-- The `i`-th byte of a memory-bus entry, extracted from the chunk
    that holds it (i = 0..3 from `value_0`, i = 4..7 from `value_1`).
    Used at the `SailSpec/BusEffect.lean` bridge where the byte-addressed
    Sail memory model needs per-byte access to the chunk-shaped entry. -/
@[reducible]
def byteAt (e : Interaction.MemoryBusEntry FGL) (i : ℕ) : FGL :=
  if i < 4 then byteOf e.value_0 i else byteOf e.value_1 (i - 4)

/-- The `.val` of a byte projection equals its standard div-mod form.
    Useful for `omega`-based proofs about byte sums. -/
lemma byteOf_val_eq (f : FGL) (i : ℕ) :
    (byteOf f i).val = (f.val / 256 ^ i) % 256 := by
  show (((f.val / 256 ^ i) % 256 : ℕ) : FGL).val = (f.val / 256 ^ i) % 256
  have h_mod_lt : (f.val / 256 ^ i) % 256 < 256 := Nat.mod_lt _ (by decide)
  have h_lt_p : (f.val / 256 ^ i) % 256 < GL_prime :=
    Nat.lt_of_lt_of_le h_mod_lt (by decide)
  rw [Fin.val_natCast, Nat.mod_eq_of_lt h_lt_p]

/-- Nat-level byte-pack identity for a Goldilocks chunk with
    `v.val < 2^32`: the 4-byte sum of `(byteOf v i).val` weights
    recovers `v.val`. Closes by `omega` after `256 ^ i` normalization. -/
lemma byteOf_val_sum_eq (v : FGL) (h : v.val < 4294967296) :
    (byteOf v 0).val + (byteOf v 1).val * 256
      + (byteOf v 2).val * 65536 + (byteOf v 3).val * 16777216
    = v.val := by
  have h0 : (256 : ℕ) ^ 0 = 1 := by decide
  have h1 : (256 : ℕ) ^ 1 = 256 := by decide
  have h2 : (256 : ℕ) ^ 2 = 65536 := by decide
  have h3 : (256 : ℕ) ^ 3 = 16777216 := by decide
  rw [byteOf_val_eq v 0, byteOf_val_eq v 1,
      byteOf_val_eq v 2, byteOf_val_eq v 3,
      h0, h1, h2, h3, Nat.div_one]
  omega

/-! ## Chunk → BitVec 64 bridge

`u64_toBV_chunks_eq_ofNat_fgl_val` is the chunk-shape analogue of
`Bits/PackedBitVec.lean`'s `u64_toBV_eq_ofNat_fgl_val`. It bridges a
2-chunk PIL memory-bus message (`value[0], value[1]`) through `byteOf`
to a `BitVec 64` register-write value, matching Sail's byte-addressed
memory model at the `SailSpec/BusEffect.lean` boundary.

This lemma is the principal ingredient of the C8 Phase 2 cutover from
byte-lane `MemoryBusEntry` to chunk-shape `MemoryBusEntry`: it allows
the bridge from chunk-shape entries to `U64.toBV` register values
without re-deriving the per-byte coercion machinery.

Trust note: no axioms. Composes the existing byte-lane bridge with
the chunk-pack identity. -/

/-- **Chunk bridge to `U64.toBV`.** Two FGL chunks `v0, v1` with
    `.val < 2^32`, fed through `byteOf` for byte projections, yield
    `U64.toBV` equal to `BitVec.ofNat 64 (v0 + v1 * 2^32).val` under
    the no-wraparound bound `v0.val + v1.val * 2^32 < GL_prime`. -/
lemma u64_toBV_chunks_eq_ofNat_fgl_val
    (v0 v1 : FGL)
    (h_v0 : v0.val < 4294967296) (h_v1 : v1.val < 4294967296)
    (h_no_wrap : v0.val + v1.val * 4294967296 < GL_prime) :
    U64.toBV #v[(byteOf v0 0 : BitVec 8), (byteOf v0 1 : BitVec 8),
                (byteOf v0 2 : BitVec 8), (byteOf v0 3 : BitVec 8),
                (byteOf v1 0 : BitVec 8), (byteOf v1 1 : BitVec 8),
                (byteOf v1 2 : BitVec 8), (byteOf v1 3 : BitVec 8)]
    = BitVec.ofNat 64 (v0 + v1 * 4294967296 : FGL).val := by
  -- Byte ranges follow from `byteOf_val_lt_256`.
  have hb_v0_0 := byteOf_val_lt_256 v0 0
  have hb_v0_1 := byteOf_val_lt_256 v0 1
  have hb_v0_2 := byteOf_val_lt_256 v0 2
  have hb_v0_3 := byteOf_val_lt_256 v0 3
  have hb_v1_0 := byteOf_val_lt_256 v1 0
  have hb_v1_1 := byteOf_val_lt_256 v1 1
  have hb_v1_2 := byteOf_val_lt_256 v1 2
  have hb_v1_3 := byteOf_val_lt_256 v1 3
  -- Byte-sum bound: byte sum equals `v0.val + v1.val * 2^32 < GL_prime`.
  have h_sum_v0 := byteOf_val_sum_eq v0 h_v0
  have h_sum_v1 := byteOf_val_sum_eq v1 h_v1
  have h_sum_bound :
      (byteOf v0 0).val + (byteOf v0 1).val * 256
      + (byteOf v0 2).val * 65536 + (byteOf v0 3).val * 16777216
      + (byteOf v1 0).val * 4294967296
      + (byteOf v1 1).val * 1099511627776
      + (byteOf v1 2).val * 281474976710656
      + (byteOf v1 3).val * 72057594037927936 < GL_prime := by
    -- High-half v1 contributions factor as `(byteOf-sum-v1) * 2^32`,
    -- which by `h_sum_v1` is `v1.val * 2^32`.
    have h_rearrange :
        (byteOf v1 0).val * 4294967296
        + (byteOf v1 1).val * 1099511627776
        + (byteOf v1 2).val * 281474976710656
        + (byteOf v1 3).val * 72057594037927936
        = ((byteOf v1 0).val + (byteOf v1 1).val * 256
            + (byteOf v1 2).val * 65536
            + (byteOf v1 3).val * 16777216) * 4294967296 := by ring
    omega
  -- Apply the byte-lane bridge from `PackedBitVec.lean`.
  rw [ZiskFv.PackedBitVec.u64_toBV_eq_ofNat_fgl_val
        (byteOf v0 0) (byteOf v0 1) (byteOf v0 2) (byteOf v0 3)
        (byteOf v1 0) (byteOf v1 1) (byteOf v1 2) (byteOf v1 3)
        hb_v0_0 hb_v0_1 hb_v0_2 hb_v0_3
        hb_v1_0 hb_v1_1 hb_v1_2 hb_v1_3
        h_sum_bound]
  -- Bridge the byte-sum FGL element to the chunk-sum FGL element.
  -- The two byte-pack equations `v_i = byteOf-sum-v_i` close the goal.
  have h_fgl_eq :
      (byteOf v0 0 + byteOf v0 1 * 256
        + byteOf v0 2 * 65536 + byteOf v0 3 * 16777216
        + byteOf v1 0 * 4294967296
        + byteOf v1 1 * 1099511627776
        + byteOf v1 2 * 281474976710656
        + byteOf v1 3 * 72057594037927936 : FGL)
      = v0 + v1 * 4294967296 := by
    have hpack0 := (bytes_of_chunk_packing v0 h_v0).symm
    have hpack1 := (bytes_of_chunk_packing v1 h_v1).symm
    linear_combination hpack0 + 4294967296 * hpack1
  rw [h_fgl_eq]

end ZiskFv.Channels.MemoryBusBytes
