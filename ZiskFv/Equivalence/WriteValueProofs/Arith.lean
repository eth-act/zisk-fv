import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.BinaryAddPackedCorrect
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.Airs.BinaryTable
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Circuit.Add
import ZiskFv.Circuit.Addi
import ZiskFv.Circuit.Addw
import ZiskFv.Circuit.Addiw
import ZiskFv.Circuit.Sub
import ZiskFv.Circuit.Subw
import ZiskFv.Sail.add

/-!
# WriteValueProofs.Arith — `h_rd_val` discharge lemmas for ALU-Arith opcodes

Provides one discharge lemma per opcode for the following 6 opcodes:
ADD, ADDI, ADDW, ADDIW, SUB, SUBW.

SLT, SLTU, SLTI, SLTIU live in `BinaryCompare.lean`.

## Tier classification

| Opcode | Tier | Status |
|--------|------|--------|
| ADD    | 1    | Fully circuit-derived (no residual)              |
| ADDI   | 1.5  | OUTPUT-EQ residual `h_input_val`                 |
| ADDW   | 1.5  | OUTPUT-EQ residual `h_input_val`                 |
| ADDIW  | 1.5  | OUTPUT-EQ residual `h_input_val`                 |
| SUB    | 1.5  | OUTPUT-EQ residual `h_input_val`                 |
| SUBW   | 1.5  | OUTPUT-EQ residual `h_input_val`                 |

## Architecture

**Tier 1 — fully circuit-derived (ADD).** `Spec/Add::add_compositional`
takes a `Valid_BinaryAdd b` parameter, ties `m.c_0`/`m.c_1` directly
to `b.c_chunks_*` via a bus-row match between Main and BinaryAdd, and
the K1-A theorem `binary_add_chunks_eq_bv_add` lifts the chunk-level
carry chain to a `BitVec 64` addition identity. No OUTPUT-EQ
parameter is needed; ADD is the *only* opcode in this file that
reaches genuine Tier 1.

**Tier 1.5 — abstract `OperationBusEntry` (ADDI, ADDW, ADDIW, SUB, SUBW).**
The corresponding `Spec/<Op>::<op>_compositional` theorems take an
**abstract** `bus_entry : OperationBusEntry FGL` (no `Valid_BinaryAdd`
or `Valid_BinaryExtension` parameter). They prove only

```
  main_c_packed m r_main = bus_entry.c_lo + bus_entry.c_hi * 2^32
```

— i.e. Main's `c` lanes equal the abstract bus entry's `c` lanes.
There is **no** Spec theorem in tree that ties
`bus_entry.c_lo + bus_entry.c_hi * 2^32` to `(<inputs>).toNat` for
these opcodes. Supplying it as `h_input_val` to the lemmas below is a
genuine OUTPUT-EQ trust gap.

The body of each non-ADD lemma still does real work:
* `h_circuit` — bundles mode witnesses + bus-match;
* `h_lane_rd` — K2 register-write lane match (Layer 1 trust);
* `h_e2_0..h_e2_7` — per-byte range bounds;
* `h_input_val : bus_entry.c_lo.val + bus_entry.c_hi.val * 2^32 = spec_val.toNat`
  — Binary SM chunk correctness (OUTPUT-EQ; named, not derived).

From these, the byte-sum Nat equality is derived **internally**
(`byte_sum_from_lane_match`) and `bv64_of_byte_sum` closes the
conclusion. The byte-decomposition layer is real Tier-1 work; only
the chunk-level `h_input_val` is the residual gap.

## Why `h_input_val` cannot be retired with the in-tree infrastructure

ADD's success rests on three pieces:

1. The `Valid_BinaryAdd` named-column AIR
   (`Airs/Binary/BinaryAdd.lean`) extracted from the BinaryAdd PIL
   AIR (#11), exposing `a_0`/`a_1`/`b_0`/`b_1`/`c_chunks_*`/`cout_*`
   columns as field accessors.
2. `Spec/Add::add_compositional` taking that AIR as a hypothesis and
   matching its bus row against Main's bus row, yielding the FGL
   identity `main_c_packed = main_a_packed + main_b_packed -
   cout_1 * 2^64`.
3. K1-A `binary_add_chunks_eq_bv_add` lifting the FGL identity to
   `BitVec 64`.

For ADDI/SUB the missing piece is (2): no
`addi_compositional_with_binaryadd` / `sub_compositional_with_binaryadd`
exists in `Spec/`.

For ADDW/ADDIW/SUBW the missing piece is *both* (1) and (2): the
W-variant Binary-SM is `BinaryExtension` (PIL AIR #12), which is
**not extracted** at all (`docs/fv/air-inventory.md` lists it as
"❌ row-constraints missing"). No `Valid_BinaryExtension` AIR
exists in the Lean tree.
-/

set_option maxHeartbeats 2400000

namespace ZiskFv.Equivalence.WriteValueProofs.Arith

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.Binary
open ZiskFv.Airs.BinaryTable
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.LaneMatch
open ZiskFv.Circuit.Add
open ZiskFv.PackedBitVec

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Shared primitive: byte-sum → U64.toBV bridge

All opcodes (Tier 1 and Tier 2) use this kernel to convert the byte-sum
identity into the U64.toBV equality. -/

/-- **Byte-sum → U64.toBV bridge.** Given byte-range bounds on the 8 lanes
    of a memory-bus entry `e2` and a hypothesis identifying their
    little-endian Nat sum with `spec_val.toNat`, produces
    `U64.toBV #v[e2.x0, ..., e2.x7] = spec_val`.

    This is the shared kernel for all derivation lemmas. -/
lemma bv64_of_byte_sum
    (spec_val : BitVec 64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : FGL)
    (h0 : x0.val < 256) (h1 : x1.val < 256) (h2 : x2.val < 256) (h3 : x3.val < 256)
    (h4 : x4.val < 256) (h5 : x5.val < 256) (h6 : x6.val < 256) (h7 : x7.val < 256)
    (h_sum :
      x0.val + x1.val * 256 + x2.val * 65536 + x3.val * 16777216
      + x4.val * 4294967296 + x5.val * 1099511627776
      + x6.val * 281474976710656 + x7.val * 72057594037927936
      = spec_val.toNat) :
    U64.toBV #v[(x0 : BitVec 8), (x1 : BitVec 8), (x2 : BitVec 8), (x3 : BitVec 8),
                (x4 : BitVec 8), (x5 : BitVec 8), (x6 : BitVec 8), (x7 : BitVec 8)]
      = spec_val := by
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_sum]

/-! ## Shared primitive: lane-match → byte-sum derivation

For opcodes using an abstract `OperationBusEntry`, derives the byte-sum
Nat equality from the c-lane bus-match and lane-match hypotheses. -/

/-- **Lane-match → byte-sum.** Given:
    * `h_clo : m.c_0 r_main = bus_entry.c_lo` (from bus-match),
    * `h_chi : m.c_1 r_main = bus_entry.c_hi` (from bus-match),
    * `h_lo_match : m.c_0 r_main = memory_entry_lo e2` (from lane-match),
    * `h_hi_match : m.c_1 r_main = memory_entry_hi e2` (from lane-match),
    * byte ranges on `e2`,
    * `h_input_val : bus_entry.c_lo.val + bus_entry.c_hi.val * 4294967296 = spec_val.toNat`,

    derives the byte-sum equality
    `e2.x0.val + ... + e2.x7.val * 2^56 = spec_val.toNat`.

    This is the internal derivation step that replaces the old `h_c_byte_sum`
    parameter in all non-ADD Tier-1 lemmas. -/
private lemma byte_sum_from_lane_match
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (e2 : MemoryBusEntry FGL)
    (spec_val : BitVec 64)
    (h_clo : m.c_0 r_main = bus_entry.c_lo)
    (h_chi : m.c_1 r_main = bus_entry.c_hi)
    (h_lo_match : m.c_0 r_main = memory_entry_lo e2)
    (h_hi_match : m.c_1 r_main = memory_entry_hi e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_val :
      bus_entry.c_lo.val + bus_entry.c_hi.val * 4294967296 = spec_val.toNat) :
    e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
    + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
    + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
    = spec_val.toNat := by
  -- Step 1: bus_entry.c_lo = memory_entry_lo e2 (from h_clo + h_lo_match)
  have h_lo_eq : bus_entry.c_lo = memory_entry_lo e2 := by
    rw [← h_clo, h_lo_match]
  have h_hi_eq : bus_entry.c_hi = memory_entry_hi e2 := by
    rw [← h_chi, h_hi_match]
  -- Step 2: lift lo to Nat
  -- memory_entry_lo e2 = e2.x0 + e2.x1*256 + e2.x2*65536 + e2.x3*16777216 : FGL
  -- Under byte ranges, this Nat sum < 2^32 < GL_prime, so the FGL.val equals the Nat sum.
  have h_lo_nat : (memory_entry_lo e2).val
      = e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 := by
    simp only [memory_entry_lo]
    have h_cast : e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216
        = (((e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536
             + e2.x3.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  -- Step 3: lift hi to Nat
  have h_hi_nat : (memory_entry_hi e2).val
      = e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 := by
    simp only [memory_entry_hi]
    have h_cast : e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216
        = (((e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536
             + e2.x7.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  -- Step 4: rewrite c_lo.val and c_hi.val via the entry equalities
  rw [h_lo_eq] at h_input_val
  rw [h_hi_eq] at h_input_val
  rw [h_lo_nat, h_hi_nat] at h_input_val
  -- h_input_val now:
  --   (x0.val + x1.val*256 + x2.val*65536 + x3.val*16777216)
  --   + (x4.val + x5.val*256 + x6.val*65536 + x7.val*16777216) * 4294967296
  --   = spec_val.toNat
  -- Step 5: omega closes the rearrangement to the byte-sum form
  omega

/-! ## ADD (Tier 1 — fully derived from circuit constraints) -/

/-- **ADD h_rd_val derivation (Tier 1 — no residual hypothesis).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = add_input.r1_val + add_input.r2_val`
    from circuit hypotheses alone.

    **Proof chain:**
    1. Extract BinaryAdd carry-chain constraints + bus match from `add_circuit_holds`.
    2. Apply `binary_add_chunks_eq_bv_add` (K1-A) → BitVec 64 addition identity.
    3. From bus match: `m.c_0/c_1` equal `b.c_chunks_{1,0}*65536+c_chunks_0` and
       `b.c_chunks_{3,2}*65536+c_chunks_2`.
    4. From lane match: `m.c_0/c_1` equal `memory_entry_lo/hi e2`.
    5. Byte ranges + c_chunks range bounds give the byte-sum identity.
    6. `bv64_of_byte_sum` closes. -/
lemma h_rd_val_arith_add
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (add_input : PureSpec.AddInput)
    -- Circuit hypothesis
    (h_circuit : add_circuit_holds m b r_main r_binary)
    -- Lane-match hypothesis for rd-write (K2, Layer 1 trust)
    (h_lane_rd  : register_write_lanes_match m r_main e2)
    -- Byte-range hypotheses for e2 (the rd-write entry)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- BinaryAdd range bounds (needed by K1-A; derivable from byte ranges + lane match)
    (h_a_range : a_chunks_in_range b r_binary)
    (h_b_range : b_chunks_in_range b r_binary)
    (h_c_range : c_chunks_in_range b r_binary)
    -- Input-value hypotheses (connecting Sail inputs to bus entry bytes)
    (h_input_r1 : add_input.r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296))
    (h_input_r2 : add_input.r2_val
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = add_input.r1_val + add_input.r2_val := by
  -- Step 1: Extract the carry chain from h_circuit.
  obtain ⟨_, h_binary_core, h_bus_match, _⟩ := h_circuit
  -- Step 2: Apply K1-A — BinaryAdd carry chain → BitVec 64 addition.
  have h_bv_add := binary_add_chunks_eq_bv_add b r_binary h_binary_core h_a_range h_b_range h_c_range
  -- Step 3: Extract c_lo / c_hi bus match equalities.
  -- From matches_entry, h_bus_match gives field equalities between Main and BinaryAdd bus rows.
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd] at h_bus_match
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus_match
  -- h_match_clo : m.c_0 r_main = b.c_chunks_1 r_binary * 65536 + b.c_chunks_0 r_binary
  -- h_match_chi : m.c_1 r_main = b.c_chunks_3 r_binary * 65536 + b.c_chunks_2 r_binary
  -- Step 4: From the rd lane match, extract c_0 / c_1 vs memory entry lo/hi.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_c0_eq, h_c1_eq⟩ := h_lane_rd
  -- h_c0_eq : m.c_0 r_main = memory_entry_lo e2
  -- h_c1_eq : m.c_1 r_main = memory_entry_hi e2
  -- Step 5: The c_chunks range bounds.
  obtain ⟨h_c0, h_c1, h_c2, h_c3⟩ := h_c_range
  -- Step 6: Show the byte sum of e2 equals c_chunks in the K1-A form.
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7]
  rw [h_input_r1, h_input_r2]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_bv_add_nat :
      (BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296)
       + BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296)).toNat
      = (BitVec.ofNat 64
          ((b.c_chunks_0 r_binary).val
            + (b.c_chunks_1 r_binary).val * 65536
            + (b.c_chunks_2 r_binary).val * 4294967296
            + (b.c_chunks_3 r_binary).val * 281474976710656)).toNat := by
    exact congrArg BitVec.toNat h_bv_add
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h_bv_add_nat
  rw [h_bv_add_nat]
  rw [BitVec.toNat_ofNat]
  have h_lo_eq : (memory_entry_lo e2).val
      = (b.c_chunks_1 r_binary).val * 65536 + (b.c_chunks_0 r_binary).val := by
    have h_fgl : memory_entry_lo e2
        = (b.c_chunks_1 r_binary) * 65536 + b.c_chunks_0 r_binary := by
      rw [← h_c0_eq, h_match_clo]
    have h_cast : b.c_chunks_1 r_binary * 65536 + b.c_chunks_0 r_binary
        = (((b.c_chunks_1 r_binary).val * 65536 + (b.c_chunks_0 r_binary).val : ℕ) : FGL) := by
      push_cast; ring
    rw [h_cast] at h_fgl
    have heq := congr_arg Fin.val h_fgl
    simp only [Fin.val_natCast] at heq
    omega
  have h_hi_eq : (memory_entry_hi e2).val
      = (b.c_chunks_3 r_binary).val * 65536 + (b.c_chunks_2 r_binary).val := by
    have h_fgl : memory_entry_hi e2
        = (b.c_chunks_3 r_binary) * 65536 + b.c_chunks_2 r_binary := by
      rw [← h_c1_eq, h_match_chi]
    have h_cast : b.c_chunks_3 r_binary * 65536 + b.c_chunks_2 r_binary
        = (((b.c_chunks_3 r_binary).val * 65536 + (b.c_chunks_2 r_binary).val : ℕ) : FGL) := by
      push_cast; ring
    rw [h_cast] at h_fgl
    have heq := congr_arg Fin.val h_fgl
    simp only [Fin.val_natCast] at heq
    omega
  simp only [memory_entry_lo, memory_entry_hi] at h_lo_eq h_hi_eq
  have h_lo_val : (e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216 : FGL).val
      = e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 := by
    have h_cast : e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216
        = (((e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast]
    rw [Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  have h_hi_val : (e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216 : FGL).val
      = e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 := by
    have h_cast : e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216
        = (((e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast]
    rw [Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  omega

/-! ## ADDI (Tier 1 — fully derived from circuit constraints) -/

/-- **ADDI h_rd_val derivation (Tier 1 — no residual hypothesis).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = r1_val + BitVec.signExtend 64 imm`
    from circuit hypotheses alone. Mirrors ADD's Tier-1 structure
    using the new `Spec/Addi::addi_compositional_with_binaryadd` (commit
    after `e0f8e11`) which threads BinaryAdd's carry chain analogously
    to `Spec/Add::add_compositional`.

    ADDI shares ADD's bus opcode literal (`OP_ADD = 10`); the BinaryAdd
    AIR cannot distinguish them. The transpile axiom (CLAUDE.md trusted
    surface) is what pins ADDI's `b` lanes to the sign-extended
    immediate rather than rs2 — that's reflected here in `h_input_imm`.

    **Proof chain:**
    1. Extract BinaryAdd carry-chain constraints + bus match from
       `addi_circuit_holds_with_binaryadd`.
    2. Apply `binary_add_chunks_eq_bv_add` (K1-A) → BitVec 64 addition.
    3. From bus match: `m.c_0/c_1` equal BinaryAdd's c-chunk packings.
    4. From lane match: `m.c_0/c_1` equal `memory_entry_lo/hi e2`.
    5. Byte ranges + chunk ranges close the byte-sum identity. -/
lemma h_rd_val_arith_addi
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    -- Tier-1 circuit hypothesis (bundles Main + BinaryAdd + bus-match + ADDI mode)
    (h_circuit : ZiskFv.Circuit.Addi.addi_circuit_holds_with_binaryadd m b r_main r_binary)
    -- Lane-match hypothesis for rd-write (K2, Layer 1 trust)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- Byte-range hypotheses for e2
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- BinaryAdd chunk-range bounds (needed by K1-A)
    (h_a_range : a_chunks_in_range b r_binary)
    (h_b_range : b_chunks_in_range b r_binary)
    (h_c_range : c_chunks_in_range b r_binary)
    -- TRANSPILE-BRIDGE: r1_val matches BinaryAdd's a-side packing
    (h_input_r1 : r1_val
      = BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296))
    -- TRANSPILE-BRIDGE: signExtend imm matches BinaryAdd's b-side packing
    -- (transpile_ADDI pins the immediate into Main's b lanes, which the
    -- bus match propagates to BinaryAdd's b lanes)
    (h_input_imm : BitVec.signExtend 64 imm
      = BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = r1_val + BitVec.signExtend 64 imm := by
  -- Step 1: Extract the carry chain from h_circuit.
  obtain ⟨_, h_binary_core, h_bus_match, _⟩ := h_circuit
  -- Step 2: Apply K1-A — BinaryAdd carry chain → BitVec 64 addition.
  have h_bv_add := binary_add_chunks_eq_bv_add b r_binary h_binary_core h_a_range h_b_range h_c_range
  -- Step 3: Extract c_lo / c_hi bus match equalities.
  simp only [matches_entry, opBus_row_Main, opBus_row_BinaryAdd] at h_bus_match
  obtain ⟨_, _, _, _, _, _, h_match_clo, h_match_chi, _, _, _, _⟩ := h_bus_match
  -- Step 4: From the rd lane match, extract c_0 / c_1 vs memory entry lo/hi.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_c0_eq, h_c1_eq⟩ := h_lane_rd
  -- Step 5: The c_chunks range bounds.
  obtain ⟨h_c0, h_c1, h_c2, h_c3⟩ := h_c_range
  -- Step 6: Show the byte sum of e2 equals c_chunks in the K1-A form.
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat _ _ _ _ _ _ _ _
        h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7]
  rw [h_input_r1, h_input_imm]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h_bv_add_nat :
      (BitVec.ofNat 64 ((b.a_0 r_binary).val + (b.a_1 r_binary).val * 4294967296)
       + BitVec.ofNat 64 ((b.b_0 r_binary).val + (b.b_1 r_binary).val * 4294967296)).toNat
      = (BitVec.ofNat 64
          ((b.c_chunks_0 r_binary).val
            + (b.c_chunks_1 r_binary).val * 65536
            + (b.c_chunks_2 r_binary).val * 4294967296
            + (b.c_chunks_3 r_binary).val * 281474976710656)).toNat := by
    exact congrArg BitVec.toNat h_bv_add
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h_bv_add_nat
  rw [h_bv_add_nat]
  rw [BitVec.toNat_ofNat]
  have h_lo_eq : (memory_entry_lo e2).val
      = (b.c_chunks_1 r_binary).val * 65536 + (b.c_chunks_0 r_binary).val := by
    have h_fgl : memory_entry_lo e2
        = (b.c_chunks_1 r_binary) * 65536 + b.c_chunks_0 r_binary := by
      rw [← h_c0_eq, h_match_clo]
    have h_cast : b.c_chunks_1 r_binary * 65536 + b.c_chunks_0 r_binary
        = (((b.c_chunks_1 r_binary).val * 65536 + (b.c_chunks_0 r_binary).val : ℕ) : FGL) := by
      push_cast; ring
    rw [h_cast] at h_fgl
    have heq := congr_arg Fin.val h_fgl
    simp only [Fin.val_natCast] at heq
    omega
  have h_hi_eq : (memory_entry_hi e2).val
      = (b.c_chunks_3 r_binary).val * 65536 + (b.c_chunks_2 r_binary).val := by
    have h_fgl : memory_entry_hi e2
        = (b.c_chunks_3 r_binary) * 65536 + b.c_chunks_2 r_binary := by
      rw [← h_c1_eq, h_match_chi]
    have h_cast : b.c_chunks_3 r_binary * 65536 + b.c_chunks_2 r_binary
        = (((b.c_chunks_3 r_binary).val * 65536 + (b.c_chunks_2 r_binary).val : ℕ) : FGL) := by
      push_cast; ring
    rw [h_cast] at h_fgl
    have heq := congr_arg Fin.val h_fgl
    simp only [Fin.val_natCast] at heq
    omega
  simp only [memory_entry_lo, memory_entry_hi] at h_lo_eq h_hi_eq
  have h_lo_val : (e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216 : FGL).val
      = e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 := by
    have h_cast : e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216
        = (((e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast]
    rw [Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  have h_hi_val : (e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216 : FGL).val
      = e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 := by
    have h_cast : e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216
        = (((e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast]
    rw [Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    omega
  omega

/-! ## Internal kernel: byte-sum from chain-style c-lane match

For SUB / ADDW / SUBW (and the BinaryCompare lemmas in their own file),
the c-lane bus match is in chain form `m.c_0 = c0 + c1*256 + c2*2^16 + c3*2^24`,
and `m.c_1 = c4 + c5*256 + c6*2^16 + c7*2^24`. Combined with the rd-write
lane match, this kernel produces the byte-sum equality
`e2 byte sum = c-byte sum (Nat)`. -/

/-- Byte-sum derivation from chain-style c-lane bus-match + lane-match. -/
private lemma byte_sum_from_chain_lane_match
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (c0 c1 c2 c3 c4 c5 c6 c7 : FGL)
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_lo_match : m.c_0 r_main = memory_entry_lo e2)
    (h_hi_match : m.c_1 r_main = memory_entry_hi e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256) :
    e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
    + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
    + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
    = c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
      + c4.val * 4294967296 + c5.val * 1099511627776
      + c6.val * 281474976710656 + c7.val * 72057594037927936 := by
  have h_lo_eq : memory_entry_lo e2 = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216 := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq : memory_entry_hi e2 = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216 := by
    rw [← h_hi_match, h_match_chi]
  have h_lo_nat : (memory_entry_lo e2).val
      = e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 := by
    simp only [memory_entry_lo]
    have h_cast : e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216
        = (((e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536
             + e2.x3.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_hi_nat : (memory_entry_hi e2).val
      = e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 := by
    simp only [memory_entry_hi]
    have h_cast : e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216
        = (((e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536
             + e2.x7.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_lo_c_nat : (c0 + c1 * 256 + c2 * 65536 + c3 * 16777216 : FGL).val
      = c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 := by
    have h_cast :
        c0 + c1 * 256 + c2 * 65536 + c3 * 16777216
        = ((((c0.val + c1.val * 256 + c2.val * 65536
             + c3.val * 16777216 : ℕ) : FGL))) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_hi_c_nat : (c4 + c5 * 256 + c6 * 65536 + c7 * 16777216 : FGL).val
      = c4.val + c5.val * 256 + c6.val * 65536 + c7.val * 16777216 := by
    have h_cast :
        c4 + c5 * 256 + c6 * 65536 + c7 * 16777216
        = ((((c4.val + c5.val * 256 + c6.val * 65536
             + c7.val * 16777216 : ℕ) : FGL))) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq
  have h_hi_val := congr_arg Fin.val h_hi_eq
  rw [h_lo_nat, h_lo_c_nat] at h_lo_val
  rw [h_hi_nat, h_hi_c_nat] at h_hi_val
  omega

/-! ## ADDW (Tier 1 — fully derived from circuit constraints, m32=1) -/

/-- **ADDW h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7]
    = BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)`
    where the 32-bit operand sums match the low halves of the 64-bit
    register reads.

    ADDW routes through `OP_ADD_W = 26` with `m32 = 1`. The Binary SM
    consumes 4 OP_ADD chains for bytes 0..3 (with `pi3 = 1` as plast)
    plus per-byte sign-extension lookups on bytes 4..7 (SEXT_00 if the
    low-32 result is non-negative, SEXT_FF otherwise). -/
lemma h_rd_val_arith_addw
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (a0 a1 a2 a3 b0 b1 b2 b3
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    -- K1-B ADDW chain witnesses (4 bytes OP_ADD).
    (h_byte_0 : consumer_byte_match_chain OP_ADD a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_ADD a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_ADD a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_ADD a3 b3 c3 cin3 fl3 pi3)
    -- Byte ranges.
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    -- Carry-chain links + plast.
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val = 1)
    -- Sign-extension choice on c4..c7 (the SEXT_00 / SEXT_FF case-disjunction).
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648))
    -- Main↔Binary c-lane bus-match.
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- The 32-bit operand sums (Sail trims the 64-bit reads to 32 bits for ADDW).
    (a32sum b32sum : ℕ)
    (h_a32 : a32sum = a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
    (h_b32 : b32sum = b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum) := by
  -- Step 1: K1-B ADDW lift.
  have h_bv := binary_addw_chunks_eq_bv_add_w
    a0 a1 a2 a3 b0 b1 b2 b3
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3
    fl0 fl1 fl2 fl3
    pi0 pi1 pi2 pi3
    h_byte_0 h_byte_1 h_byte_2 h_byte_3
    ha0 ha1 ha2 ha3
    hb0 hb1 hb2 hb3
    hc0 hc1 hc2 hc3
    h_cin0 h_cin1 h_cin2 h_cin3
    h_pi0 h_pi1 h_pi2 h_pi3
    h_sext_choice
  -- Step 2: extract lane-match.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- Step 3: derive byte-sum identity.
  have h_byte_sum := byte_sum_from_chain_lane_match m r_main e2
    c0 c1 c2 c3 c4 c5 c6 c7
    h_match_clo h_match_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  -- Step 4: tie to BitVec.signExtend output.
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum)).toNat := by
    rw [h_byte_sum, h_a32, h_b32]
    rw [h_bv, BitVec.toNat_ofNat]
    have h_lt :
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
          + c4.val * 4294967296 + c5.val * 1099511627776
          + c6.val * 281474976710656 + c7.val * 72057594037927936
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum
    (BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum))
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## ADDIW (Tier 1 — fully derived from circuit constraints, m32=1) -/

/-- **ADDIW h_rd_val derivation (Tier 1).**
    ADDIW shares ADDW's Zisk opcode (`OP_ADD_W = 26` with `m32 = 1`)
    at the Binary SM. Differs only on the Sail side (immediate vs rs2);
    the circuit-level identity is the same. Forwards to
    `h_rd_val_arith_addw` with the Sail immediate-extended `b32sum`. -/
lemma h_rd_val_arith_addiw
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (a0 a1 a2 a3 b0 b1 b2 b3
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    (h_byte_0 : consumer_byte_match_chain OP_ADD a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_ADD a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_ADD a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_ADD a3 b3 c3 cin3 fl3 pi3)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val = 1)
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648))
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (a32sum b32sum : ℕ)
    (h_a32 : a32sum = a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
    (h_b32 : b32sum = b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ofNat 32 a32sum + BitVec.ofNat 32 b32sum) :=
  h_rd_val_arith_addw m r_main e2
    a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3 fl0 fl1 fl2 fl3 pi0 pi1 pi2 pi3
    h_byte_0 h_byte_1 h_byte_2 h_byte_3
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_cin0 h_cin1 h_cin2 h_cin3
    h_pi0 h_pi1 h_pi2 h_pi3 h_sext_choice
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    a32sum b32sum h_a32 h_b32

/-! ## SUB (Tier 1 — fully derived from circuit constraints) -/

/-- **SUB h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = r1_val - r2_val` from K1-B
    SUB chain lift, c-lane bus-match, lane-match, byte ranges, and
    transpile bridges. No `h_input_val` residual.

    SUB routes through `OP_SUB = 11` via `ALURTypeArchetype` on the
    Main side; the Binary AIR consumes 8 byte-chains at `OP_SUB` with
    `pi7 = 1` (final byte) and per-byte cin links. -/
lemma h_rd_val_arith_sub
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    -- K1-B SUB chain witnesses (8 bytes, OP_SUB).
    (a0 a1 a2 a3 a4 a5 a6 a7
     b0 b1 b2 b3 b4 b5 b6 b7
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
     fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
     pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7 : FGL)
    (h_byte_0 : consumer_byte_match_chain OP_SUB a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_SUB a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_SUB a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_SUB a3 b3 c3 cin3 fl3 pi3)
    (h_byte_4 : consumer_byte_match_chain OP_SUB a4 b4 c4 cin4 fl4 pi4)
    (h_byte_5 : consumer_byte_match_chain OP_SUB a5 b5 c5 cin5 fl5 pi5)
    (h_byte_6 : consumer_byte_match_chain OP_SUB a6 b6 c6 cin6 fl6 pi6)
    (h_byte_7 : consumer_byte_match_chain OP_SUB a7 b7 c7 cin7 fl7 pi7)
    -- Byte ranges on a/b/c cells.
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (ha4 : a4.val < 256) (ha5 : a5.val < 256) (ha6 : a6.val < 256) (ha7 : a7.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hb4 : b4.val < 256) (hb5 : b5.val < 256) (hb6 : b6.val < 256) (hb7 : b7.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    -- Carry-chain links (cin_0 = 0, cin_{i+1} = flags_i % 2).
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_cin4 : cin4.val = fl3.val % 2)
    (h_cin5 : cin5.val = fl4.val % 2)
    (h_cin6 : cin6.val = fl5.val % 2)
    (h_cin7 : cin7.val = fl6.val % 2)
    -- Position-indicator pins (pi0..pi6 ≠ 1, pi7 = 1).
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val ≠ 1) (h_pi4 : pi4.val ≠ 1) (h_pi5 : pi5.val ≠ 1)
    (h_pi6 : pi6.val ≠ 1) (h_pi7 : pi7.val = 1)
    -- Main↔Binary c-lane bus-match (cout = 0 since pi7 = 1).
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Transpile bridges (input side).
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
            + a4.val * 4294967296 + a5.val * 1099511627776
            + a6.val * 281474976710656 + a7.val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          (b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216
            + b4.val * 4294967296 + b5.val * 1099511627776
            + b6.val * 281474976710656 + b7.val * 72057594037927936)) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = r1_val - r2_val := by
  -- Step 1: K1-B SUB lift.
  have h_bv := binary_sub_chunks_eq_bv_sub
    a0 a1 a2 a3 a4 a5 a6 a7
    b0 b1 b2 b3 b4 b5 b6 b7
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3 cin4 cin5 cin6 cin7
    fl0 fl1 fl2 fl3 fl4 fl5 fl6 fl7
    pi0 pi1 pi2 pi3 pi4 pi5 pi6 pi7
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_cin0 h_cin1 h_cin2 h_cin3 h_cin4 h_cin5 h_cin6 h_cin7
    h_pi0 h_pi1 h_pi2 h_pi3 h_pi4 h_pi5 h_pi6 h_pi7
  -- Step 2: extract lane-match.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- Step 3: derive byte-sum identity from chain bus-match + lane-match.
  have h_byte_sum := byte_sum_from_chain_lane_match m r_main e2
    c0 c1 c2 c3 c4 c5 c6 c7
    h_match_clo h_match_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  -- Step 4: identify byte sum with (r1_val - r2_val).toNat via h_bv.
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (r1_val - r2_val).toNat := by
    rw [h_byte_sum]
    rw [h_input_r1, h_input_r2]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt :
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
          + c4.val * 4294967296 + c5.val * 1099511627776
          + c6.val * 281474976710656 + c7.val * 72057594037927936
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val - r2_val) e2.x0 e2.x1 e2.x2 e2.x3
    e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SUBW (Tier 1 — fully derived from circuit constraints, m32=1) -/

/-- **SUBW h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7]
    = BitVec.signExtend 64 (BitVec.ofNat 32 a32sum - BitVec.ofNat 32 b32sum)`
    where the 32-bit operand sums match the low halves of the 64-bit
    register reads.

    SUBW routes through `OP_SUB_W = 27` with `m32 = 1`. Same circuit-level
    structure as ADDW but with an inline SUBW K1-B-style lift combining the
    4-byte SUB chain (bytes 0..3 at OP_SUB, `pi3 = 1`) with the
    sign-extension byte lookups on bytes 4..7. -/
lemma h_rd_val_arith_subw
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (e2 : MemoryBusEntry FGL)
    (a0 a1 a2 a3 b0 b1 b2 b3
     c0 c1 c2 c3 c4 c5 c6 c7
     cin0 cin1 cin2 cin3
     fl0 fl1 fl2 fl3
     pi0 pi1 pi2 pi3 : FGL)
    -- K1-B SUB chain witnesses (4 bytes OP_SUB).
    (h_byte_0 : consumer_byte_match_chain OP_SUB a0 b0 c0 cin0 fl0 pi0)
    (h_byte_1 : consumer_byte_match_chain OP_SUB a1 b1 c1 cin1 fl1 pi1)
    (h_byte_2 : consumer_byte_match_chain OP_SUB a2 b2 c2 cin2 fl2 pi2)
    (h_byte_3 : consumer_byte_match_chain OP_SUB a3 b3 c3 cin3 fl3 pi3)
    -- Byte ranges.
    (ha0 : a0.val < 256) (ha1 : a1.val < 256) (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256) (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (hc0 : c0.val < 256) (hc1 : c1.val < 256) (hc2 : c2.val < 256) (hc3 : c3.val < 256)
    (hc4 : c4.val < 256) (hc5 : c5.val < 256) (hc6 : c6.val < 256) (hc7 : c7.val < 256)
    -- Carry-chain links + plast.
    (h_cin0 : cin0.val = 0)
    (h_cin1 : cin1.val = fl0.val % 2)
    (h_cin2 : cin2.val = fl1.val % 2)
    (h_cin3 : cin3.val = fl2.val % 2)
    (h_pi0 : pi0.val ≠ 1) (h_pi1 : pi1.val ≠ 1) (h_pi2 : pi2.val ≠ 1)
    (h_pi3 : pi3.val = 1)
    -- Sign-extension choice on c4..c7.
    (h_sext_choice :
      ((c4.val = 0 ∧ c5.val = 0 ∧ c6.val = 0 ∧ c7.val = 0) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 < 2147483648) ∨
      ((c4.val = 255 ∧ c5.val = 255 ∧ c6.val = 255 ∧ c7.val = 255) ∧
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216 ≥ 2147483648))
    -- Main↔Binary c-lane bus-match.
    (h_match_clo : m.c_0 r_main = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216)
    (h_match_chi : m.c_1 r_main = c4 + c5 * 256 + c6 * 65536 + c7 * 16777216)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- The 32-bit operand sums.
    (a32sum b32sum : ℕ)
    (h_a32 : a32sum = a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216)
    (h_b32 : b32sum = b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ofNat 32 a32sum - BitVec.ofNat 32 b32sum) := by
  -- Step 1: Inline K1-B-style SUBW lift.
  have h_bv := binary_subw_chunks_eq_bv_sub_w
    a0 a1 a2 a3 b0 b1 b2 b3
    c0 c1 c2 c3 c4 c5 c6 c7
    cin0 cin1 cin2 cin3
    fl0 fl1 fl2 fl3
    pi0 pi1 pi2 pi3
    h_byte_0 h_byte_1 h_byte_2 h_byte_3
    ha0 ha1 ha2 ha3
    hb0 hb1 hb2 hb3
    hc0 hc1 hc2 hc3
    h_cin0 h_cin1 h_cin2 h_cin3
    h_pi0 h_pi1 h_pi2 h_pi3
    h_sext_choice
  -- Step 2: extract lane-match.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- Step 3: derive byte-sum identity.
  have h_byte_sum := byte_sum_from_chain_lane_match m r_main e2
    c0 c1 c2 c3 c4 c5 c6 c7
    h_match_clo h_match_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  -- Step 4: tie to the BitVec.signExtend output.
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.ofNat 32 a32sum - BitVec.ofNat 32 b32sum)).toNat := by
    rw [h_byte_sum, h_a32, h_b32]
    rw [h_bv, BitVec.toNat_ofNat]
    have h_lt :
        c0.val + c1.val * 256 + c2.val * 65536 + c3.val * 16777216
          + c4.val * 4294967296 + c5.val * 1099511627776
          + c6.val * 281474976710656 + c7.val * 72057594037927936
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum
    (BitVec.signExtend 64 (BitVec.ofNat 32 a32sum - BitVec.ofNat 32 b32sum))
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SLT, SLTU, SLTI, SLTIU — see `Equivalence.WriteValueProofs.BinaryCompare`.

These four signed/unsigned compare opcodes ship as Tier-1 derivations
in `BinaryCompare.lean`, using the K1-B LTU/LT chain lifts plus the
Binary SM's `c[0] += cout` bus emission for the cout-only output. -/

end ZiskFv.Equivalence.WriteValueProofs.Arith
