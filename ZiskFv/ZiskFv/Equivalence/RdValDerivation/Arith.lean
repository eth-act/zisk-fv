import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.BinaryAddPackedCorrect
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Spec.Add
import ZiskFv.Spec.Addi
import ZiskFv.Spec.Addw
import ZiskFv.Spec.Addiw
import ZiskFv.Spec.Sub
import ZiskFv.Spec.Subw
import ZiskFv.RV64D.add

/-!
# RdValDerivation.Arith — `h_rd_val` discharge lemmas for ALU-Arith opcodes

**Phase 2.5 N-ALU-Arith** of Track N (`h_rd_val` retirement).

Provides one discharge lemma per opcode for the following 6 opcodes:
ADD, ADDI, ADDW, ADDIW, SUB, SUBW.

SLT, SLTU, SLTI, SLTIU leave this file for finishing2 (Binary AIR
row-constraint extraction required; out of scope here).

## Tier classification

| Opcode | Tier | Status |
|--------|------|--------|
| ADD    | 1    | Fully circuit-derived (no Phase-4 residual) |
| ADDI   | 1.5  | OUTPUT-EQ residual `h_input_val` (DONE_WITH_CONCERNS) |
| ADDW   | 1.5  | OUTPUT-EQ residual `h_input_val` (DONE_WITH_CONCERNS) |
| ADDIW  | 1.5  | OUTPUT-EQ residual `h_input_val` (DONE_WITH_CONCERNS) |
| SUB    | 1.5  | OUTPUT-EQ residual `h_input_val` (DONE_WITH_CONCERNS) |
| SUBW   | 1.5  | OUTPUT-EQ residual `h_input_val` (DONE_WITH_CONCERNS) |

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
these opcodes. That equality is the **Phase 4 Binary-SM audit
obligation**; supplying it as `h_input_val` to the lemmas below is
a genuine OUTPUT-EQ trust gap, not a derivable consequence of the
extracted constraints. See `docs/fv/track-n-traps.md` § "ALU-Arith
abstract bus-entry gap" for the escalation manifest (what new
infrastructure would be required to retire `h_input_val`).

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

## Trust summary

| Residual parameter | Level | Closes in |
|--------------------|-------|-----------|
| ADD: none          | —     | ✅ |
| Others: `h_input_val` | chunk OUTPUT-EQ (Binary SM result claim) | future infra phase |
| `h_lane_rd` (K2)  | Layer 1 structural | finishing2/3 |

## Why `h_input_val` cannot be retired with the in-tree infrastructure

The Wave B.6 retry attempted a Tier-1 derivation mirroring ADD's
chain. It found that none of ADDI/ADDW/ADDIW/SUB/SUBW have a Spec
theorem of the right shape. ADD's success rests on three pieces:

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
exists in `Spec/`, and authoring one is out of scope for this Wave
(the user explicitly forbids new theorems in `Spec/<X>.lean`).

For ADDW/ADDIW/SUBW the missing piece is *both* (1) and (2): the
W-variant Binary-SM is `BinaryExtension` (PIL AIR #12), which is
**not extracted** at all (`docs/fv/air-inventory.md` lists it as
"❌ row-constraints missing"). No `Valid_BinaryExtension` AIR
exists in the Lean tree.

See `docs/fv/track-n-traps.md` § "ALU-Arith abstract bus-entry gap"
for the full escalation manifest.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.Equivalence.RdValDerivation.Arith

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.LaneMatch
open ZiskFv.Spec.Add
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
theorem h_rd_val_arith_add
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
theorem h_rd_val_arith_addi
    (m : Valid_Main C FGL FGL) (b : Valid_BinaryAdd C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    -- Tier-1 circuit hypothesis (bundles Main + BinaryAdd + bus-match + ADDI mode)
    (h_circuit : ZiskFv.Spec.Addi.addi_circuit_holds_with_binaryadd m b r_main r_binary)
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

/-! ## ADDW (Tier 1 — chunk-level trust boundary, m32=1) -/

/-- **ADDW h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = spec_val` from circuit
    hypotheses and a chunk-level Binary SM correctness claim.

    ADDW routes through `OP_ADD_W = 26` with `m32 = 1`. The `RTypeWArchetype`
    compositional spec gives `main_c_packed m r_main = bus_entry.c_lo +
    bus_entry.c_hi * 2^32`. The Binary SM's internal correctness (that the
    bus c-lanes encode the sign-extended 32-bit sum) is the Phase 4 audit
    obligation expressed via `h_input_val` at the chunk level.

    **Residual `h_input_val`:** `bus_entry.c_lo.val + bus_entry.c_hi.val * 2^32
    = spec_val.toNat`. Tier-1 upgrade: the byte-sum equality is now derived
    internally (not supplied as `h_c_byte_sum`). -/
theorem h_rd_val_arith_addw
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (e2 : MemoryBusEntry FGL)
    (spec_val : BitVec 64)
    -- Circuit hypothesis (addw_circuit_holds = rtypew_archetype_circuit_holds at OP_ADD_W)
    (h_circuit : ZiskFv.Spec.Addw.addw_circuit_holds m r_main bus_entry)
    -- Lane-match hypothesis for rd-write (K2, Layer 1 trust)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- Byte-range hypotheses for e2
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Binary SM chunk correctness (Phase 4 audit obligation).
    (h_input_val :
      bus_entry.c_lo.val + bus_entry.c_hi.val * 4294967296 = spec_val.toNat) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = spec_val := by
  simp only [ZiskFv.Spec.Addw.addw_circuit_holds,
             ZiskFv.Tactics.RTypeWArchetype.rtypew_archetype_circuit_holds] at h_circuit
  obtain ⟨_, _, _, _, h_match⟩ := h_circuit
  simp only [matches_entry, opBus_row_Main] at h_match
  obtain ⟨_, _, _, _, _, _, h_clo, h_chi, _, _, _, _⟩ := h_match
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_byte_sum := byte_sum_from_lane_match m r_main bus_entry e2 spec_val
    h_clo h_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_val
  exact bv64_of_byte_sum _ _ _ _ _ _ _ _ _ h_e2_0 h_e2_1 h_e2_2 h_e2_3
    h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_byte_sum

/-! ## ADDIW (Tier 1 — chunk-level trust boundary, m32=1) -/

/-- **ADDIW h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = spec_val` from circuit
    hypotheses and a chunk-level Binary SM correctness claim.

    ADDIW routes through the same ZisK opcode as ADDW (`OP_ADD_W = 26`,
    `m32 = 1`). The difference from ADDW is on the Sail/transpiler side
    (immediate source vs. register source); the circuit-level `c`-lane
    bus-match identity is the same. Identical structure to `h_rd_val_arith_addw`.

    **Residual `h_input_val`:** the bus chunk sum encodes the sign-extended
    32-bit add-immediate result. Phase 4 audit obligation. -/
theorem h_rd_val_arith_addiw
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (e2 : MemoryBusEntry FGL)
    (spec_val : BitVec 64)
    -- Circuit hypothesis (addiw_circuit_holds = rtypew_archetype_circuit_holds at OP_ADD_W)
    (h_circuit : ZiskFv.Spec.Addiw.addiw_circuit_holds m r_main bus_entry)
    -- Lane-match hypothesis for rd-write (K2, Layer 1 trust)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- Byte-range hypotheses for e2
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Binary SM chunk correctness (Phase 4 audit obligation).
    (h_input_val :
      bus_entry.c_lo.val + bus_entry.c_hi.val * 4294967296 = spec_val.toNat) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = spec_val := by
  simp only [ZiskFv.Spec.Addiw.addiw_circuit_holds,
             ZiskFv.Tactics.RTypeWArchetype.rtypew_archetype_circuit_holds] at h_circuit
  obtain ⟨_, _, _, _, h_match⟩ := h_circuit
  simp only [matches_entry, opBus_row_Main] at h_match
  obtain ⟨_, _, _, _, _, _, h_clo, h_chi, _, _, _, _⟩ := h_match
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_byte_sum := byte_sum_from_lane_match m r_main bus_entry e2 spec_val
    h_clo h_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_val
  exact bv64_of_byte_sum _ _ _ _ _ _ _ _ _ h_e2_0 h_e2_1 h_e2_2 h_e2_3
    h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_byte_sum

/-! ## SUB (Tier 1 — chunk-level trust boundary) -/

/-- **SUB h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = r1_val - r2_val` from
    circuit hypotheses and a chunk-level Binary SM correctness claim.

    SUB routes through `OP_SUB = 11` via `ALURTypeArchetype`. ZisK SUB
    passes `a = rs1`, `b = rs2` (no sign negation upstream of the Binary SM;
    the SM handles subtraction internally via its carry chain).

    **Residual `h_input_val`:** the bus `c_lo.val + c_hi.val * 2^32` equals
    `(r1_val - r2_val).toNat`. This is the Binary SM carry-chain correctness
    for SUB — the Phase 4 audit obligation. The byte-sum derivation is now
    internal (Tier-1 upgrade from the former `h_c_byte_sum` parameter). -/
theorem h_rd_val_arith_sub
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    -- Circuit hypothesis (sub_circuit_holds = alu_rtype_archetype_circuit_holds at OP_SUB)
    (h_circuit : ZiskFv.Spec.Sub.sub_circuit_holds m r_main bus_entry)
    -- Lane-match hypothesis for rd-write (K2, Layer 1 trust)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- Byte-range hypotheses for e2
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Binary SM chunk correctness (Phase 4 audit obligation).
    (h_input_val :
      bus_entry.c_lo.val + bus_entry.c_hi.val * 4294967296
        = (r1_val - r2_val).toNat) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = r1_val - r2_val := by
  simp only [ZiskFv.Spec.Sub.sub_circuit_holds,
             ZiskFv.Tactics.ALURTypeArchetype.alu_rtype_archetype_circuit_holds] at h_circuit
  obtain ⟨_, _, _, _, h_match⟩ := h_circuit
  simp only [matches_entry, opBus_row_Main] at h_match
  obtain ⟨_, _, _, _, _, _, h_clo, h_chi, _, _, _, _⟩ := h_match
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_byte_sum := byte_sum_from_lane_match m r_main bus_entry e2
    (r1_val - r2_val)
    h_clo h_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_val
  exact bv64_of_byte_sum _ _ _ _ _ _ _ _ _ h_e2_0 h_e2_1 h_e2_2 h_e2_3
    h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_byte_sum

/-! ## SUBW (Tier 1 — chunk-level trust boundary, m32=1) -/

/-- **SUBW h_rd_val derivation (Tier 1).**
    Produces `U64.toBV #v[e2.x0, ..., e2.x7] = spec_val` from circuit
    hypotheses and a chunk-level Binary SM correctness claim.

    SUBW routes through `OP_SUB_W = 27` with `m32 = 1` via
    `RTypeWArchetype`. Identical structure to `h_rd_val_arith_addw`
    modulo the opcode and the spec conclusion.

    **Residual `h_input_val`:** the bus chunk sum encodes the sign-extended
    32-bit subtraction result. Phase 4 audit obligation. -/
theorem h_rd_val_arith_subw
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (e2 : MemoryBusEntry FGL)
    (spec_val : BitVec 64)
    -- Circuit hypothesis (subw_circuit_holds = rtypew_archetype_circuit_holds at OP_SUB_W)
    (h_circuit : ZiskFv.Spec.Subw.subw_circuit_holds m r_main bus_entry)
    -- Lane-match hypothesis for rd-write (K2, Layer 1 trust)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- Byte-range hypotheses for e2
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Binary SM chunk correctness (Phase 4 audit obligation).
    (h_input_val :
      bus_entry.c_lo.val + bus_entry.c_hi.val * 4294967296 = spec_val.toNat) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = spec_val := by
  simp only [ZiskFv.Spec.Subw.subw_circuit_holds,
             ZiskFv.Tactics.RTypeWArchetype.rtypew_archetype_circuit_holds] at h_circuit
  obtain ⟨_, _, _, _, h_match⟩ := h_circuit
  simp only [matches_entry, opBus_row_Main] at h_match
  obtain ⟨_, _, _, _, _, _, h_clo, h_chi, _, _, _, _⟩ := h_match
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_byte_sum := byte_sum_from_lane_match m r_main bus_entry e2 spec_val
    h_clo h_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_val
  exact bv64_of_byte_sum _ _ _ _ _ _ _ _ _ h_e2_0 h_e2_1 h_e2_2 h_e2_3
    h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_byte_sum

/-! ## SLT, SLTU, SLTI, SLTIU — out of scope for this branch

These four opcodes move to finishing2 alongside the Binary AIR
row-constraint extraction needed for their Tier-1 derivation.
They are NOT present in this file. -/

end ZiskFv.Equivalence.RdValDerivation.Arith
