import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.BinaryExtensionTable
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Equivalence.RdValDerivation.Arith

/-!
# RdValDerivation.BinaryShift — Tier-1 `h_rd_val` discharges for SLL/SLLI/SRL/SRLI/SRA/SRAI/SRLW/SRLIW/SLLW/SLLIW/SRAW/SRAIW

Twelve Tier-1 lemmas covering the RV64I logical/arithmetic shift
opcodes routed through ZisK's `BinaryExtension` AIR with full byte
semantics in the trusted `BinaryExtensionTable.wf_SLL` / `wf_SRL` /
`wf_SRA` / `wf_SRL_W` / `wf_SLL_W` / `wf_SRA_W` clauses.

## Architecture (Tier 1, fully circuit-derived)

Each lemma combines:

1. **K1-C BitVec lift** (`binary_extension_{sll,srl}_chunks_eq_bv_{shl,ushr}`
   in `Airs/Binary/BinaryExtensionPackedCorrect.lean`) — converts the 8
   byte-level lookup-table entries against the BinaryExtensionTable into a
   64-bit `BitVec.shiftLeft` / `BitVec.ushiftRight` identity on the packed
   byte sums of `Valid_BinaryExtension`'s `free_in_a_*` and
   `free_in_c_*` (lo/hi halves) cells.
2. **Operation-bus c-lane match** — pinning Main's `c_0`/`c_1` lanes to the
   `Valid_BinaryExtension` row's packed `c_lo` / `c_hi` byte sums.
3. **Memory-bus rd-write lane match** (`register_write_lanes_match`) —
   pinning Main's `c_0`/`c_1` lanes to the rd-write `MemoryBusEntry`'s
   `memory_entry_lo` / `memory_entry_hi`.
4. **Transpile bridges (input side)** — `r1_val` matches `Valid_BinaryExtension`'s
   packed 8-byte input; the shift amount on the Sail side equals
   `(v.free_in_b r_binary).val % 64` (applied via the RV64 mask).

The conclusion `U64.toBV #v[e2.x0..7] = r1_val <<< (...)` (resp. `>>>`)
follows directly:

* Apply K1-C to lift byte sums → BitVec identity.
* Use input bridge to rewrite the LHS as `BitVec.shiftLeft r1_val shift`.
* Use bus-match + lane-match + byte ranges to identify the byte sum of `e2`
  with the packed `c_lo + c_hi*2^32` sum, closing via `bv64_of_byte_sum`.

No new axioms; no `sorry`; no output-equality residual hypothesis.

## Note on SLL/SLLI sharing the same Zisk opcode

ZisK's `BinaryExtension` SM dispatches SLL and SLLI through the same
opcode literal (`OP_SLL = 33`); they differ only on the Sail side in the
shift-amount source (register vs immediate). The Tier-1 lemma is the
same shape; only the `h_input_imm` form of the shift-amount transpile
bridge differs for the I-variant. Same for SRL/SRLI.

## Note on BinaryExtension's c-cell layout

BinaryExtension's `Valid_BinaryExtension` has 16 c cells: `free_in_c_0..7`
are the per-byte LOW 32-bit contributions, `free_in_c_8..15` are the per-byte
HIGH 32-bit contributions. The K1-C lift sums each half separately, so the
Main↔BinaryExtension bus identifies:

* `m.c_0 = sum of free_in_c_0..7` (low 32 bits of the shifted result)
* `m.c_1 = sum of free_in_c_8..15` (high 32 bits)

These are the analog of `Binary` AIR's per-byte c-bytes (4 bytes per
32-bit half), but for shifts each "byte" of the K1-C output is itself a
32-bit value (the bit-shifted contribution of one input byte) — they
sum, not concatenate.
-/

set_option maxHeartbeats 1600000

namespace ZiskFv.Equivalence.RdValDerivation.BinaryShift

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.BinaryExtensionTable
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.LaneMatch
open ZiskFv.PackedBitVec
open ZiskFv.Equivalence.RdValDerivation.Arith

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## SLL -/

/-- **SLL `h_rd_val` derivation (Tier 1).**

    Concludes `U64.toBV #v[e2.x0..7] = r1_val <<< (shift % 64)` from K1-C SLL
    lift, Main↔BinaryExtension bus c-lane match (the two c lanes equal the
    sums of the lo/hi byte halves of `Valid_BinaryExtension`), the rd-write
    lane match, byte ranges, and a transpile bridge identifying `r1_val`
    with the packed 8-byte input sum.

    The shift amount is taken from `(v.free_in_b r_binary).val % 64` directly
    (RV64 SLL/SLLI mask the shift amount to its low 6 bits). -/
theorem h_rd_val_shift_sll
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    -- K1-C: op is OP_SLL on this row.
    (h_op : (v.op r_binary).val = OP_SLL)
    -- K1-C: the 8 byte-lookup hypotheses against the BinaryExtensionTable.
    (h_bytes : ByteLookupHypotheses v r_binary)
    -- K1-C: input-byte ranges.
    (h_a_range : a_bytes_in_range v r_binary)
    -- Byte ranges on the c-lo / c-hi cells (needed for the Nat byte-sum lift
    -- and for the K1-C output-side identity to fit in 2^64).
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    -- Bound on the summed lo / hi values: each is < 2^32 (that's the
    -- arithmetic invariant the K1-C lift assumes; here they bridge via
    -- the bus-match identities to the Main row's `c_0` / `c_1` lanes).
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    -- Main↔BinaryExtension c-lane bus-match.
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Transpile bridge (input side): r1_val matches Valid_BinaryExtension's
    -- packed 8-byte a sum.
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    -- Transpile bridge (shift amount): the Sail shift equals the masked
    -- `free_in_b`. RV64 SLL pre-masks the rs2 register read to 6 bits.
    (h_shift : shift = (v.free_in_b r_binary).val % 64) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.shiftLeft r1_val shift := by
  -- Step 1: K1-C SLL lift.
  have h_bv := binary_extension_sll_chunks_eq_bv_shl v r_binary h_op h_bytes h_a_range
  -- Step 2: Lane-match equalities for c0/c1.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- Step 3: Identify Main's c_0/c_1 with the BinaryExtension c-lo/c-hi sums
  -- as FGL elements; lift to Nat via byte ranges.
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  -- Lift to Nat. The c-lo sum bound gives < 2^32 < GL_prime.
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
  -- The c-lo binary-side sum lift to Nat.
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
       + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
             + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
             + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
       + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
       + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
             + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
             + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  -- Step 4: Derive the e2-byte-sum equals the BinaryExtension c-lo/hi packed sum.
  have h_byte_sum_e2_to_c :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  -- Step 5: Now use K1-C's BitVec output to bridge the byte sum to the
  -- target `r1_val <<< shift`.
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.shiftLeft r1_val shift).toNat := by
    rw [h_byte_sum_e2_to_c]
    -- Goal: c-lo sum + c-hi sum * 2^32 = (r1_val <<< shift).toNat.
    rw [h_input_r1, h_shift]
    -- The RHS (BitVec.shiftLeft (BitVec.ofNat 64 sum_a) ((free_in_b).val % 64))
    -- equals h_bv's LHS, and h_bv equates that to BitVec.ofNat 64 (lo + hi*2^32).
    -- Take .toNat of both, use BitVec.toNat_ofNat plus the byte-sum bound.
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    -- Goal: c-lo + c-hi*2^32 = (c-lo + c-hi*2^32) % 2^64.
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.shiftLeft r1_val shift)
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SLLI -/

/-- **SLLI `h_rd_val` derivation (Tier 1).** Same shape as `h_rd_val_shift_sll`;
    SLLI shares SLL's Zisk opcode (`OP_SLL = 33`) at the BinaryExtension SM.
    The shift amount on the Sail side is the immediate (5/6-bit shamt) rather
    than rs2; `h_shift` captures the transpile pin equating it to
    `(v.free_in_b r_binary).val % 64`. -/
theorem h_rd_val_shift_slli
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SLL)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift : shift = (v.free_in_b r_binary).val % 64) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.shiftLeft r1_val shift := by
  exact h_rd_val_shift_sll m v r_main r_binary e2 r1_val shift h_op h_bytes h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1 h_shift

/-! ## SRL -/

/-- **SRL `h_rd_val` derivation (Tier 1).** Same architecture as
    `h_rd_val_shift_sll` but with `BitVec.ushiftRight`. Uses K1-C SRL
    lift `binary_extension_srl_chunks_eq_bv_ushr`. -/
theorem h_rd_val_shift_srl
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift : shift = (v.free_in_b r_binary).val % 64) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.ushiftRight r1_val shift := by
  have h_bv := binary_extension_srl_chunks_eq_bv_ushr v r_binary h_op h_bytes h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary := by
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
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
       + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
             + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
             + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
       + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
       + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
             + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
             + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.ushiftRight r1_val shift).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.ushiftRight r1_val shift)
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SRLI -/

/-- **SRLI `h_rd_val` derivation (Tier 1).** Same shape as `h_rd_val_shift_srl`;
    SRLI shares SRL's Zisk opcode (`OP_SRL = 34`) at the BinaryExtension SM. -/
theorem h_rd_val_shift_srli
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift : shift = (v.free_in_b r_binary).val % 64) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.ushiftRight r1_val shift := by
  exact h_rd_val_shift_srl m v r_main r_binary e2 r1_val shift h_op h_bytes h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1 h_shift

/-! ## SRA -/

/-- **SRA `h_rd_val` derivation (Tier 1).** Same architecture as
    `h_rd_val_shift_sll`/`_srl` but with `BitVec.sshiftRight`. Uses K1-C SRA
    lift `binary_extension_sra_chunks_eq_bv_sshr`. RV64 SRA pre-masks the
    rs2 register read to 6 bits. -/
theorem h_rd_val_shift_sra
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift : shift = (v.free_in_b r_binary).val % 64) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.sshiftRight r1_val shift := by
  have h_bv := binary_extension_sra_chunks_eq_bv_sshr v r_binary h_op h_bytes h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary := by
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
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
       + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
             + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
             + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
       + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
       + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
             + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
             + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.sshiftRight r1_val shift).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.sshiftRight r1_val shift)
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SRAI -/

/-- **SRAI `h_rd_val` derivation (Tier 1).** Same shape as `h_rd_val_shift_sra`;
    SRAI shares SRA's Zisk opcode (`OP_SRA = 35`) at the BinaryExtension SM.
    The shift amount on the Sail side is the immediate (5/6-bit shamt) rather
    than rs2; `h_shift` captures the transpile pin equating it to
    `(v.free_in_b r_binary).val % 64`. -/
theorem h_rd_val_shift_srai
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_shift : shift = (v.free_in_b r_binary).val % 64) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.sshiftRight r1_val shift := by
  exact h_rd_val_shift_sra m v r_main r_binary e2 r1_val shift h_op h_bytes h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1 h_shift

/-! ## SRLW -/

/-- **SRLW `h_rd_val` derivation (Tier 1).** W-mode unsigned shift right:
    take the low 32 bits of `r1_val`, shift right (logical) by the low 5
    bits of `r2_val`, sign-extend the 32-bit result back to 64. Uses K1-C
    SRLW lift `binary_extension_srlw_chunks_eq_bv_ushr_w`.

    The lemma takes `r1_val_lo32 : BitVec 32` directly with a transpile
    bridge to `BitVec.ofNat 32 (sum a_lo)`. The shift amount on the Sail
    side equals `(v.free_in_b r_binary).val % 32` — RV64 SRLW pre-masks
    the rs2 register read to 5 bits. -/
theorem h_rd_val_shift_srlw
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Transpile bridge (input side, low 32): `r1_val_lo32` matches the
    -- BinaryExtension row's packed 4-byte low input.
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift) := by
  have h_bv := binary_extension_srlw_chunks_eq_bv_ushr_w v r_binary h_op h_bytes h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary := by
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
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
       + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
             + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
             + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
       + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
       + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
             + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
             + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift)).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1_lo32, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift))
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SRLIW -/

/-- **SRLIW `h_rd_val` derivation (Tier 1).** Same shape as `h_rd_val_shift_srlw`;
    SRLIW shares SRLW's Zisk opcode (`OP_SRL_W = 37`) at the BinaryExtension SM.
    The shift amount on the Sail side is the immediate (5-bit shamt) rather
    than rs2; `h_shift` captures the transpile pin equating it to
    `(v.free_in_b r_binary).val % 32`. -/
theorem h_rd_val_shift_srliw
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift) := by
  exact h_rd_val_shift_srlw m v r_main r_binary e2 r1_val_lo32 shift h_op h_bytes h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1_lo32 h_shift

/-! ## SLLW -/

/-- **SLLW `h_rd_val` derivation (Tier 1).** W-mode left shift:
    take the low 32 bits of `r1_val`, shift left by the low 5 bits of
    `r2_val`, sign-extend the 32-bit result back to 64. Uses K1-C SLLW
    lift `binary_extension_sllw_chunks_eq_bv_shl_w`.

    The lemma takes `r1_val_lo32 : BitVec 32` directly with a transpile
    bridge to `BitVec.ofNat 32 (sum a_lo)`. The shift amount on the Sail
    side equals `(v.free_in_b r_binary).val % 32` — RV64 SLLW pre-masks
    the rs2 register read to 5 bits. -/
theorem h_rd_val_shift_sllw
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SLL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Transpile bridge (input side, low 32): `r1_val_lo32` matches the
    -- BinaryExtension row's packed 4-byte low input.
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift) := by
  have h_bv := binary_extension_sllw_chunks_eq_bv_shl_w v r_binary h_op h_bytes h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary := by
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
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
       + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
             + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
             + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
       + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
       + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
             + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
             + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift)).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1_lo32, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift))
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SLLIW -/

/-- **SLLIW `h_rd_val` derivation (Tier 1).** Same shape as `h_rd_val_shift_sllw`;
    SLLIW shares SLLW's Zisk opcode (`OP_SLL_W = 36`) at the BinaryExtension SM.
    The shift amount on the Sail side is the immediate (5-bit shamt) rather
    than rs2; `h_shift` captures the transpile pin equating it to
    `(v.free_in_b r_binary).val % 32`. -/
theorem h_rd_val_shift_slliw
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SLL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift) := by
  exact h_rd_val_shift_sllw m v r_main r_binary e2 r1_val_lo32 shift h_op h_bytes h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1_lo32 h_shift

/-! ## SRAW -/

/-- **SRAW `h_rd_val` derivation (Tier 1).** W-mode signed shift right:
    take the low 32 bits of `r1_val`, shift right (arithmetic) by the low
    5 bits of `r2_val`, sign-extend the 32-bit result back to 64. Uses
    K1-C SRAW lift `binary_extension_sraw_chunks_eq_bv_sshr_w`.

    The lemma takes `r1_val_lo32 : BitVec 32` directly with a transpile
    bridge to `BitVec.ofNat 32 (sum a_lo)`. The shift amount on the Sail
    side equals `(v.free_in_b r_binary).val % 32` — RV64 SRAW pre-masks
    the rs2 register read to 5 bits. -/
theorem h_rd_val_shift_sraw
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    -- Transpile bridge (input side, low 32): `r1_val_lo32` matches the
    -- BinaryExtension row's packed 4-byte low input.
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift) := by
  have h_bv := binary_extension_sraw_chunks_eq_bv_sshr_w v r_binary h_op h_bytes h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary := by
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
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
       + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
       + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
        + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
        + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
             + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
             + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
       + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
       + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
        + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
        + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
             + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
             + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift)).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1_lo32, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
          + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
          + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val)
        + ((v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
          + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
          + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift))
    e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-! ## SRAIW -/

/-- **SRAIW `h_rd_val` derivation (Tier 1).** Same shape as `h_rd_val_shift_sraw`;
    SRAIW shares SRAW's Zisk opcode (`OP_SRA_W = 38`) at the BinaryExtension SM.
    The shift amount on the Sail side is the immediate (5-bit shamt) rather
    than rs2; `h_shift` captures the transpile pin equating it to
    `(v.free_in_b r_binary).val % 32`. -/
theorem h_rd_val_shift_sraiw
    (m : Valid_Main C FGL FGL) (v : Valid_BinaryExtension C FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val
        + (v.free_in_c_2 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val
        + (v.free_in_c_6 r_binary).val + (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_8 r_binary).val + (v.free_in_c_9 r_binary).val
        + (v.free_in_c_10 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_13 r_binary).val
        + (v.free_in_c_14 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary
          + v.free_in_c_2 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_5 r_binary
          + v.free_in_c_6 r_binary + v.free_in_c_7 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_8 r_binary + v.free_in_c_9 r_binary
          + v.free_in_c_10 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_13 r_binary
          + v.free_in_c_14 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : e2.x0.val < 256) (h_e2_1 : e2.x1.val < 256)
    (h_e2_2 : e2.x2.val < 256) (h_e2_3 : e2.x3.val < 256)
    (h_e2_4 : e2.x4.val < 256) (h_e2_5 : e2.x5.val < 256)
    (h_e2_6 : e2.x6.val < 256) (h_e2_7 : e2.x7.val < 256)
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift) := by
  exact h_rd_val_shift_sraw m v r_main r_binary e2 r1_val_lo32 shift h_op h_bytes h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1_lo32 h_shift

end ZiskFv.Equivalence.RdValDerivation.BinaryShift
