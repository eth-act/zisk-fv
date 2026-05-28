import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.Airs.Tables.BinaryExtensionTable
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.WriteValueProofs.Arith

/-!
# WriteValueProofs.BinaryShift — Tier-1 `h_rd_val` discharges for SLL/SLLI/SRL/SRLI/SRA/SRAI/SRLW/SRLIW/SLLW/SLLIW/SRAW/SRAIW

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

The conclusion `U64.toBV #v[(byteAt e2 0)..7] = r1_val <<< (...)` (resp. `>>>`)
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
are the per-byte LOW 32-bit contributions, `free_in_c_1..15` are the per-byte
HIGH 32-bit contributions. The K1-C lift sums each half separately, so the
Main↔BinaryExtension bus identifies:

* `m.c_0 = sum of free_in_c_0..7` (low 32 bits of the shifted result)
* `m.c_1 = sum of free_in_c_1..15` (high 32 bits)

These are the analog of `Binary` AIR's per-byte c-bytes (4 bytes per
32-bit half), but for shifts each "byte" of the K1-C output is itself a
32-bit value (the bit-shifted contribution of one input byte) — they
sum, not concatenate.
-/

set_option maxHeartbeats 1600000

namespace ZiskFv.EquivCore.WriteValueProofs.BinaryShift

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf)
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryExtension
open ZiskFv.Airs.Tables.BinaryExtensionTable
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.PackedBitVec
open ZiskFv.EquivCore.WriteValueProofs.Arith

/-! ## Chunk → byte-sum equalities (chunk-shape `MemoryBusEntry` bridge)

After the C8 Phase 2 cutover, `memory_entry_lo e2 = e2.value_0` and
`memory_entry_hi e2 = e2.value_1`. The byte sum of the 4 byte
projections of each chunk recovers the chunk's `.val` via
`ZiskFv.Channels.MemoryBusBytes.byteOf_val_sum_eq` composed with a local
bound derived from the same c-lane equality used by the shift proof.

These private helpers mirror the same-named helpers in
`EquivCore/WriteValueProofs/Arith.lean` (private there, replicated
here to keep BinaryShift self-contained). -/

private lemma byteAt_lo_val_sum_eq (e : MemoryBusEntry FGL)
    (h : e.value_0.val < 4294967296) :
    (byteAt e 0).val + (byteAt e 1).val * 256
      + (byteAt e 2).val * 65536 + (byteAt e 3).val * 16777216
    = e.value_0.val := by
  have hb0 : byteAt e 0 = byteOf e.value_0 0 := by
    unfold byteAt; simp only [show (0 : ℕ) < 4 from by decide, if_true]
  have hb1 : byteAt e 1 = byteOf e.value_0 1 := by
    unfold byteAt; simp only [show (1 : ℕ) < 4 from by decide, if_true]
  have hb2 : byteAt e 2 = byteOf e.value_0 2 := by
    unfold byteAt; simp only [show (2 : ℕ) < 4 from by decide, if_true]
  have hb3 : byteAt e 3 = byteOf e.value_0 3 := by
    unfold byteAt; simp only [show (3 : ℕ) < 4 from by decide, if_true]
  rw [hb0, hb1, hb2, hb3]
  exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_sum_eq e.value_0
          h

private lemma byteAt_hi_val_sum_eq (e : MemoryBusEntry FGL)
    (h : e.value_1.val < 4294967296) :
    (byteAt e 4).val + (byteAt e 5).val * 256
      + (byteAt e 6).val * 65536 + (byteAt e 7).val * 16777216
    = e.value_1.val := by
  have hb4 : byteAt e 4 = byteOf e.value_1 0 := by
    unfold byteAt; simp only [show ¬ (4 : ℕ) < 4 from by decide, if_false]
  have hb5 : byteAt e 5 = byteOf e.value_1 1 := by
    unfold byteAt; simp only [show ¬ (5 : ℕ) < 4 from by decide, if_false]
  have hb6 : byteAt e 6 = byteOf e.value_1 2 := by
    unfold byteAt; simp only [show ¬ (6 : ℕ) < 4 from by decide, if_false]
  have hb7 : byteAt e 7 = byteOf e.value_1 3 := by
    unfold byteAt; simp only [show ¬ (7 : ℕ) < 4 from by decide, if_false]
  rw [hb4, hb5, hb6, hb7]
  exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_sum_eq e.value_1 h

private lemma memory_entry_lo_bound_of_shift_sum
    (e : MemoryBusEntry FGL)
    (c0 c1 c2 c3 c4 c5 c6 c7 : FGL)
    (h_eq : memory_entry_lo e = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (h_sum_lt : c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val
      < 4294967296) :
    e.value_0.val < 4294967296 := by
  have h_sum_val :
      (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 : FGL).val
        = c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val := by
    have h_cast :
        c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7
          = ((((c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val : ℕ) : FGL))) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_val := congrArg Fin.val h_eq
  simp only [memory_entry_lo] at h_val
  rw [h_sum_val] at h_val
  omega

private lemma memory_entry_hi_bound_of_shift_sum
    (e : MemoryBusEntry FGL)
    (c0 c1 c2 c3 c4 c5 c6 c7 : FGL)
    (h_eq : memory_entry_hi e = c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7)
    (h_sum_lt : c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val
      < 4294967296) :
    e.value_1.val < 4294967296 := by
  have h_sum_val :
      (c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 : FGL).val
        = c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val := by
    have h_cast :
        c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7
          = ((((c0.val + c1.val + c2.val + c3.val + c4.val + c5.val + c6.val + c7.val : ℕ) : FGL))) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have h_val := congrArg Fin.val h_eq
  simp only [memory_entry_hi] at h_val
  rw [h_sum_val] at h_val
  omega


/-! ## SLL -/

/-- **SLL `h_rd_val` derivation (Tier 1).**

    Concludes `U64.toBV #v[(byteAt e2 0)..7] = r1_val <<< (shift % 64)` from K1-C SLL
    lift, Main↔BinaryExtension bus c-lane match (the two c lanes equal the
    sums of the lo/hi byte halves of `Valid_BinaryExtension`), the rd-write
    lane match, byte ranges, and a transpile bridge identifying `r1_val`
    with the packed 8-byte input sum.

    The shift amount is taken from `(v.free_in_b r_binary).val % 64` directly
    (RV64 SLL/SLLI mask the shift amount to its low 6 bits). -/
lemma h_rd_val_shift_sll_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    -- K1-C: op is OP_SLL on this row.
    (h_op : (v.op r_binary).val = OP_SLL)
    -- K1-C: the 8 byte-lookup hypotheses against the BinaryExtensionTable.
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    -- K1-C: input-byte ranges.
    (h_a_range : a_bytes_in_range v r_binary)
    -- Byte ranges on the c-lo / c-hi cells (needed for the Nat byte-sum lift
    -- and for the K1-C output-side identity to fit in 2^64).
    (_hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (_hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (_hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (_hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (_hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (_hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (_hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (_hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (_hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (_hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (_hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (_hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (_hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (_hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (_hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (_hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    -- Bound on the summed lo / hi values: each is < 2^32 (that's the
    -- arithmetic invariant the K1-C lift assumes; here they bridge via
    -- the bus-match identities to the Main row's `c_0` / `c_1` lanes).
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    -- Main↔BinaryExtension c-lane bus-match.
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
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
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.shiftLeft r1_val shift := by
  -- K1-C SLL lift.
  have h_bv := binary_extension_sll_chunks_eq_bv_shl_of_wf v r_binary h_op h_bytes h_wfs h_a_range
  -- Lane-match equalities for c0/c1.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- Identify Main's c_0/c_1 with the BinaryExtension c-lo/c-hi sums
  -- as FGL elements; lift to Nat via byte ranges.
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  -- Lift to Nat. The c-lo sum bound gives < 2^32 < GL_prime.
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_shift_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_shift_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256 + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  -- The c-lo binary-side sum lift to Nat.
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  -- Derive the e2-byte-sum equals the BinaryExtension c-lo/hi packed sum.
  have h_byte_sum_e2_to_c :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  -- Now use K1-C's BitVec output to bridge the byte sum to the
  -- target `r1_val <<< shift`.
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
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
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.shiftLeft r1_val shift)
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3) (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

-- legacy h_rd_val_shift_sll (bin_ext_table_consumer_wf route) deleted in T4-purge P3.4.

lemma h_rd_val_shift_slli_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SLL)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
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
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.shiftLeft r1_val shift := by
  exact h_rd_val_shift_sll_of_wf m v r_main r_binary e2 r1_val shift h_op h_bytes h_wfs h_a_range
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
lemma h_rd_val_shift_srl_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (_hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (_hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (_hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (_hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (_hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (_hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (_hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (_hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (_hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (_hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (_hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (_hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (_hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (_hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (_hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (_hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
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
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.ushiftRight r1_val shift := by
  have h_bv := binary_extension_srl_chunks_eq_bv_ushr_of_wf v r_binary h_op h_bytes h_wfs h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_shift_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_shift_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256 + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.ushiftRight r1_val shift).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.ushiftRight r1_val shift)
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3) (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

-- legacy h_rd_val_shift_srl (bin_ext_table_consumer_wf route) deleted in T4-purge P3.4.

lemma h_rd_val_shift_srli_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
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
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.ushiftRight r1_val shift := by
  exact h_rd_val_shift_srl_of_wf m v r_main r_binary e2 r1_val shift h_op h_bytes h_wfs h_a_range
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
lemma h_rd_val_shift_sra_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (_hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (_hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (_hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (_hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (_hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (_hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (_hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (_hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (_hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (_hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (_hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (_hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (_hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (_hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (_hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (_hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
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
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.sshiftRight r1_val shift := by
  have h_bv := binary_extension_sra_chunks_eq_bv_sshr_of_wf v r_binary h_op h_bytes h_wfs h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_shift_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_shift_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256 + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.sshiftRight r1_val shift).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.sshiftRight r1_val shift)
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3) (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

-- legacy h_rd_val_shift_sra (bin_ext_table_consumer_wf route) deleted in T4-purge P3.4.

lemma h_rd_val_shift_srai_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
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
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.sshiftRight r1_val shift := by
  exact h_rd_val_shift_sra_of_wf m v r_main r_binary e2 r1_val shift h_op h_bytes h_wfs h_a_range
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
lemma h_rd_val_shift_srlw_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (_hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (_hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (_hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (_hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (_hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (_hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (_hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (_hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (_hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (_hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (_hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (_hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (_hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (_hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (_hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (_hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    -- Transpile bridge (input side, low 32): `r1_val_lo32` matches the
    -- BinaryExtension row's packed 4-byte low input.
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift) := by
  have h_bv := binary_extension_srlw_chunks_eq_bv_ushr_w_of_wf v r_binary h_op h_bytes h_wfs h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_shift_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_shift_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256 + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift)).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1_lo32, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift))
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3) (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

-- legacy h_rd_val_shift_srlw (bin_ext_table_consumer_wf route) deleted in T4-purge P3.4.

lemma h_rd_val_shift_srliw_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.ushiftRight r1_val_lo32 shift) := by
  exact h_rd_val_shift_srlw_of_wf m v r_main r_binary e2 r1_val_lo32 shift h_op h_bytes h_wfs h_a_range
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
lemma h_rd_val_shift_sllw_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SLL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (_hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (_hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (_hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (_hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (_hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (_hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (_hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (_hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (_hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (_hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (_hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (_hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (_hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (_hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (_hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (_hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    -- Transpile bridge (input side, low 32): `r1_val_lo32` matches the
    -- BinaryExtension row's packed 4-byte low input.
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift) := by
  have h_bv := binary_extension_sllw_chunks_eq_bv_shl_w_of_wf v r_binary h_op h_bytes h_wfs h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_shift_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_shift_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256 + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift)).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1_lo32, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift))
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3) (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

-- legacy h_rd_val_shift_sllw (bin_ext_table_consumer_wf route) deleted in T4-purge P3.4.

lemma h_rd_val_shift_slliw_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SLL_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.shiftLeft r1_val_lo32 shift) := by
  exact h_rd_val_shift_sllw_of_wf m v r_main r_binary e2 r1_val_lo32 shift h_op h_bytes h_wfs h_a_range
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
lemma h_rd_val_shift_sraw_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (_hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (_hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (_hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (_hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (_hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (_hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (_hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (_hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (_hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (_hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (_hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (_hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (_hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (_hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (_hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (_hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    -- Transpile bridge (input side, low 32): `r1_val_lo32` matches the
    -- BinaryExtension row's packed 4-byte low input.
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift) := by
  have h_bv := binary_extension_sraw_chunks_eq_bv_sshr_w_of_wf v r_binary h_op h_bytes h_wfs h_a_range
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_lo_eq_fgl : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq_fgl : memory_entry_hi e2
      = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary := by
    rw [← h_hi_match, h_match_chi]
  have h_v0_lt : e2.value_0.val < 4294967296 :=
    memory_entry_lo_bound_of_shift_sum e2
      (v.free_in_c_0 r_binary) (v.free_in_c_2 r_binary)
      (v.free_in_c_4 r_binary) (v.free_in_c_6 r_binary)
      (v.free_in_c_8 r_binary) (v.free_in_c_10 r_binary)
      (v.free_in_c_12 r_binary) (v.free_in_c_14 r_binary)
      h_lo_eq_fgl hc_lo_sum_lt
  have h_v1_lt : e2.value_1.val < 4294967296 :=
    memory_entry_hi_bound_of_shift_sum e2
      (v.free_in_c_1 r_binary) (v.free_in_c_3 r_binary)
      (v.free_in_c_5 r_binary) (v.free_in_c_7 r_binary)
      (v.free_in_c_9 r_binary) (v.free_in_c_11 r_binary)
      (v.free_in_c_13 r_binary) (v.free_in_c_15 r_binary)
      h_hi_eq_fgl hc_hi_sum_lt
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_v0_lt).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256 + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_v1_lt).symm
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
       + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
       + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
       + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
        + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
        + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
        + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
             + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
             + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
             + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_hi_bin_nat :
      (v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
       + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
       + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
       + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary : FGL).val
      = (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val := by
    have h_cast :
        v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
        + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
        + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
        + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary
        = ((((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
             + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
             + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
             + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; show _ < 18446744069414584321; omega
  have h_lo_val := congr_arg Fin.val h_lo_eq_fgl
  have h_hi_val := congr_arg Fin.val h_hi_eq_fgl
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  have h_byte_sum_e2_to_c :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val)
          * 4294967296 := by
    omega
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift)).toNat := by
    rw [h_byte_sum_e2_to_c]
    rw [h_input_r1_lo32, h_shift]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt : ((v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
          + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
          + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
          + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val)
        + ((v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
          + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
          + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
          + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val) * 4294967296
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift))
    (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3) (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

-- legacy h_rd_val_shift_sraw (bin_ext_table_consumer_wf route) deleted in T4-purge P3.4.

lemma h_rd_val_shift_sraiw_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_BinaryExtension FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val_lo32 : BitVec 32) (shift : ℕ)
    (h_op : (v.op r_binary).val = OP_SRA_W)
    (h_bytes : ByteLookupHypotheses v r_binary)
    (h_wfs : ByteLookupWfHypotheses h_bytes)
    (h_a_range : a_bytes_in_range v r_binary)
    (hc_lo_0 : (v.free_in_c_0 r_binary).val < 4294967296)
    (hc_lo_1 : (v.free_in_c_2 r_binary).val < 4294967296)
    (hc_lo_2 : (v.free_in_c_4 r_binary).val < 4294967296)
    (hc_lo_3 : (v.free_in_c_6 r_binary).val < 4294967296)
    (hc_lo_4 : (v.free_in_c_8 r_binary).val < 4294967296)
    (hc_lo_5 : (v.free_in_c_10 r_binary).val < 4294967296)
    (hc_lo_6 : (v.free_in_c_12 r_binary).val < 4294967296)
    (hc_lo_7 : (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_0 : (v.free_in_c_1 r_binary).val < 4294967296)
    (hc_hi_1 : (v.free_in_c_3 r_binary).val < 4294967296)
    (hc_hi_2 : (v.free_in_c_5 r_binary).val < 4294967296)
    (hc_hi_3 : (v.free_in_c_7 r_binary).val < 4294967296)
    (hc_hi_4 : (v.free_in_c_9 r_binary).val < 4294967296)
    (hc_hi_5 : (v.free_in_c_11 r_binary).val < 4294967296)
    (hc_hi_6 : (v.free_in_c_13 r_binary).val < 4294967296)
    (hc_hi_7 : (v.free_in_c_15 r_binary).val < 4294967296)
    (hc_lo_sum_lt : (v.free_in_c_0 r_binary).val + (v.free_in_c_2 r_binary).val
        + (v.free_in_c_4 r_binary).val + (v.free_in_c_6 r_binary).val
        + (v.free_in_c_8 r_binary).val + (v.free_in_c_10 r_binary).val
        + (v.free_in_c_12 r_binary).val + (v.free_in_c_14 r_binary).val < 4294967296)
    (hc_hi_sum_lt : (v.free_in_c_1 r_binary).val + (v.free_in_c_3 r_binary).val
        + (v.free_in_c_5 r_binary).val + (v.free_in_c_7 r_binary).val
        + (v.free_in_c_9 r_binary).val + (v.free_in_c_11 r_binary).val
        + (v.free_in_c_13 r_binary).val + (v.free_in_c_15 r_binary).val < 4294967296)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_2 r_binary
          + v.free_in_c_4 r_binary + v.free_in_c_6 r_binary
          + v.free_in_c_8 r_binary + v.free_in_c_10 r_binary
          + v.free_in_c_12 r_binary + v.free_in_c_14 r_binary)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_1 r_binary + v.free_in_c_3 r_binary
          + v.free_in_c_5 r_binary + v.free_in_c_7 r_binary
          + v.free_in_c_9 r_binary + v.free_in_c_11 r_binary
          + v.free_in_c_13 r_binary + v.free_in_c_15 r_binary)
    (h_lane_rd : register_write_lanes_match m r_main e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_input_r1_lo32 : r1_val_lo32
      = BitVec.ofNat 32
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216))
    (h_shift : shift = (v.free_in_b r_binary).val % 32) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.signExtend 64 (BitVec.sshiftRight r1_val_lo32 shift) := by
  exact h_rd_val_shift_sraw_of_wf m v r_main r_binary e2 r1_val_lo32 shift h_op h_bytes h_wfs h_a_range
    hc_lo_0 hc_lo_1 hc_lo_2 hc_lo_3 hc_lo_4 hc_lo_5 hc_lo_6 hc_lo_7
    hc_hi_0 hc_hi_1 hc_hi_2 hc_hi_3 hc_hi_4 hc_hi_5 hc_hi_6 hc_hi_7
    hc_lo_sum_lt hc_hi_sum_lt
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1_lo32 h_shift

end ZiskFv.EquivCore.WriteValueProofs.BinaryShift
