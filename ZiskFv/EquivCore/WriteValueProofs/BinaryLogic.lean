import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryPackedCorrect
import ZiskFv.Airs.Tables.BinaryTable
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.WriteValueProofs.Arith

/-!
# WriteValueProofs.BinaryLogic — Tier-1 `h_rd_val` discharges for AND/ANDI/OR/ORI/XOR/XORI

Six Tier-1 lemmas covering the RV64I bitwise opcodes routed through
ZisK's `Binary` AIR.

## Architecture (Tier 1, fully circuit-derived)

Each lemma combines:

1. **K1-B BitVec lift** (`binary_{and,or,xor}_chunks_eq_bv_{and,or,xor}` in
   `Airs/Binary/BinaryPackedCorrect.lean`) — converts the 8 byte-level
   lookup-table entries (consumed at multiplicity 1, op = `OP_AND/OR/XOR`)
   into a 64-bit `BitVec` identity on the packed byte sums of `Valid_Binary`'s
   `free_in_a_*` / `free_in_b_*` / `free_in_c_*` cells.
2. **Operation-bus c-lane match** — pinning Main's `c_0`/`c_1` lanes to the
   `Valid_Binary` row's packed `c` byte sums (4 bytes each).
3. **Memory-bus rd-write lane match** (`register_write_lanes_match`) —
   pinning Main's `c_0`/`c_1` lanes to the rd-write `MemoryBusEntry`'s
   `memory_entry_lo`/`memory_entry_hi`.
4. **Transpile bridges (input side)** — pinning the Sail `r1_val`/`r2_val`
   to `Valid_Binary`'s packed 8-byte input sums. These bridges are the
   row-shape provenance surface (CLAUDE.md), not new axioms — they capture
   the same property the Spec/AND etc. lemmas would derive once Main↔Binary
   bus emission is wired through.

The conclusion `U64.toBV #v[(byteAt e2 0)..7] = r1_val &&& r2_val` (resp. `|||`,
`^^^`) follows directly:

* Apply K1-B to lift byte sums → BitVec identity.
* Use input bridges to rewrite the LHS as `BitVec.and r1_val r2_val`.
* Use bus-match + lane-match + byte ranges to identify the byte sum of `e2`
  with the packed `c`-sum, closing via `bv64_of_byte_sum`.

No new axioms; no `sorry`; no output-equality residual hypothesis.

## Note on AND/ANDI sharing the same Zisk opcode

ZisK's `Binary` SM dispatches AND and ANDI through the same opcode literal
(`OP_AND = 14`); the Main-side ALU-RTYPE / ALU-ITYPE archetype distinguishes
them only via the `b` source (register vs immediate). The Tier-1 lemma is
therefore the same shape for both — only the input bridge for `r2_val`
differs (rs2 register-read vs sign-extended immediate). The body is shared
via a single `_logic_and_core` helper; the AND and ANDI lemmas re-export it
with their respective input bridges. Same applies to OR/ORI and XOR/XORI.
-/

set_option maxHeartbeats 1200000

namespace ZiskFv.EquivCore.WriteValueProofs.BinaryLogic

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf)
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.Tables.BinaryTable
open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.MemoryBus
open ZiskFv.PackedBitVec
open ZiskFv.EquivCore.WriteValueProofs.Arith


/-! ## Chunk → byte-sum equalities

Mirrors the Arith.lean helpers: project a memory-bus entry's two value
chunks into per-byte sums via `byteAt` + `byteOf_val_sum_eq`. -/

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
  exact ZiskFv.Channels.MemoryBusBytes.byteOf_val_sum_eq e.value_0 h

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

/-! ## Internal kernel: byte-sum identity from c-lane bus-match + lane-match -/

/-- **Byte-sum from c-lane bus-match + lane-match (Logic variant).** Same
    role as `Arith.byte_sum_from_lane_match`, but with the c-lane match
    expressed in `Valid_Binary`'s 4-byte packed form (c bytes 0..3 for low,
    4..7 for high) rather than via an abstract `OperationBusEntry`.

    The hypotheses say:

    * `h_match_clo` : `m.c_0 r_main = v.free_in_c_0 + v.free_in_c_1*256
                                       + v.free_in_c_2*65536 + v.free_in_c_3*16777216`
    * `h_match_chi` : `m.c_1 r_main = v.free_in_c_4 + ...`
    * `h_lo_match`/`h_hi_match` : Main↔memory-entry lo/hi match.
    * Byte ranges on `e2` and on `v.free_in_c_*`.

    Derives the byte-sum equality of `e2`'s 8 bytes equals the byte-sum of
    `v.free_in_c_*`'s 8 bytes, in `Nat`. -/
private lemma byte_sum_from_binary_lane_match
    (m : Valid_Main FGL FGL)
    (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
    (h_lo_match : m.c_0 r_main = memory_entry_lo e2)
    (h_hi_match : m.c_1 r_main = memory_entry_hi e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256) :
    (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
    + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
    + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
    = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
      + (v.free_in_c_2 r_binary).val * 65536 + (v.free_in_c_3 r_binary).val * 16777216
      + (v.free_in_c_4 r_binary).val * 4294967296
      + (v.free_in_c_5 r_binary).val * 1099511627776
      + (v.free_in_c_6 r_binary).val * 281474976710656
      + (v.free_in_c_7 r_binary).val * 72057594037927936 := by
  -- identify the lo/hi packed memory entry with the binary-c lo/hi packings.
  have h_lo_eq : memory_entry_lo e2
      = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
        + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216 := by
    rw [← h_lo_match, h_match_clo]
  have h_hi_eq : memory_entry_hi e2
      = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
        + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216 := by
    rw [← h_hi_match, h_match_chi]
  have h_lo_bound : e2.value_0.val < 4294967296 := by
    change (memory_entry_lo e2).val < 4294967296
    rw [h_lo_eq]
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
        + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
             + (v.free_in_c_2 r_binary).val * 65536
             + (v.free_in_c_3 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have h_hi_bound : e2.value_1.val < 4294967296 := by
    change (memory_entry_hi e2).val < 4294967296
    rw [h_hi_eq]
    have h_cast :
        v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
        + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216
        = ((((v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val * 256
             + (v.free_in_c_6 r_binary).val * 65536
             + (v.free_in_c_7 r_binary).val * 16777216 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  -- Chunk-shape: memory_entry_lo e2 = e2.value_0; byteAt projections of value_0
  -- pack-decompose via byteAt_lo_val_sum_eq.
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_lo_bound).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_hi_bound).symm
  -- RHS Nat lifting on the binary-c side.
  have h_lo_bin_nat :
      (v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
       + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216 : FGL).val
      = (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
        + (v.free_in_c_2 r_binary).val * 65536
        + (v.free_in_c_3 r_binary).val * 16777216 := by
    have h_cast :
        v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
        + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216
        = ((((v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
             + (v.free_in_c_2 r_binary).val * 65536
             + (v.free_in_c_3 r_binary).val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_hi_bin_nat :
      (v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
       + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216 : FGL).val
      = (v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val * 256
        + (v.free_in_c_6 r_binary).val * 65536
        + (v.free_in_c_7 r_binary).val * 16777216 := by
    have h_cast :
        v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
        + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216
        = ((((v.free_in_c_4 r_binary).val + (v.free_in_c_5 r_binary).val * 256
             + (v.free_in_c_6 r_binary).val * 65536
             + (v.free_in_c_7 r_binary).val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  -- Apply Fin.val to the FGL lo/hi equalities, simplify.
  have h_lo_val := congr_arg Fin.val h_lo_eq
  have h_hi_val := congr_arg Fin.val h_hi_eq
  rw [h_lo_nat, h_lo_bin_nat] at h_lo_val
  rw [h_hi_nat, h_hi_bin_nat] at h_hi_val
  omega

private lemma byte_ranges_of_consumer_byte_match_wf
    {op_val : ℕ} {a b c : FGL}
    (h : consumer_byte_match_wf op_val a b c) :
    a.val < 256 ∧ b.val < 256 ∧ c.val < 256 := by
  obtain ⟨e, h_wf, _h_op, h_a, h_b, h_c⟩ := h
  rcases h_wf.1 with ⟨ha, hb, hc, _hcin⟩
  exact ⟨by simpa [h_a] using ha, by simpa [h_b] using hb,
    by simpa [h_c] using hc⟩

private lemma byte_sum_from_binary_row_lane_match
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (e2 : MemoryBusEntry FGL)
    (h_match_clo :
        row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216 = memory_entry_lo e2)
    (h_match_chi :
        row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216 = memory_entry_hi e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (hc0 : row.cBytes.free_in_c_0.val < 256)
    (hc1 : row.cBytes.free_in_c_1.val < 256)
    (hc2 : row.cBytes.free_in_c_2.val < 256)
    (hc3 : row.cBytes.free_in_c_3.val < 256)
    (hc4 : row.cBytes.free_in_c_4.val < 256)
    (hc5 : row.cBytes.free_in_c_5.val < 256)
    (hc6 : row.cBytes.free_in_c_6.val < 256)
    (hc7 : row.cBytes.free_in_c_7.val < 256) :
    (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
    + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
    + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
    = row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
      + row.cBytes.free_in_c_2.val * 65536
      + row.cBytes.free_in_c_3.val * 16777216
      + row.cBytes.free_in_c_4.val * 4294967296
      + row.cBytes.free_in_c_5.val * 1099511627776
      + row.cBytes.free_in_c_6.val * 281474976710656
      + row.cBytes.free_in_c_7.val * 72057594037927936 := by
  have h_lo_row_nat :
      (row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
       + row.cBytes.free_in_c_2 * 65536
       + row.cBytes.free_in_c_3 * 16777216 : FGL).val
      = row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536
        + row.cBytes.free_in_c_3.val * 16777216 := by
    have h_cast :
        row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
        + row.cBytes.free_in_c_2 * 65536
        + row.cBytes.free_in_c_3 * 16777216
        = (((row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
             + row.cBytes.free_in_c_2.val * 65536
             + row.cBytes.free_in_c_3.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_hi_row_nat :
      (row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
       + row.cBytes.free_in_c_6 * 65536
       + row.cBytes.free_in_c_7 * 16777216 : FGL).val
      = row.cBytes.free_in_c_4.val + row.cBytes.free_in_c_5.val * 256
        + row.cBytes.free_in_c_6.val * 65536
        + row.cBytes.free_in_c_7.val * 16777216 := by
    have h_cast :
        row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
        + row.cBytes.free_in_c_6 * 65536
        + row.cBytes.free_in_c_7 * 16777216
        = (((row.cBytes.free_in_c_4.val + row.cBytes.free_in_c_5.val * 256
             + row.cBytes.free_in_c_6.val * 65536
             + row.cBytes.free_in_c_7.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt; omega
  have h_lo_bound : e2.value_0.val < 4294967296 := by
    change (memory_entry_lo e2).val < 4294967296
    rw [← h_match_clo, h_lo_row_nat]
    omega
  have h_hi_bound : e2.value_1.val < 4294967296 := by
    change (memory_entry_hi e2).val < 4294967296
    rw [← h_match_chi, h_hi_row_nat]
    omega
  have h_lo_nat : (memory_entry_lo e2).val
      = (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216 := by
    simp only [memory_entry_lo]; exact (byteAt_lo_val_sum_eq e2 h_lo_bound).symm
  have h_hi_nat : (memory_entry_hi e2).val
      = (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216 := by
    simp only [memory_entry_hi]; exact (byteAt_hi_val_sum_eq e2 h_hi_bound).symm
  have h_lo_val := congrArg Fin.val h_match_clo
  have h_hi_val := congrArg Fin.val h_match_chi
  rw [h_lo_row_nat, h_lo_nat] at h_lo_val
  rw [h_hi_row_nat, h_hi_nat] at h_hi_val
  omega

/-! ## AND -/

/-- Row-native AND write-value derivation.

This is the C7 entry point below the legacy `Valid_Binary` wrapper stack:
the Binary-side semantic input is a Clean `BinaryRow` plus row-level static
BinaryTable facts. The operation-bus and memory-bus information is supplied
as direct lane equalities, which is exactly what the Clean balance projection
and row-native Main/memory bridge should produce. -/
lemma h_rd_val_logic_and_row_of_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    (h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row OP_AND)
    (h_match_clo :
        row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216 = memory_entry_lo e2)
    (h_match_chi :
        row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216 = memory_entry_hi e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
            + row.aBytes.free_in_a_2.val * 65536
            + row.aBytes.free_in_a_3.val * 16777216
            + row.aBytes.free_in_a_4.val * 4294967296
            + row.aBytes.free_in_a_5.val * 1099511627776
            + row.aBytes.free_in_a_6.val * 281474976710656
            + row.aBytes.free_in_a_7.val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
            + row.bBytes.free_in_b_2.val * 65536
            + row.bBytes.free_in_b_3.val * 16777216
            + row.bBytes.free_in_b_4.val * 4294967296
            + row.bBytes.free_in_b_5.val * 1099511627776
            + row.bBytes.free_in_b_6.val * 281474976710656
            + row.bBytes.free_in_b_7.val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val &&& r2_val := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨_, _, hc0⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨_, _, hc1⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨_, _, hc2⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨_, _, hc3⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨_, _, hc4⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨_, _, hc5⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨_, _, hc6⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨_, _, hc7⟩ := byte_ranges_of_consumer_byte_match_wf h7
  have h_matches' :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row OP_AND :=
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have h_bv :=
    ZiskFv.EquivCore.Bridge.Binary.binary_row_and_chunks_eq_bv_and_of_wf
      row h_matches'
  have h_byte_sum := byte_sum_from_binary_row_lane_match row e2
    h_match_clo h_match_chi
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (r1_val &&& r2_val).toNat := by
    rw [h_byte_sum]
    rw [h_input_r1, h_input_r2]
    rw [show (BitVec.ofNat 64 _ &&& BitVec.ofNat 64 _ : BitVec 64)
            = BitVec.and (BitVec.ofNat 64 _) (BitVec.ofNat 64 _) from rfl]
    rw [h_bv, BitVec.toNat_ofNat]
    have h_lt :
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216
          + row.cBytes.free_in_c_4.val * 4294967296
          + row.cBytes.free_in_c_5.val * 1099511627776
          + row.cBytes.free_in_c_6.val * 281474976710656
          + row.cBytes.free_in_c_7.val * 72057594037927936
        < 2 ^ 64 := by
      show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val &&& r2_val) (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

lemma h_rd_val_logic_or_row_of_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    (h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row OP_OR)
    (h_match_clo :
        row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216 = memory_entry_lo e2)
    (h_match_chi :
        row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216 = memory_entry_hi e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
            + row.aBytes.free_in_a_2.val * 65536
            + row.aBytes.free_in_a_3.val * 16777216
            + row.aBytes.free_in_a_4.val * 4294967296
            + row.aBytes.free_in_a_5.val * 1099511627776
            + row.aBytes.free_in_a_6.val * 281474976710656
            + row.aBytes.free_in_a_7.val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
            + row.bBytes.free_in_b_2.val * 65536
            + row.bBytes.free_in_b_3.val * 16777216
            + row.bBytes.free_in_b_4.val * 4294967296
            + row.bBytes.free_in_b_5.val * 1099511627776
            + row.bBytes.free_in_b_6.val * 281474976710656
            + row.bBytes.free_in_b_7.val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val ||| r2_val := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨_, _, hc0⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨_, _, hc1⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨_, _, hc2⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨_, _, hc3⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨_, _, hc4⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨_, _, hc5⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨_, _, hc6⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨_, _, hc7⟩ := byte_ranges_of_consumer_byte_match_wf h7
  have h_matches' :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row OP_OR :=
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have h_bv :=
    ZiskFv.EquivCore.Bridge.Binary.binary_row_or_chunks_eq_bv_or_of_wf
      row h_matches'
  have h_byte_sum := byte_sum_from_binary_row_lane_match row e2
    h_match_clo h_match_chi
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (r1_val ||| r2_val).toNat := by
    rw [h_byte_sum]
    rw [h_input_r1, h_input_r2]
    rw [show (BitVec.ofNat 64 _ ||| BitVec.ofNat 64 _ : BitVec 64)
            = BitVec.or (BitVec.ofNat 64 _) (BitVec.ofNat 64 _) from rfl]
    rw [h_bv, BitVec.toNat_ofNat]
    have h_lt :
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216
          + row.cBytes.free_in_c_4.val * 4294967296
          + row.cBytes.free_in_c_5.val * 1099511627776
          + row.cBytes.free_in_c_6.val * 281474976710656
          + row.cBytes.free_in_c_7.val * 72057594037927936
        < 2 ^ 64 := by
      show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val ||| r2_val) (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

lemma h_rd_val_logic_xor_row_of_wf
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    (h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row OP_XOR)
    (h_match_clo :
        row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536
          + row.cBytes.free_in_c_3 * 16777216 = memory_entry_lo e2)
    (h_match_chi :
        row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536
          + row.cBytes.free_in_c_7 * 16777216 = memory_entry_hi e2)
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          (row.aBytes.free_in_a_0.val + row.aBytes.free_in_a_1.val * 256
            + row.aBytes.free_in_a_2.val * 65536
            + row.aBytes.free_in_a_3.val * 16777216
            + row.aBytes.free_in_a_4.val * 4294967296
            + row.aBytes.free_in_a_5.val * 1099511627776
            + row.aBytes.free_in_a_6.val * 281474976710656
            + row.aBytes.free_in_a_7.val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          (row.bBytes.free_in_b_0.val + row.bBytes.free_in_b_1.val * 256
            + row.bBytes.free_in_b_2.val * 65536
            + row.bBytes.free_in_b_3.val * 16777216
            + row.bBytes.free_in_b_4.val * 4294967296
            + row.bBytes.free_in_b_5.val * 1099511627776
            + row.bBytes.free_in_b_6.val * 281474976710656
            + row.bBytes.free_in_b_7.val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val ^^^ r2_val := by
  rcases h_matches with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨_, _, hc0⟩ := byte_ranges_of_consumer_byte_match_wf h0
  obtain ⟨_, _, hc1⟩ := byte_ranges_of_consumer_byte_match_wf h1
  obtain ⟨_, _, hc2⟩ := byte_ranges_of_consumer_byte_match_wf h2
  obtain ⟨_, _, hc3⟩ := byte_ranges_of_consumer_byte_match_wf h3
  obtain ⟨_, _, hc4⟩ := byte_ranges_of_consumer_byte_match_wf h4
  obtain ⟨_, _, hc5⟩ := byte_ranges_of_consumer_byte_match_wf h5
  obtain ⟨_, _, hc6⟩ := byte_ranges_of_consumer_byte_match_wf h6
  obtain ⟨_, _, hc7⟩ := byte_ranges_of_consumer_byte_match_wf h7
  have h_matches' :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row row OP_XOR :=
    ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  have h_bv :=
    ZiskFv.EquivCore.Bridge.Binary.binary_row_xor_chunks_eq_bv_xor_of_wf
      row h_matches'
  have h_byte_sum := byte_sum_from_binary_row_lane_match row e2
    h_match_clo h_match_chi
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (r1_val ^^^ r2_val).toNat := by
    rw [h_byte_sum]
    rw [h_input_r1, h_input_r2]
    rw [show (BitVec.ofNat 64 _ ^^^ BitVec.ofNat 64 _ : BitVec 64)
            = BitVec.xor (BitVec.ofNat 64 _) (BitVec.ofNat 64 _) from rfl]
    rw [h_bv, BitVec.toNat_ofNat]
    have h_lt :
        row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
          + row.cBytes.free_in_c_2.val * 65536
          + row.cBytes.free_in_c_3.val * 16777216
          + row.cBytes.free_in_c_4.val * 4294967296
          + row.cBytes.free_in_c_5.val * 1099511627776
          + row.cBytes.free_in_c_6.val * 281474976710656
          + row.cBytes.free_in_c_7.val * 72057594037927936
        < 2 ^ 64 := by
      show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val ^^^ r2_val) (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

lemma h_rd_val_logic_and_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    -- K1-B byte-lookup hypotheses.
    (h_byte_0 : consumer_byte_match_wf OP_AND
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : consumer_byte_match_wf OP_AND
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : consumer_byte_match_wf OP_AND
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : consumer_byte_match_wf OP_AND
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : consumer_byte_match_wf OP_AND
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : consumer_byte_match_wf OP_AND
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : consumer_byte_match_wf OP_AND
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : consumer_byte_match_wf OP_AND
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    -- Byte ranges on Valid_Binary's a/b cells (needed by K1-B).
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    -- Byte ranges on Valid_Binary's c cells (needed for the Nat byte-sum lift).
    -- These are derivable from the same lookup contract as the a/b ranges
    -- (every entry consumed has range_conditions; not exposed as a separate
    -- bundle to avoid a third helper structure — supplied at the call site
    -- in the same shape as ha0..ha7).
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    -- Main↔Binary c-lane bus-match (the operation-bus c-lane identity).
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
    -- rd-write lane match.
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- e2 byte ranges.
    (h_e2_0 : (byteAt e2 0).val < 256) (h_e2_1 : (byteAt e2 1).val < 256)
    (h_e2_2 : (byteAt e2 2).val < 256) (h_e2_3 : (byteAt e2 3).val < 256)
    (h_e2_4 : (byteAt e2 4).val < 256) (h_e2_5 : (byteAt e2 5).val < 256)
    (h_e2_6 : (byteAt e2 6).val < 256) (h_e2_7 : (byteAt e2 7).val < 256)
    -- Transpile bridges (input side): r1_val / r2_val match Valid_Binary's
    -- packed 8-byte a/b sums.
    (h_input_r1 : r1_val
      = BitVec.ofNat 64
          ((v.free_in_a_0 r_binary).val + (v.free_in_a_1 r_binary).val * 256
            + (v.free_in_a_2 r_binary).val * 65536
            + (v.free_in_a_3 r_binary).val * 16777216
            + (v.free_in_a_4 r_binary).val * 4294967296
            + (v.free_in_a_5 r_binary).val * 1099511627776
            + (v.free_in_a_6 r_binary).val * 281474976710656
            + (v.free_in_a_7 r_binary).val * 72057594037927936))
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val &&& r2_val := by
  -- K1-B AND lift.
  have h_bv := binary_and_chunks_eq_bv_and_of_wf v r_binary
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  -- extract the lane-match equalities for c0/c1.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  -- derive the byte-sum Nat identity for e2 = c-bytes packed sum.
  have h_byte_sum := byte_sum_from_binary_lane_match m v r_main r_binary e2
    h_match_clo h_match_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  -- convert the byte sum to U64.toBV via bv64_of_byte_sum at spec_val
  -- = r1_val &&& r2_val.
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (r1_val &&& r2_val).toNat := by
    rw [h_byte_sum]
    -- Now goal: byte-sum of c equals (r1_val &&& r2_val).toNat.
    -- From h_bv we have BitVec.and (BitVec.ofNat 64 sum_a) (BitVec.ofNat 64 sum_b)
    --                  = BitVec.ofNat 64 sum_c
    -- Apply h_input_r1, h_input_r2 to identify the LHS with r1_val &&& r2_val.
    rw [h_input_r1, h_input_r2]
    -- Goal: byte-sum of c
    --       = (BitVec.and (BitVec.ofNat 64 sum_a) (BitVec.ofNat 64 sum_b)).toNat
    rw [show (BitVec.ofNat 64 _ &&& BitVec.ofNat 64 _ : BitVec 64)
            = BitVec.and (BitVec.ofNat 64 _) (BitVec.ofNat 64 _) from rfl]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    -- Now we need: byte_sum_c (Nat) = byte_sum_c_natly % 2^64.
    -- Under the byte ranges hc0..hc7, byte_sum_c < 2^64.
    have h_lt :
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216
          + (v.free_in_c_4 r_binary).val * 4294967296
          + (v.free_in_c_5 r_binary).val * 1099511627776
          + (v.free_in_c_6 r_binary).val * 281474976710656
          + (v.free_in_c_7 r_binary).val * 72057594037927936
        < 2 ^ 64 := by
      show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val &&& r2_val) (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-- Static-provider variant of `h_rd_val_logic_andi`. -/
lemma h_rd_val_logic_andi_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_byte_0 : consumer_byte_match_wf OP_AND
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : consumer_byte_match_wf OP_AND
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : consumer_byte_match_wf OP_AND
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : consumer_byte_match_wf OP_AND
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : consumer_byte_match_wf OP_AND
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : consumer_byte_match_wf OP_AND
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : consumer_byte_match_wf OP_AND
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : consumer_byte_match_wf OP_AND
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
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
    (h_input_imm : BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val &&& BitVec.signExtend 64 imm := by
  exact h_rd_val_logic_and_of_wf m v r_main r_binary e2 r1_val (BitVec.signExtend 64 imm)
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1 h_input_imm

/-- Static-provider variant of `h_rd_val_logic_or`. -/
lemma h_rd_val_logic_or_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    (h_byte_0 : consumer_byte_match_wf OP_OR
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : consumer_byte_match_wf OP_OR
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : consumer_byte_match_wf OP_OR
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : consumer_byte_match_wf OP_OR
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : consumer_byte_match_wf OP_OR
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : consumer_byte_match_wf OP_OR
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : consumer_byte_match_wf OP_OR
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : consumer_byte_match_wf OP_OR
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
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
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val ||| r2_val := by
  have h_bv := binary_or_chunks_eq_bv_or_of_wf v r_binary
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_byte_sum := byte_sum_from_binary_lane_match m v r_main r_binary e2
    h_match_clo h_match_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (r1_val ||| r2_val).toNat := by
    rw [h_byte_sum]
    rw [h_input_r1, h_input_r2]
    rw [show (BitVec.ofNat 64 _ ||| BitVec.ofNat 64 _ : BitVec 64)
            = BitVec.or (BitVec.ofNat 64 _) (BitVec.ofNat 64 _) from rfl]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt :
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216
          + (v.free_in_c_4 r_binary).val * 4294967296
          + (v.free_in_c_5 r_binary).val * 1099511627776
          + (v.free_in_c_6 r_binary).val * 281474976710656
          + (v.free_in_c_7 r_binary).val * 72057594037927936
        < 2 ^ 64 := by
      show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val ||| r2_val) (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-- Static-provider variant of `h_rd_val_logic_ori`. -/
lemma h_rd_val_logic_ori_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_byte_0 : consumer_byte_match_wf OP_OR
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : consumer_byte_match_wf OP_OR
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : consumer_byte_match_wf OP_OR
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : consumer_byte_match_wf OP_OR
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : consumer_byte_match_wf OP_OR
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : consumer_byte_match_wf OP_OR
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : consumer_byte_match_wf OP_OR
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : consumer_byte_match_wf OP_OR
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
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
    (h_input_imm : BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val ||| BitVec.signExtend 64 imm := by
  exact h_rd_val_logic_or_of_wf m v r_main r_binary e2 r1_val (BitVec.signExtend 64 imm)
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1 h_input_imm

/-- Static-provider variant of `h_rd_val_logic_xor`. -/
lemma h_rd_val_logic_xor_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val r2_val : BitVec 64)
    (h_byte_0 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
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
    (h_input_r2 : r2_val
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val ^^^ r2_val := by
  have h_bv := binary_xor_chunks_eq_bv_xor_of_wf v r_binary
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_lo_match, h_hi_match⟩ := h_lane_rd
  have h_byte_sum := byte_sum_from_binary_lane_match m v r_main r_binary e2
    h_match_clo h_match_chi h_lo_match h_hi_match
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
  have h_target :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
      = (r1_val ^^^ r2_val).toNat := by
    rw [h_byte_sum]
    rw [h_input_r1, h_input_r2]
    rw [show (BitVec.ofNat 64 _ ^^^ BitVec.ofNat 64 _ : BitVec 64)
            = BitVec.xor (BitVec.ofNat 64 _) (BitVec.ofNat 64 _) from rfl]
    rw [h_bv]
    rw [BitVec.toNat_ofNat]
    have h_lt :
        (v.free_in_c_0 r_binary).val + (v.free_in_c_1 r_binary).val * 256
          + (v.free_in_c_2 r_binary).val * 65536
          + (v.free_in_c_3 r_binary).val * 16777216
          + (v.free_in_c_4 r_binary).val * 4294967296
          + (v.free_in_c_5 r_binary).val * 1099511627776
          + (v.free_in_c_6 r_binary).val * 281474976710656
          + (v.free_in_c_7 r_binary).val * 72057594037927936
        < 2 ^ 64 := by
      show _ < 18446744073709551616; omega
    rw [Nat.mod_eq_of_lt h_lt]
  exact bv64_of_byte_sum (r1_val ^^^ r2_val) (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7 h_target

/-- Static-provider variant of `h_rd_val_logic_xori`. -/
lemma h_rd_val_logic_xori_of_wf
    (m : Valid_Main FGL FGL) (v : Valid_Binary FGL FGL)
    (r_main r_binary : ℕ)
    (e2 : MemoryBusEntry FGL)
    (r1_val : BitVec 64) (imm : BitVec 12)
    (h_byte_0 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary) (v.free_in_c_0 r_binary))
    (h_byte_1 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary) (v.free_in_c_1 r_binary))
    (h_byte_2 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary) (v.free_in_c_2 r_binary))
    (h_byte_3 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary) (v.free_in_c_3 r_binary))
    (h_byte_4 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary) (v.free_in_c_4 r_binary))
    (h_byte_5 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary) (v.free_in_c_5 r_binary))
    (h_byte_6 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary) (v.free_in_c_6 r_binary))
    (h_byte_7 : consumer_byte_match_wf OP_XOR
      (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary) (v.free_in_c_7 r_binary))
    (ha0 : (v.free_in_a_0 r_binary).val < 256) (ha1 : (v.free_in_a_1 r_binary).val < 256)
    (ha2 : (v.free_in_a_2 r_binary).val < 256) (ha3 : (v.free_in_a_3 r_binary).val < 256)
    (ha4 : (v.free_in_a_4 r_binary).val < 256) (ha5 : (v.free_in_a_5 r_binary).val < 256)
    (ha6 : (v.free_in_a_6 r_binary).val < 256) (ha7 : (v.free_in_a_7 r_binary).val < 256)
    (hb0 : (v.free_in_b_0 r_binary).val < 256) (hb1 : (v.free_in_b_1 r_binary).val < 256)
    (hb2 : (v.free_in_b_2 r_binary).val < 256) (hb3 : (v.free_in_b_3 r_binary).val < 256)
    (hb4 : (v.free_in_b_4 r_binary).val < 256) (hb5 : (v.free_in_b_5 r_binary).val < 256)
    (hb6 : (v.free_in_b_6 r_binary).val < 256) (hb7 : (v.free_in_b_7 r_binary).val < 256)
    (hc0 : (v.free_in_c_0 r_binary).val < 256) (hc1 : (v.free_in_c_1 r_binary).val < 256)
    (hc2 : (v.free_in_c_2 r_binary).val < 256) (hc3 : (v.free_in_c_3 r_binary).val < 256)
    (hc4 : (v.free_in_c_4 r_binary).val < 256) (hc5 : (v.free_in_c_5 r_binary).val < 256)
    (hc6 : (v.free_in_c_6 r_binary).val < 256) (hc7 : (v.free_in_c_7 r_binary).val < 256)
    (h_match_clo : m.c_0 r_main
        = v.free_in_c_0 r_binary + v.free_in_c_1 r_binary * 256
          + v.free_in_c_2 r_binary * 65536 + v.free_in_c_3 r_binary * 16777216)
    (h_match_chi : m.c_1 r_main
        = v.free_in_c_4 r_binary + v.free_in_c_5 r_binary * 256
          + v.free_in_c_6 r_binary * 65536 + v.free_in_c_7 r_binary * 16777216)
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
    (h_input_imm : BitVec.signExtend 64 imm
      = BitVec.ofNat 64
          ((v.free_in_b_0 r_binary).val + (v.free_in_b_1 r_binary).val * 256
            + (v.free_in_b_2 r_binary).val * 65536
            + (v.free_in_b_3 r_binary).val * 16777216
            + (v.free_in_b_4 r_binary).val * 4294967296
            + (v.free_in_b_5 r_binary).val * 1099511627776
            + (v.free_in_b_6 r_binary).val * 281474976710656
            + (v.free_in_b_7 r_binary).val * 72057594037927936)) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8), ((byteAt e2 3) : BitVec 8),
                ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8), ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = r1_val ^^^ BitVec.signExtend 64 imm := by
  exact h_rd_val_logic_xor_of_wf m v r_main r_binary e2 r1_val (BitVec.signExtend 64 imm)
    h_byte_0 h_byte_1 h_byte_2 h_byte_3 h_byte_4 h_byte_5 h_byte_6 h_byte_7
    ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
    hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
    hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    h_match_clo h_match_chi h_lane_rd
    h_e2_0 h_e2_1 h_e2_2 h_e2_3 h_e2_4 h_e2_5 h_e2_6 h_e2_7
    h_input_r1 h_input_imm

end ZiskFv.EquivCore.WriteValueProofs.BinaryLogic
