import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.ZiskCircuit.LoadD
import ZiskFv.Tactics.LoadArchetype

/-!
# Circuit.LoadDerivation — derive cross-entry byte facts for loads from circuit witnesses

The seven RV64IM integer load equivalence theorems used to accept an
unproven hypothesis tying the rd-write bus entry `e2`'s bytes to the
read entry `e1`'s bytes (or to a sign/zero-extension thereof). This
module discharges that hypothesis from circuit witnesses.

## Family A — copyb byte passthrough (LD, LBU, LHU, LWU)

ZisK lowers all four to `copyb` (`OP_COPYB = 1, OpType::Internal`).
Main constraints 9 and 16 force `c_0 = b_0` and `c_1 = b_1` directly.
With the `b` lanes packing the read entry `e1` and the `c` lanes
packing the write entry `e2`, this gives `lo e1 = lo e2 ∧ hi e1 = hi e2`
in FGL. Per-byte byte-range hypotheses (caller-supplied, mirroring
`Equivalence/Add.lean`'s `h_e2_*` parameters) close to per-byte
equality via base-256 unique decomposition.

## Family B — sign-extension (LB, LH, LW)

`is_external_op = 1`; the `c` lanes are produced by the BinaryExtension
AIR over the operation bus. Handled separately below once
`Airs/BinaryExtensionTable.lean::wf_properties` is extended with the
`SEXT_B/H/W` cases (they are present in the upstream PIL but were
absent in the Lean port). See `Tactics/SignExtendLoadArchetype.lean`
for the c-packed bus-side closure.
-/

set_option maxHeartbeats 400000

namespace ZiskFv.ZiskCircuit.LoadDerivation

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf byteOf_zero byteOf_of_lt_pow)
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.MemBridge
open ZiskFv.ZiskCircuit.LoadD
open ZiskFv.Tactics.LoadArchetype


/-! ## Base-256 unique decomposition over FGL

The half-packed FGL expression `x0 + x1 * 256 + x2 * 2^16 + x3 * 2^24`
is bounded by `4 * 256 * 2^24 = 2^32 < GL_prime`, so its `.val`
equals the corresponding ℕ sum without modular reduction. Two such
expressions agree iff their bytes agree. -/

/-- 4-byte version of `PackedBitVec.fgl_packed_bytes_val_of_lt_prime`:
    the `.val` of a 4-byte FGL packed sum equals the ℕ byte sum when
    the bytes are individually `< 256` (sum is `< 2^32 < GL_prime`). -/
private lemma fgl_packed_4bytes_val_of_byte_range
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
  -- Sum is at most `255 + 255*256 + 255*65536 + 255*16777216 = 2^32 - 1`.
  -- GL_prime = 2^64 - 2^32 + 1.
  omega

/-- Per-byte FGL equality from packed FGL equality, given byte ranges.
    "Half" version (4 bytes; works for either lo or hi half of a memory
    bus entry). -/
lemma four_bytes_eq_of_packed_eq
    (a0 a1 a2 a3 b0 b1 b2 b3 : FGL)
    (ha0 : a0.val < 256) (ha1 : a1.val < 256)
    (ha2 : a2.val < 256) (ha3 : a3.val < 256)
    (hb0 : b0.val < 256) (hb1 : b1.val < 256)
    (hb2 : b2.val < 256) (hb3 : b3.val < 256)
    (h_eq : a0 + a1 * 256 + a2 * 65536 + a3 * 16777216
          = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  -- Pass through `.val` to ℕ.
  have h_val_a := fgl_packed_4bytes_val_of_byte_range a0 a1 a2 a3 ha0 ha1 ha2 ha3
  have h_val_b := fgl_packed_4bytes_val_of_byte_range b0 b1 b2 b3 hb0 hb1 hb2 hb3
  have h_val_eq :
      a0.val + a1.val * 256 + a2.val * 65536 + a3.val * 16777216
      = b0.val + b1.val * 256 + b2.val * 65536 + b3.val * 16777216 := by
    rw [← h_val_a, ← h_val_b, h_eq]
  -- Clear the FGL hypothesis so omega sees only Nat equations.
  clear h_eq h_val_a h_val_b
  -- omega closes each per-byte equality given bounds + h_val_eq.
  have hE0 : a0.val = b0.val := by omega
  have hE1 : a1.val = b1.val := by omega
  have hE2 : a2.val = b2.val := by omega
  have hE3 : a3.val = b3.val := by omega
  exact ⟨Fin.ext hE0, Fin.ext hE1, Fin.ext hE2, Fin.ext hE3⟩

/-! ## Family A — copyb byte passthrough -/

/-- **Family A passthrough.** Given an LD-mode Main row plus the read
    and write bus emissions plus byte ranges on both entries, derive
    per-byte FGL equality between the read entry `e1` and the write
    entry `e2`. The lo/hi halves match because constraints 9/16
    (`(1 - is_external_op) * op * (b - c) = 0`) collapse under the
    LD-mode witnesses (`is_external_op = 0, op = 1`); per-byte
    equality follows from `four_bytes_eq_of_packed_eq` on each half. -/
lemma load_copyb_e1_e2_bytes_eq
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (h_copy0 : internal_op1_copies_b0 m r_main)
    (h_copy1 : internal_op1_copies_b1 m r_main)
    (h_ext : m.is_external_op r_main = 0)
    (h_op : m.op r_main = (1 : FGL))
    (h_emit_b :
      m.b_0 r_main = memory_entry_lo e1
      ∧ m.b_1 r_main = memory_entry_hi e1)
    (h_emit_c :
      m.c_0 r_main = memory_entry_lo e2
      ∧ m.c_1 r_main = memory_entry_hi e2) :
    (byteAt e1 0) = (byteAt e2 0) ∧ (byteAt e1 1) = (byteAt e2 1) ∧ (byteAt e1 2) = (byteAt e2 2) ∧ (byteAt e1 3) = (byteAt e2 3)
    ∧ (byteAt e1 4) = (byteAt e2 4) ∧ (byteAt e1 5) = (byteAt e2 5) ∧ (byteAt e1 6) = (byteAt e2 6) ∧ (byteAt e1 7) = (byteAt e2 7) := by
  obtain ⟨h_b0, h_b1⟩ := h_emit_b
  obtain ⟨h_c0, h_c1⟩ := h_emit_c
  -- Constraint 9/16 reduce to `b_0 = c_0` / `b_1 = c_1` after substitution.
  simp only [internal_op1_copies_b0, internal_op1_copies_b1] at h_copy0 h_copy1
  rw [h_ext, h_op] at h_copy0 h_copy1
  have h_bc0 : m.b_0 r_main = m.c_0 r_main := by linear_combination h_copy0
  have h_bc1 : m.b_1 r_main = m.c_1 r_main := by linear_combination h_copy1
  have h_v0 : e1.value_0 = e2.value_0 := by
    have h_lo : memory_entry_lo e1 = memory_entry_lo e2 := by
      rw [← h_b0, h_bc0, h_c0]
    simpa only [memory_entry_lo] using h_lo
  have h_v1 : e1.value_1 = e2.value_1 := by
    have h_hi : memory_entry_hi e1 = memory_entry_hi e2 := by
      rw [← h_b1, h_bc1, h_c1]
    simpa only [memory_entry_hi] using h_hi
  -- Each byteAt projection depends only on value_0 or value_1; chunk
  -- equality propagates pointwise.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold byteAt; simp only [h_v0, h_v1])

/-- **BitVec 8 lift.** Per-byte FGL equality lifts to per-byte
    `BitVec 8` equality through the `FGL → BitVec 8` coercion. -/
lemma byte_bitvec_eq_of_fgl_eq {a b : FGL} (h : a = b) :
    (a : BitVec 8) = (b : BitVec 8) := by
  rw [h]

/-- **LD-shape derivation.** From the Family A passthrough plus byte
    ranges, deliver the eight `(e2.x_i : BitVec 8) = (e1.x_i : BitVec 8)`
    equations the `Equivalence/Ld.lean` proof body needs in place
    of the retired `h_e1_e2_bytes` hypothesis. -/
lemma load_copyb_e1_e2_bytes_eq_bv
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (e1 e2 : MemoryBusEntry FGL)
    (h_copy0 : internal_op1_copies_b0 m r_main)
    (h_copy1 : internal_op1_copies_b1 m r_main)
    (h_ext : m.is_external_op r_main = 0)
    (h_op : m.op r_main = (1 : FGL))
    (h_emit_b :
      m.b_0 r_main = memory_entry_lo e1
      ∧ m.b_1 r_main = memory_entry_hi e1)
    (h_emit_c :
      m.c_0 r_main = memory_entry_lo e2
      ∧ m.c_1 r_main = memory_entry_hi e2) :
    ((byteAt e2 0) : BitVec 8) = (byteAt e1 0)
    ∧ ((byteAt e2 1) : BitVec 8) = (byteAt e1 1)
    ∧ ((byteAt e2 2) : BitVec 8) = (byteAt e1 2)
    ∧ ((byteAt e2 3) : BitVec 8) = (byteAt e1 3)
    ∧ ((byteAt e2 4) : BitVec 8) = (byteAt e1 4)
    ∧ ((byteAt e2 5) : BitVec 8) = (byteAt e1 5)
    ∧ ((byteAt e2 6) : BitVec 8) = (byteAt e1 6)
    ∧ ((byteAt e2 7) : BitVec 8) = (byteAt e1 7) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    load_copyb_e1_e2_bytes_eq m r_main e1 e2
      h_copy0 h_copy1 h_ext h_op h_emit_b h_emit_c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    <;> exact (byte_bitvec_eq_of_fgl_eq (by assumption)).symm

-- Audit: confirm `load_copyb_e1_e2_bytes_eq` adds no axioms beyond
-- Lean's kernel + Mathlib classical primitives.
#print axioms load_copyb_e1_e2_bytes_eq

/-! ## Family A + C — zero-extension load c-packed forms

For LBU/LHU/LWU, Family A passthrough plus the MemAlign zero-padding
theorem over the structural provider witness compose into the `U64.toBV`
equation each canonical equivalence proof expects. These BitVec shapes
— `(setWidth 32 b).setWidth 64`, etc. — match the
`bus_effect_matches_sail_loadu_<n>byte_rrrw` consumer side. -/

/-- BitVec helper: a `U64.toBV` whose top 7 byte lanes are zero
    collapses to the `(setWidth 32 b).setWidth 64` form expected by
    the LBU sail-side spec. -/
lemma u64_toBV_low_byte_only (b : BitVec 8) :
    U64.toBV #v[b, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
      = (BitVec.setWidth 32 b).setWidth 64 := by
  simp only [U64.toBV, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  bv_decide

/-- BitVec helper: top 6 byte lanes zero collapses to the LHU form. -/
lemma u64_toBV_low_2bytes_only (b1 b0 : BitVec 8) :
    U64.toBV #v[b0, b1, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]
      = (BitVec.setWidth 32 (b1 ++ b0)).setWidth 64 := by
  simp only [U64.toBV, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  bv_decide

/-- BitVec helper: top 4 byte lanes zero collapses to the LWU form. -/
lemma u64_toBV_low_4bytes_only (b3 b2 b1 b0 : BitVec 8) :
    U64.toBV #v[b0, b1, b2, b3, 0#8, 0#8, 0#8, 0#8]
      = BitVec.zeroExtend 64 (b3 ++ b2 ++ b1 ++ b0) := by
  simp only [U64.toBV, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ]
  bv_decide

/-- The FGL→BitVec 8 coercion of `(0 : FGL)` is `0#8`. -/
@[simp]
lemma fgl_zero_to_bitvec8 : ((0 : FGL) : BitVec 8) = 0#8 := by
  decide

/-- **LBU c-packed.** From Family A passthrough plus MemAlign
    zero-padding (derived in
    `Airs/MemoryBus/MemAlignBridge.lean`), derive the LBU U64.toBV
    form. -/
lemma load_lbu_c_packed
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (e1 e2 : MemoryBusEntry FGL)
    (h_copy0 : internal_op1_copies_b0 m r_main)
    (h_copy1 : internal_op1_copies_b1 m r_main)
    (h_ext : m.is_external_op r_main = 0)
    (h_op : m.op r_main = (1 : FGL))
    (h_width : m.ind_width r_main = (1 : FGL))
    (h_emit_b :
      m.b_0 r_main = memory_entry_lo e1
      ∧ m.b_1 r_main = memory_entry_hi e1
      ∧ e1.as = 2 ∧ e1.multiplicity = -1)
    (h_emit_c :
      m.c_0 r_main = memory_entry_lo e2
      ∧ m.c_1 r_main = memory_entry_hi e2)
    (h_mab_core : ∀ r, ZiskFv.Airs.MemAlignByte.core_every_row mab r)
    (h_marb_core : ∀ r, ZiskFv.Airs.MemAlignReadByte.core_every_row marb r)
    (h_mab_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignByte.RangeLookupWitness mab r)
    (h_marb_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignReadByte.RangeLookupWitness marb r)
    (h_provider :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        m mab marb ma r_main e1) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8),
                ((byteAt e2 3) : BitVec 8), ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8),
                ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = (BitVec.setWidth 32 ((byteAt e1 0) : BitVec 8)).setWidth 64 := by
  -- Family A passthrough.
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    load_copyb_e1_e2_bytes_eq_bv m r_main e1 e2
      h_copy0 h_copy1 h_ext h_op
      ⟨h_emit_b.1, h_emit_b.2.1⟩ h_emit_c
  have h_zero_pad :=
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_subdoubleword_load_high_bytes_zero
      m mab marb ma r_main e1 h_emit_b (Or.inl h_width) h_mab_core
      h_marb_core h_mab_lookup h_marb_lookup h_provider
  -- Width = 1 chunk-shape zero-pad: e1.value_1 = 0 ∧ e1.value_0.val < 256.
  obtain ⟨hv1_zero, hv0_lt⟩ := h_zero_pad.1 h_width
  -- Derive the 7 zero-byte facts at the FGL level (byteAt e1 i for i = 1..7).
  have hb1 : byteAt e1 1 = 0 := by
    show (if (1 : ℕ) < 4 then byteOf e1.value_0 1 else byteOf e1.value_1 (1 - 4)) = 0
    simp only [show (1 : ℕ) < 4 from by decide, if_true]
    exact byteOf_of_lt_pow e1.value_0 1 (by simpa using hv0_lt)
  have hb2 : byteAt e1 2 = 0 := by
    show (if (2 : ℕ) < 4 then byteOf e1.value_0 2 else byteOf e1.value_1 (2 - 4)) = 0
    simp only [show (2 : ℕ) < 4 from by decide, if_true]
    exact byteOf_of_lt_pow e1.value_0 2 (by
      have : (256 : ℕ) ^ 2 = 65536 := by decide
      omega)
  have hb3 : byteAt e1 3 = 0 := by
    show (if (3 : ℕ) < 4 then byteOf e1.value_0 3 else byteOf e1.value_1 (3 - 4)) = 0
    simp only [show (3 : ℕ) < 4 from by decide, if_true]
    exact byteOf_of_lt_pow e1.value_0 3 (by
      have : (256 : ℕ) ^ 3 = 16777216 := by decide
      omega)
  have hb4 : byteAt e1 4 = 0 := by
    show (if (4 : ℕ) < 4 then byteOf e1.value_0 4 else byteOf e1.value_1 (4 - 4)) = 0
    simp only [show ¬ (4 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb5 : byteAt e1 5 = 0 := by
    show (if (5 : ℕ) < 4 then byteOf e1.value_0 5 else byteOf e1.value_1 (5 - 4)) = 0
    simp only [show ¬ (5 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb6 : byteAt e1 6 = 0 := by
    show (if (6 : ℕ) < 4 then byteOf e1.value_0 6 else byteOf e1.value_1 (6 - 4)) = 0
    simp only [show ¬ (6 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb7 : byteAt e1 7 = 0 := by
    show (if (7 : ℕ) < 4 then byteOf e1.value_0 7 else byteOf e1.value_1 (7 - 4)) = 0
    simp only [show ¬ (7 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  simp only [fgl_zero_to_bitvec8]
  exact u64_toBV_low_byte_only _

/-- **LHU c-packed.** From Family A passthrough plus MemAlign
    zero-padding (derived in `MemAlignBridge.lean`), derive the LHU
    U64.toBV form. -/
lemma load_lhu_c_packed
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (e1 e2 : MemoryBusEntry FGL)
    (h_copy0 : internal_op1_copies_b0 m r_main)
    (h_copy1 : internal_op1_copies_b1 m r_main)
    (h_ext : m.is_external_op r_main = 0)
    (h_op : m.op r_main = (1 : FGL))
    (h_width : m.ind_width r_main = (2 : FGL))
    (h_emit_b :
      m.b_0 r_main = memory_entry_lo e1
      ∧ m.b_1 r_main = memory_entry_hi e1
      ∧ e1.as = 2 ∧ e1.multiplicity = -1)
    (h_emit_c :
      m.c_0 r_main = memory_entry_lo e2
      ∧ m.c_1 r_main = memory_entry_hi e2)
    (h_mab_core : ∀ r, ZiskFv.Airs.MemAlignByte.core_every_row mab r)
    (h_marb_core : ∀ r, ZiskFv.Airs.MemAlignReadByte.core_every_row marb r)
    (h_mab_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignByte.RangeLookupWitness mab r)
    (h_marb_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignReadByte.RangeLookupWitness marb r)
    (h_provider :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        m mab marb ma r_main e1) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8),
                ((byteAt e2 3) : BitVec 8), ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8),
                ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = (BitVec.setWidth 32
          (((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8))).setWidth 64 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    load_copyb_e1_e2_bytes_eq_bv m r_main e1 e2
      h_copy0 h_copy1 h_ext h_op
      ⟨h_emit_b.1, h_emit_b.2.1⟩ h_emit_c
  have h_zero_pad :=
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_subdoubleword_load_high_bytes_zero
      m mab marb ma r_main e1 h_emit_b (Or.inr (Or.inl h_width)) h_mab_core
      h_marb_core h_mab_lookup h_marb_lookup h_provider
  -- Width = 2 chunk-shape zero-pad: e1.value_1 = 0 ∧ e1.value_0.val < 65536.
  obtain ⟨hv1_zero, hv0_lt⟩ := h_zero_pad.2.1 h_width
  -- Derive bytes 2..7 of e1 are 0 at the FGL level.
  have hb2 : byteAt e1 2 = 0 := by
    show (if (2 : ℕ) < 4 then byteOf e1.value_0 2 else byteOf e1.value_1 (2 - 4)) = 0
    simp only [show (2 : ℕ) < 4 from by decide, if_true]
    exact byteOf_of_lt_pow e1.value_0 2 (by
      have : (256 : ℕ) ^ 2 = 65536 := by decide
      omega)
  have hb3 : byteAt e1 3 = 0 := by
    show (if (3 : ℕ) < 4 then byteOf e1.value_0 3 else byteOf e1.value_1 (3 - 4)) = 0
    simp only [show (3 : ℕ) < 4 from by decide, if_true]
    exact byteOf_of_lt_pow e1.value_0 3 (by
      have : (256 : ℕ) ^ 3 = 16777216 := by decide
      omega)
  have hb4 : byteAt e1 4 = 0 := by
    show (if (4 : ℕ) < 4 then byteOf e1.value_0 4 else byteOf e1.value_1 (4 - 4)) = 0
    simp only [show ¬ (4 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb5 : byteAt e1 5 = 0 := by
    show (if (5 : ℕ) < 4 then byteOf e1.value_0 5 else byteOf e1.value_1 (5 - 4)) = 0
    simp only [show ¬ (5 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb6 : byteAt e1 6 = 0 := by
    show (if (6 : ℕ) < 4 then byteOf e1.value_0 6 else byteOf e1.value_1 (6 - 4)) = 0
    simp only [show ¬ (6 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb7 : byteAt e1 7 = 0 := by
    show (if (7 : ℕ) < 4 then byteOf e1.value_0 7 else byteOf e1.value_1 (7 - 4)) = 0
    simp only [show ¬ (7 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [hb2, hb3, hb4, hb5, hb6, hb7]
  simp only [fgl_zero_to_bitvec8]
  exact u64_toBV_low_2bytes_only _ _

/-- **LWU c-packed.** From Family A passthrough plus MemAlign
    zero-padding (derived in `MemAlignBridge.lean`), derive the LWU
    U64.toBV form. -/
lemma load_lwu_c_packed
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL)
    (marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL)
    (ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL)
    (e1 e2 : MemoryBusEntry FGL)
    (h_copy0 : internal_op1_copies_b0 m r_main)
    (h_copy1 : internal_op1_copies_b1 m r_main)
    (h_ext : m.is_external_op r_main = 0)
    (h_op : m.op r_main = (1 : FGL))
    (h_width : m.ind_width r_main = (4 : FGL))
    (h_emit_b :
      m.b_0 r_main = memory_entry_lo e1
      ∧ m.b_1 r_main = memory_entry_hi e1
      ∧ e1.as = 2 ∧ e1.multiplicity = -1)
    (h_emit_c :
      m.c_0 r_main = memory_entry_lo e2
      ∧ m.c_1 r_main = memory_entry_hi e2)
    (h_mab_core : ∀ r, ZiskFv.Airs.MemAlignByte.core_every_row mab r)
    (h_marb_core : ∀ r, ZiskFv.Airs.MemAlignReadByte.core_every_row marb r)
    (h_mab_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignByte.RangeLookupWitness mab r)
    (h_marb_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignReadByte.RangeLookupWitness marb r)
    (h_provider :
      ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
        m mab marb ma r_main e1) :
    U64.toBV #v[((byteAt e2 0) : BitVec 8), ((byteAt e2 1) : BitVec 8), ((byteAt e2 2) : BitVec 8),
                ((byteAt e2 3) : BitVec 8), ((byteAt e2 4) : BitVec 8), ((byteAt e2 5) : BitVec 8),
                ((byteAt e2 6) : BitVec 8), ((byteAt e2 7) : BitVec 8)]
      = BitVec.zeroExtend 64
          (((byteAt e1 3) : BitVec 8) ++ ((byteAt e1 2) : BitVec 8)
            ++ ((byteAt e1 1) : BitVec 8) ++ ((byteAt e1 0) : BitVec 8)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    load_copyb_e1_e2_bytes_eq_bv m r_main e1 e2
      h_copy0 h_copy1 h_ext h_op
      ⟨h_emit_b.1, h_emit_b.2.1⟩ h_emit_c
  have h_zero_pad :=
    ZiskFv.Airs.MemoryBus.MemAlignBridge.memalign_subdoubleword_load_high_bytes_zero
      m mab marb ma r_main e1 h_emit_b (Or.inr (Or.inr h_width)) h_mab_core
      h_marb_core h_mab_lookup h_marb_lookup h_provider
  -- Width = 4 chunk-shape zero-pad: e1.value_1 = 0.
  have hv1_zero : e1.value_1 = 0 := h_zero_pad.2.2 h_width
  -- Derive bytes 4..7 of e1 are 0 at the FGL level.
  have hb4 : byteAt e1 4 = 0 := by
    show (if (4 : ℕ) < 4 then byteOf e1.value_0 4 else byteOf e1.value_1 (4 - 4)) = 0
    simp only [show ¬ (4 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb5 : byteAt e1 5 = 0 := by
    show (if (5 : ℕ) < 4 then byteOf e1.value_0 5 else byteOf e1.value_1 (5 - 4)) = 0
    simp only [show ¬ (5 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb6 : byteAt e1 6 = 0 := by
    show (if (6 : ℕ) < 4 then byteOf e1.value_0 6 else byteOf e1.value_1 (6 - 4)) = 0
    simp only [show ¬ (6 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  have hb7 : byteAt e1 7 = 0 := by
    show (if (7 : ℕ) < 4 then byteOf e1.value_0 7 else byteOf e1.value_1 (7 - 4)) = 0
    simp only [show ¬ (7 : ℕ) < 4 from by decide, if_false]
    rw [hv1_zero]; exact byteOf_zero _
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  rw [hb4, hb5, hb6, hb7]
  simp only [fgl_zero_to_bitvec8]
  exact u64_toBV_low_4bytes_only _ _ _ _

end ZiskFv.ZiskCircuit.LoadDerivation
