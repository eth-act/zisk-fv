import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge

/-!
# MemoryBus.MemAlignBridge — sub-doubleword load zero-padding from MemAlign* providers

The trusted axiom `lookup_consumer_matches_provider_load`
(`Airs/MemoryBus/MemBridge.lean`) pairs Main load consumers with rows
of the **`Mem`** AIR, but `Mem` only provides aligned width-8 loads
(`mem.pil:524-527`). Sub-doubleword loads (LBU=1, LHU=2, LWU=4) are
provided by the **MemAlign\*** AIR family:

* **MemAlignByte** (`mem_align_byte.pil:96`) — width=1; `value[1]` slot
  is the literal `0`.
* **MemAlignReadByte** (`mem_align_read_byte.pil`) — read-only
  specialization; width=1; `value[1]` literal `0`.
* **MemAlign** (`mem_align.pil:189`) — widths 1/2/4 (and 8) via the
  general unaligned multi-row chain; `value[1]` is a witness column
  whose value-zero claim for sub-doubleword widths is mediated by the
  MemAlignRom lookup.

This file states the permutation-soundness handshake between Main and
the MemAlign\* providers (one new axiom), the ROM-lookup-soundness
fact that pins `value_1 = 0` for sub-doubleword MemAlign rows (one
new axiom, narrow citation), and **derives**
`memalign_subdoubleword_load_high_bytes_zero` as a theorem.
-/

namespace ZiskFv.Airs.MemoryBus.MemAlignBridge

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemAlign
open ZiskFv.Airs.MemAlignByte
open ZiskFv.Airs.MemAlignReadByte
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.MemBridge


/-! ## Bus-tuple row-match predicates

Each predicate mirrors the LOAD-side `permutation_proves` emission
descriptor in `build/extraction/Extraction/MemoryBuses.lean`,
formulated against the provider AIR's named columns. The predicate
asserts that the named row's bus tuple equals the entry's
projection: `[mem_op, addr, step, width, value_0, value_1]` ↔
`[LOAD, e.ptr, e.timestamp, w, lo(e), hi(e)]`.

The `width` slot is captured as an extra equality outside the
predicate (the perm axiom's conclusion bundles it). The `as = 2`
literal is recorded inside the predicate (memory-side address space).
-/

/-- LOAD-side row match for `MemAlignByte` mirroring
    `bus_emission_MemAlignByte_2` (`MemoryBuses.lean:1742`).
    For LOAD: `is_write = 0` ⇒ slot[0] = `1 + is_write` = 1
    (= `MEMORY_LOAD_OP`); slot[3] is the width literal 1; slot[5] is
    the literal 0. -/
@[simp]
def memalign_byte_row_matches_load_entry
    (v : Valid_MemAlignByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  v.is_write r = 0
  ∧ v.addr_w r * 8
      + (4 * v.sel_high_4b r + 2 * v.sel_high_2b r + v.sel_high_b r) = e.ptr
  ∧ v.step r = e.timestamp
  ∧ v.bus_byte r = memory_entry_lo e
  ∧ memory_entry_hi e = 0
  ∧ e.as = 2

/-- LOAD-side row match for `MemAlignReadByte` mirroring
    `bus_emission_MemAlignReadByte_1` (`MemoryBuses.lean:1842`). -/
@[simp]
def memalign_read_byte_row_matches_load_entry
    (v : Valid_MemAlignReadByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  v.addr_w r * 8
      + (4 * v.sel_high_4b r + 2 * v.sel_high_2b r + v.sel_high_b r) = e.ptr
  ∧ v.step r = e.timestamp
  ∧ v.byte_value r = memory_entry_lo e
  ∧ memory_entry_hi e = 0
  ∧ e.as = 2

/-- LOAD-side row match for `MemAlign` mirroring
    `bus_emission_MemAlign_0` (`MemoryBuses.lean:1666`). For LOAD:
    `wr = 0` ⇒ slot[0] = `wr + 1` = 1; selectors `sel_up_to_down` /
    `sel_down_to_up` zero (paired aligned reads against `Mem` use
    those; the prove side pins `sel_prove = 1`). -/
@[simp]
def memalign_row_matches_load_entry
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL) : Prop :=
  v.sel_prove r = 1
  ∧ v.sel_up_to_down r = 0
  ∧ v.sel_down_to_up r = 0
  ∧ v.wr r = 0
  ∧ v.addr r * 8 + v.offset r = e.ptr
  ∧ v.step r = e.timestamp
  ∧ v.value_0 r = memory_entry_lo e
  ∧ v.value_1 r = memory_entry_hi e
  ∧ e.as = 2

/-! ## Trusted-surface axioms

Two narrow axioms, each cited to a specific PIL artifact.
-/

/-- **Permutation-soundness — sub-doubleword load consumer.** Mirrors
    `lookup_consumer_matches_provider_load` (`MemBridge.lean:170`)
    but pairs the Main consumer with the MemAlign\* provider AIRs
    that actually emit narrow-load tuples on `bus_id = 10`.

    Per the Phase A audit (commit `c5ff29f`), three AIRs may provide
    a sub-doubleword load tuple:

    * **MemAlignByte_2** (`mem_align_byte.pil:96`): width=1, slot[5]
      literal 0.
    * **MemAlignReadByte_1** (`mem_align_read_byte.pil:_proves_`):
      width=1, slot[5] literal 0.
    * **MemAlign_0** (`mem_align.pil:189`): widths 1/2/4, slot[5] is
      the `value_1` witness column.

    Project-trusted at the same scope as
    `lookup_consumer_matches_provider_load` (PLONK / plookup
    permutation argument). -/
axiom memalign_load_perm_sound
    (main : Valid_Main FGL FGL)
    (mab : Valid_MemAlignByte FGL FGL)
    (marb : Valid_MemAlignReadByte FGL FGL)
    (ma : Valid_MemAlign FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_emit : main.b_0 r_main = memory_entry_lo e
              ∧ main.b_1 r_main = memory_entry_hi e
              ∧ e.as = 2 ∧ e.multiplicity = -1)
    (h_subdw : main.ind_width r_main = 1
             ∨ main.ind_width r_main = 2
             ∨ main.ind_width r_main = 4) :
    (∃ r, memalign_byte_row_matches_load_entry mab r e
        ∧ main.ind_width r_main = 1)
  ∨ (∃ r, memalign_read_byte_row_matches_load_entry marb r e
        ∧ main.ind_width r_main = 1)
  ∨ (∃ r, memalign_row_matches_load_entry ma r e
        ∧ ma.width r = main.ind_width r_main)

/-- **MemAlignRom lookup soundness — sub-doubleword `value_1 = 0`.**
    The `MemAlignRom` table (`mem_align_rom.pil`) enumerates the
    legal `(pc, delta_pc, delta_addr, offset, width, flags)` tuples
    for valid `MemAlign` programs. For prove-side (`sel_prove = 1`)
    rows whose `width` column is sub-doubleword (∈ {1, 2, 4}), the
    ROM-permitted selector patterns force `prove_val[1] = 0`
    (`mem_align.pil:172-188`'s `prove_val` arithmetic), and via
    `value[1] = sel_prove · prove_val[1] + sel_assume · assume_val[1]`
    (`mem_align.pil:187`, extracted as `constraint_32_every_row`)
    this propagates to `value_1 = 0`.

    Project-trusted at the same scope as `bin_ext_table_consumer_wf`
    (`Airs/BinaryExtensionTable.lean:262`) — a ROM-lookup soundness
    statement scoped to a single state-machine ROM. -/
axiom mem_align_rom_subdoubleword_load_value_1_zero
    (ma : Valid_MemAlign FGL FGL) (r : ℕ)
    (h_live : ma.sel_prove r = 1)
    (h_narrow : ma.width r = 1 ∨ ma.width r = 2 ∨ ma.width r = 4) :
    ma.value_1 r = 0

/-! ## Per-AIR proven theorems

Discharge `e.x4..x7 = 0` (and per-width lo-byte zeros) from the
row-match predicate plus byte-range hypotheses on `e`. The
arithmetic is the standard Goldilocks-prime base-256 unique
decomposition: `Σ b_i · 256^i = 0` over `b_i ∈ [0, 256)` ⇒ all zero.
-/

/-- High-byte zeros for any LOAD-providing `MemAlignByte` row.
    Direct from `slot[5] = 0` ↔ `memory_entry_hi e = 0`. -/
lemma memalign_byte_load_high_bytes_zero
    (v : Valid_MemAlignByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_byte_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e) :
    e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0 := by
  obtain ⟨_, _, _, _, h_hi_zero, _⟩ := h_match
  obtain ⟨_, _, _, _, h4, h5, h6, h7⟩ := h_range
  simp only [memory_entry_hi] at h_hi_zero
  exact ZiskFv.PackedBitVec.four_bytes_zero_of_packed_zero
    e.x4 e.x5 e.x6 e.x7 h4 h5 h6 h7 h_hi_zero

/-- Width=1 collapses lo bytes 1..3 to zero. The `bus_byte` slot is
    range-checked to [0, 256) by the byte-bus, so `lo(e) = bus_byte`
    (a single-byte value) plus byte ranges on `e.x0..x3` forces
    `e.x1 = e.x2 = e.x3 = 0`.

    Note: this is not consumed by the derivation theorem (which only
    needs the high-byte zeros for the `high_bytes_zero_for_width`
    predicate's width=1 case to *also* need `e.x1..x3 = 0`); it is
    provided here for completeness with the predicate. The width=1
    low-byte pinning consumes a separate hypothesis (the byte-bus
    range check on `bus_byte`) which is supplied at the call site. -/
lemma memalign_byte_load_low_bytes_zero
    (v : Valid_MemAlignByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_byte_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e)
    (h_bus_byte_lt : (v.bus_byte r).val < 256) :
    e.x1 = 0 ∧ e.x2 = 0 ∧ e.x3 = 0 := by
  obtain ⟨_, _, _, h_lo, _, _⟩ := h_match
  obtain ⟨h0, h1, h2, h3, _, _, _, _⟩ := h_range
  simp only [memory_entry_lo] at h_lo
  -- lo(e) = bus_byte; lo(e).val = bus_byte.val < 256 forces e.x1..3 = 0.
  have h_lt : (e.x0 + e.x1 * 256 + e.x2 * 65536 + e.x3 * 16777216 : FGL).val < 256 := by
    rw [← h_lo]; exact h_bus_byte_lt
  exact ZiskFv.PackedBitVec.four_bytes_high_three_zero_of_packed_lt_256
    e.x0 e.x1 e.x2 e.x3 h0 h1 h2 h3 h_lt

/-- High-byte zeros for any LOAD-providing `MemAlignReadByte` row.
    Same shape as the MemAlignByte case (slot[5] = literal 0). -/
lemma memalign_read_byte_load_high_bytes_zero
    (v : Valid_MemAlignReadByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_read_byte_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e) :
    e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0 := by
  obtain ⟨_, _, _, h_hi_zero, _⟩ := h_match
  obtain ⟨_, _, _, _, h4, h5, h6, h7⟩ := h_range
  simp only [memory_entry_hi] at h_hi_zero
  exact ZiskFv.PackedBitVec.four_bytes_zero_of_packed_zero
    e.x4 e.x5 e.x6 e.x7 h4 h5 h6 h7 h_hi_zero

/-- Width=1 lo-bytes pinning for `MemAlignReadByte`, analogous to the
    MemAlignByte version. -/
lemma memalign_read_byte_load_low_bytes_zero
    (v : Valid_MemAlignReadByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_read_byte_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e)
    (h_byte_value_lt : (v.byte_value r).val < 256) :
    e.x1 = 0 ∧ e.x2 = 0 ∧ e.x3 = 0 := by
  obtain ⟨_, _, h_lo, _, _⟩ := h_match
  obtain ⟨h0, h1, h2, h3, _, _, _, _⟩ := h_range
  simp only [memory_entry_lo] at h_lo
  have h_lt : (e.x0 + e.x1 * 256 + e.x2 * 65536 + e.x3 * 16777216 : FGL).val < 256 := by
    rw [← h_lo]; exact h_byte_value_lt
  exact ZiskFv.PackedBitVec.four_bytes_high_three_zero_of_packed_lt_256
    e.x0 e.x1 e.x2 e.x3 h0 h1 h2 h3 h_lt

/-- High-byte zeros for any LOAD-providing `MemAlign` row whose
    width is sub-doubleword. Combines the row-match's
    `value_1 = hi(e)` with the ROM-lookup axiom's `value_1 = 0`. -/
lemma memalign_load_high_bytes_zero
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e)
    (h_narrow : v.width r = 1 ∨ v.width r = 2 ∨ v.width r = 4) :
    e.x4 = 0 ∧ e.x5 = 0 ∧ e.x6 = 0 ∧ e.x7 = 0 := by
  obtain ⟨h_live, _, _, _, _, _, _, h_v1_eq, _⟩ := h_match
  obtain ⟨_, _, _, _, h4, h5, h6, h7⟩ := h_range
  have h_v1_zero := mem_align_rom_subdoubleword_load_value_1_zero v r h_live h_narrow
  have h_hi_zero : memory_entry_hi e = 0 := by rw [← h_v1_eq, h_v1_zero]
  simp only [memory_entry_hi] at h_hi_zero
  exact ZiskFv.PackedBitVec.four_bytes_zero_of_packed_zero
    e.x4 e.x5 e.x6 e.x7 h4 h5 h6 h7 h_hi_zero

/-- Width-conditional low-byte pinning for `MemAlign`. For width=2,
    `value_0 = lo(e) < 65536`; for width=1, `value_0 = lo(e) < 256`.
    The byte-range argument needs an explicit bound on `value_0`
    coming from the ROM/AIR-internal width pinning — supplied at the
    derivation site as `h_v0_lt`. -/
lemma memalign_load_low_bytes_pinned_for_width_1
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e)
    (h_v0_lt : (v.value_0 r).val < 256) :
    e.x1 = 0 ∧ e.x2 = 0 ∧ e.x3 = 0 := by
  obtain ⟨_, _, _, _, _, _, h_v0_eq, _, _⟩ := h_match
  obtain ⟨h0, h1, h2, h3, _, _, _, _⟩ := h_range
  simp only [memory_entry_lo] at h_v0_eq
  have h_lt : (e.x0 + e.x1 * 256 + e.x2 * 65536 + e.x3 * 16777216 : FGL).val < 256 := by
    rw [← h_v0_eq]; exact h_v0_lt
  exact ZiskFv.PackedBitVec.four_bytes_high_three_zero_of_packed_lt_256
    e.x0 e.x1 e.x2 e.x3 h0 h1 h2 h3 h_lt

lemma memalign_load_low_bytes_pinned_for_width_2
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_row_matches_load_entry v r e)
    (h_range : memory_entry_bytes_in_range e)
    (h_v0_lt : (v.value_0 r).val < 65536) :
    e.x2 = 0 ∧ e.x3 = 0 := by
  obtain ⟨_, _, _, _, _, _, h_v0_eq, _, _⟩ := h_match
  obtain ⟨h0, h1, h2, h3, _, _, _, _⟩ := h_range
  simp only [memory_entry_lo] at h_v0_eq
  have h_lt : (e.x0 + e.x1 * 256 + e.x2 * 65536 + e.x3 * 16777216 : FGL).val < 65536 := by
    rw [← h_v0_eq]; exact h_v0_lt
  exact ZiskFv.PackedBitVec.four_bytes_high_two_zero_of_packed_lt_65536
    e.x0 e.x1 e.x2 e.x3 h0 h1 h2 h3 h_lt

/-! ## Derivation theorem

Composes `memalign_load_perm_sound` (Or over 3 providers) with the
per-AIR theorems above into the `high_bytes_zero_for_width`
predicate. -/

/-- Width=1 case requires width-conditional low-byte pinning, which
    in turn requires byte-range hypotheses on the provider's bus_byte
    / byte_value / value_0 column. The derivation packages all three
    via `h_low_pinning`. -/
structure SubdoublewordLoadLowBytePinning
    (mab : Valid_MemAlignByte FGL FGL)
    (marb : Valid_MemAlignReadByte FGL FGL)
    (ma : Valid_MemAlign FGL FGL) where
  byte_value_lt : ∀ r, (mab.bus_byte r).val < 256
  read_byte_value_lt : ∀ r, (marb.byte_value r).val < 256
  ma_value_0_lt_for_width_1 : ∀ r, ma.width r = 1 → (ma.value_0 r).val < 256
  ma_value_0_lt_for_width_2 : ∀ r, ma.width r = 2 → (ma.value_0 r).val < 65536

/-- **Derived theorem** replacing the old
    `memalign_load_high_bytes_zero` axiom. Given the perm axiom and
    the ROM axiom, plus byte-range hypotheses on `e` and width-conditional
    range pinning on the providers' lo-value columns, produce
    `high_bytes_zero_for_width e (main.ind_width r_main)`. -/
lemma memalign_subdoubleword_load_high_bytes_zero
    (main : Valid_Main FGL FGL)
    (mab : Valid_MemAlignByte FGL FGL)
    (marb : Valid_MemAlignReadByte FGL FGL)
    (ma : Valid_MemAlign FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (h_emit : main.b_0 r_main = memory_entry_lo e
              ∧ main.b_1 r_main = memory_entry_hi e
              ∧ e.as = 2 ∧ e.multiplicity = -1)
    (h_subdw : main.ind_width r_main = 1
             ∨ main.ind_width r_main = 2
             ∨ main.ind_width r_main = 4)
    (h_byte_range : memory_entry_bytes_in_range e)
    (h_low : SubdoublewordLoadLowBytePinning mab marb ma) :
    high_bytes_zero_for_width e (main.ind_width r_main) := by
  rcases memalign_load_perm_sound main mab marb ma r_main e h_emit h_subdw with
    ⟨r, h_match, h_w_eq⟩ | ⟨r, h_match, h_w_eq⟩ | ⟨r, h_match, h_w_eq⟩
  · -- MemAlignByte branch: provider's width is literal 1.
    obtain ⟨h4, h5, h6, h7⟩ :=
      memalign_byte_load_high_bytes_zero mab r e h_match h_byte_range
    obtain ⟨h1, h2, h3⟩ :=
      memalign_byte_load_low_bytes_zero mab r e h_match h_byte_range
        (h_low.byte_value_lt r)
    refine ⟨?_, ?_, ?_⟩ <;> intro h_w
    · exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
  · -- MemAlignReadByte branch: provider's width is literal 1.
    obtain ⟨h4, h5, h6, h7⟩ :=
      memalign_read_byte_load_high_bytes_zero marb r e h_match h_byte_range
    obtain ⟨h1, h2, h3⟩ :=
      memalign_read_byte_load_low_bytes_zero marb r e h_match h_byte_range
        (h_low.read_byte_value_lt r)
    refine ⟨?_, ?_, ?_⟩ <;> intro h_w
    · exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
  · -- MemAlign branch: width is the provider's `width` column.
    have h_narrow : ma.width r = 1 ∨ ma.width r = 2 ∨ ma.width r = 4 := by
      rcases h_subdw with h | h | h <;> rw [← h_w_eq] at h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨h4, h5, h6, h7⟩ :=
      memalign_load_high_bytes_zero ma r e h_match h_byte_range h_narrow
    refine ⟨?_, ?_, ?_⟩ <;> intro h_w
    · -- width = 1: also need lo bytes 1..3 zero.
      have h_w_provider : ma.width r = 1 := by rw [h_w_eq]; exact h_w
      obtain ⟨h1, h2, h3⟩ :=
        memalign_load_low_bytes_pinned_for_width_1 ma r e h_match h_byte_range
          (h_low.ma_value_0_lt_for_width_1 r h_w_provider)
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · -- width = 2: need lo bytes 2..3 zero.
      have h_w_provider : ma.width r = 2 := by rw [h_w_eq]; exact h_w
      obtain ⟨h2, h3⟩ :=
        memalign_load_low_bytes_pinned_for_width_2 ma r e h_match h_byte_range
          (h_low.ma_value_0_lt_for_width_2 r h_w_provider)
      exact ⟨h2, h3, h4, h5, h6, h7⟩
    · -- width = 4: only high bytes need to be zero.
      exact ⟨h4, h5, h6, h7⟩

end ZiskFv.Airs.MemoryBus.MemAlignBridge
