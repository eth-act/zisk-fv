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
import ZiskFv.AirsClean.MemAlignByte.Bridge
import ZiskFv.AirsClean.MemAlignReadByte.Bridge

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

This file consumes an explicit structural provider witness for the
MemAlign\* row selected by the Clean memory-bus route, then derives
`memalign_subdoubleword_load_high_bytes_zero` as a theorem. The witness
keeps the formerly implicit permutation/ROM facts visible to callers
instead of hiding them in trust-ledger axioms.
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

/-! ## Structural provider witness -/

/-- Concrete MemAlign-family provider selected for a sub-doubleword Main
load consumer.

This is the structural-unpacking replacement for the former
`memalign_load_perm_sound` and
`mem_align_rom_subdoubleword_load_value_1_zero` trust-ledger axioms.
The first two branches are direct MemAlignByte/MemAlignReadByte provider
rows whose bus tuple already carries a literal high chunk of zero. The
general MemAlign branch carries the selected provider row plus the
ROM-derived low/high value facts needed by the zero-padding theorem.

No protocol fact is hidden behind a top-level axiom here: callers must
provide the selected provider row and the exact branch facts. -/
structure SubdoublewordLoadProviderWitness
    (main : Valid_Main FGL FGL)
    (mab : Valid_MemAlignByte FGL FGL)
    (marb : Valid_MemAlignReadByte FGL FGL)
    (ma : Valid_MemAlign FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL) : Prop where
  provider :
    (∃ r, memalign_byte_row_matches_load_entry mab r e
        ∧ main.ind_width r_main = 1)
  ∨ (∃ r, memalign_read_byte_row_matches_load_entry marb r e
        ∧ main.ind_width r_main = 1)
  ∨ (∃ r, memalign_row_matches_load_entry ma r e
        ∧ ma.width r = main.ind_width r_main
        ∧ ma.value_1 r = 0
        ∧ (ma.width r = 1 → (ma.value_0 r).val < 256)
        ∧ (ma.width r = 2 → (ma.value_0 r).val < 65536))

/-! ## Per-AIR proven theorems

Discharge `e.value_1 = 0` (and per-width `e.value_0.val < bound`)
from the row-match predicate. Under the chunk-shape redesign
(C8 Phase 2), the previous per-byte derivations collapse to direct
chunk equalities; no Goldilocks-prime base-256 unique decomposition
is needed.
-/

/-- High-chunk zero for any LOAD-providing `MemAlignByte` row.
    Direct from the row-match's hi-chunk equation. -/
lemma memalign_byte_load_high_bytes_zero
    (v : Valid_MemAlignByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_byte_row_matches_load_entry v r e) :
    e.value_1 = 0 := by
  obtain ⟨_, _, _, _, h_hi_zero, _⟩ := h_match
  simp only [memory_entry_hi] at h_hi_zero
  exact h_hi_zero

/-- Width=1 byte-range on `value_0` for `MemAlignByte`. The `bus_byte`
    slot is range-checked to [0, 256) by the byte-bus, and the
    row-match's lo-chunk equation `memory_entry_lo e = bus_byte`
    transports the bound to `e.value_0`. -/
lemma memalign_byte_load_low_bytes_zero
    (v : Valid_MemAlignByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_byte_row_matches_load_entry v r e)
    (h_bus_byte_lt : (v.bus_byte r).val < 256) :
    e.value_0.val < 256 := by
  obtain ⟨_, _, _, h_lo, _, _⟩ := h_match
  simp only [memory_entry_lo] at h_lo
  rw [← h_lo]; exact h_bus_byte_lt

/-- Row-native MemAlignByte low-byte range from the Clean provider `Spec`.

This is the full-ensemble replacement surface for the older
`bus_byte_in_range_via_component` route: a selected Clean provider row
already carries its `Spec` through `witness.Spec`, and that `Spec` contains
the byte range supplied by the component's static lookup. -/
lemma memalign_byte_load_low_bytes_zero_of_clean_spec
    (row : ZiskFv.AirsClean.MemAlignByte.MemAlignByteRow FGL)
    (e : MemoryBusEntry FGL)
    (h_match :
      memalign_byte_row_matches_load_entry
        (ZiskFv.AirsClean.MemAlignByte.validOfRow row) 0 e)
    (h_spec : ZiskFv.AirsClean.MemAlignByte.Spec row) :
    e.value_0.val < 256 := by
  exact memalign_byte_load_low_bytes_zero
    (ZiskFv.AirsClean.MemAlignByte.validOfRow row) 0 e h_match
    (by
      simpa [ZiskFv.AirsClean.MemAlignByte.validOfRow] using
        h_spec.2.2.2.2.2.1)

/-- Adapt a Clean MemAlignByte provider message match back to the legacy
load-provider predicate used by the existing zero-padding bridge. -/
theorem memalign_byte_row_matches_load_entry_of_message_match_valid
    (mab : Valid_MemAlignByte FGL FGL) (r_mab : ℕ)
    (row : ZiskFv.AirsClean.MemAlignByte.MemAlignByteRow FGL)
    (e : MemoryBusEntry FGL)
    (h_row : row = ZiskFv.AirsClean.MemAlignByte.rowAt mab r_mab)
    (h_is_write : mab.is_write r_mab = 0)
    (h_match :
      matches_memory_entry e
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.MemAlignByte.memBusMessage row) 1 2)) :
    memalign_byte_row_matches_load_entry mab r_mab e := by
  obtain ⟨_h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
  rw [h_row] at h_ptr h_v0 h_v1 h_ts
  refine ⟨h_is_write, ?_, ?_, ?_, ?_, h_as⟩
  · rw [h_ptr]
    ring
  · simpa [ZiskFv.AirsClean.MemAlignByte.rowAt,
      ZiskFv.AirsClean.MemAlignByte.memBusMessage,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] using h_ts.symm
  · simpa [ZiskFv.AirsClean.MemAlignByte.rowAt,
      ZiskFv.AirsClean.MemAlignByte.memBusMessage,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
      memory_entry_lo] using h_v0.symm
  · simpa [ZiskFv.AirsClean.MemAlignByte.rowAt,
      ZiskFv.AirsClean.MemAlignByte.memBusMessage,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
      memory_entry_hi] using h_v1

/-- High-chunk zero for any LOAD-providing `MemAlignReadByte` row.
    Same shape as the MemAlignByte case (slot[5] = literal 0). -/
lemma memalign_read_byte_load_high_bytes_zero
    (v : Valid_MemAlignReadByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_read_byte_row_matches_load_entry v r e) :
    e.value_1 = 0 := by
  obtain ⟨_, _, _, h_hi_zero, _⟩ := h_match
  simp only [memory_entry_hi] at h_hi_zero
  exact h_hi_zero

/-- Width=1 byte-range on `value_0` for `MemAlignReadByte`, analogous
    to the MemAlignByte version. -/
lemma memalign_read_byte_load_low_bytes_zero
    (v : Valid_MemAlignReadByte FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_read_byte_row_matches_load_entry v r e)
    (h_byte_value_lt : (v.byte_value r).val < 256) :
    e.value_0.val < 256 := by
  obtain ⟨_, _, h_lo, _, _⟩ := h_match
  simp only [memory_entry_lo] at h_lo
  rw [← h_lo]; exact h_byte_value_lt

/-- Row-native MemAlignReadByte low-byte range from the Clean provider
`Spec`. This consumes the exact selected provider row supplied by the full
memory ensemble, rather than a caller-level byte-range promise. -/
lemma memalign_read_byte_load_low_bytes_zero_of_clean_spec
    (row : ZiskFv.AirsClean.MemAlignReadByte.MemAlignReadByteRow FGL)
    (e : MemoryBusEntry FGL)
    (h_match :
      memalign_read_byte_row_matches_load_entry
        (ZiskFv.AirsClean.MemAlignReadByte.validOfRow row) 0 e)
    (h_spec : ZiskFv.AirsClean.MemAlignReadByte.Spec row) :
    e.value_0.val < 256 := by
  exact memalign_read_byte_load_low_bytes_zero
    (ZiskFv.AirsClean.MemAlignReadByte.validOfRow row) 0 e h_match
    (by
      simpa [ZiskFv.AirsClean.MemAlignReadByte.validOfRow] using h_spec.2)

/-- Adapt a Clean MemAlignReadByte provider message match back to the legacy
load-provider predicate used by the existing zero-padding bridge. -/
theorem memalign_read_byte_row_matches_load_entry_of_message_match_valid
    (marb : Valid_MemAlignReadByte FGL FGL) (r_marb : ℕ)
    (row : ZiskFv.AirsClean.MemAlignReadByte.MemAlignReadByteRow FGL)
    (e : MemoryBusEntry FGL)
    (h_row : row = ZiskFv.AirsClean.MemAlignReadByte.rowAt marb r_marb)
    (h_match :
      matches_memory_entry e
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.MemAlignReadByte.memBusMessage row) 1 2)) :
    memalign_read_byte_row_matches_load_entry marb r_marb e := by
  obtain ⟨_h_mult, h_as, h_ptr, h_v0, h_v1, h_ts⟩ := h_match
  rw [h_row] at h_ptr h_v0 h_v1 h_ts
  refine ⟨?_, ?_, ?_, ?_, h_as⟩
  · rw [h_ptr]
    ring
  · simpa [ZiskFv.AirsClean.MemAlignReadByte.rowAt,
      ZiskFv.AirsClean.MemAlignReadByte.memBusMessage,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry] using h_ts.symm
  · simpa [ZiskFv.AirsClean.MemAlignReadByte.rowAt,
      ZiskFv.AirsClean.MemAlignReadByte.memBusMessage,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
      memory_entry_lo] using h_v0.symm
  · simpa [ZiskFv.AirsClean.MemAlignReadByte.rowAt,
      ZiskFv.AirsClean.MemAlignReadByte.memBusMessage,
      ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
      memory_entry_hi] using h_v1

/-- High-chunk zero for any LOAD-providing `MemAlign` row whose width
    is sub-doubleword. The `value_1 = 0` fact is supplied by the
    explicit structural provider witness, which is where the MemAlignRom
    lookup evidence is unpacked. -/
lemma memalign_load_high_bytes_zero
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_row_matches_load_entry v r e)
    (h_value_1_zero : v.value_1 r = 0) :
    e.value_1 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, h_v1_eq, _⟩ := h_match
  simp only [memory_entry_hi] at h_v1_eq
  rw [← h_v1_eq, h_value_1_zero]

/-- Width-conditional `value_0` range for `MemAlign`. For width=1,
    `value_0 = lo(e) < 256`; the byte-range argument comes from the
    ROM/AIR-internal width pinning, supplied at the derivation site
    as `h_v0_lt`. -/
lemma memalign_load_low_bytes_pinned_for_width_1
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_row_matches_load_entry v r e)
    (h_v0_lt : (v.value_0 r).val < 256) :
    e.value_0.val < 256 := by
  obtain ⟨_, _, _, _, _, _, h_v0_eq, _, _⟩ := h_match
  simp only [memory_entry_lo] at h_v0_eq
  rw [← h_v0_eq]; exact h_v0_lt

/-- Width=2 analogue: `value_0 = lo(e) < 65536`. -/
lemma memalign_load_low_bytes_pinned_for_width_2
    (v : Valid_MemAlign FGL FGL) (r : ℕ) (e : MemoryBusEntry FGL)
    (h_match : memalign_row_matches_load_entry v r e)
    (h_v0_lt : (v.value_0 r).val < 65536) :
    e.value_0.val < 65536 := by
  obtain ⟨_, _, _, _, _, _, h_v0_eq, _, _⟩ := h_match
  simp only [memory_entry_lo] at h_v0_eq
  rw [← h_v0_eq]; exact h_v0_lt

/-! ## Derivation theorem

Composes the structural provider witness with the per-AIR theorems above
into the `high_bytes_zero_for_width` predicate. -/

/- Width=1 case requires width-conditional low-byte pinning, which
    in turn requires byte-range hypotheses on the provider's
    byte_value / value_0 column. The derivation packages them via
    `h_low_pinning`.

    **C1 re-root:** the MemAlignByte `bus_byte < 256` bound is **no
    longer** a field here — it is derived from the MemAlignByte AIR's
    own `core_every_row` PIL constraints through the Clean Component
    (`AirsClean/MemAlignByte/Bridge.lean :: bus_byte_in_range_via_component`),
    not a caller-supplied promise.

    **C2 re-root:** likewise the MemAlignReadByte `byte_value < 256`
    bound is derived from the MemAlignReadByte AIR's own `core_every_row`
    PIL constraints plus lookup-aware Clean range evidence. The general
    MemAlign branch's low-value bounds are carried by the structural
    provider witness because the MemAlignRom table is not yet extracted
    as a first-class Lean table. -/

/-- **Derived theorem** replacing the old
    `memalign_load_high_bytes_zero` axiom. Given a structural provider
    witness plus byte-range facts derived from MemAlignByte /
    MemAlignReadByte Clean components, produce
    `high_bytes_zero_for_width e (main.ind_width r_main)`.

    **C1 re-root.** The MemAlignByte branch's `bus_byte < 256` bound
    is derived from `h_mab_core` (the MemAlignByte AIR's own
    `core_every_row` PIL constraints) and `h_mab_lookup` (the Clean
    `lookup rangeTable*` evidence) through the soundness-only
    `ranges_of_lookup_aware_const_soundness` projection — not from
    `range_bus_sound` and not through the Clean Component completeness field.

    **C2 re-root.** Likewise the MemAlignReadByte branch's
    `byte_value < 256` bound is derived from `h_marb_core` (the
    MemAlignReadByte AIR's own `core_every_row` PIL constraints)
    and `h_marb_lookup` (the Clean `lookup rangeTable8` evidence) through the
    soundness-only `byte_value_range_of_lookup_aware_const_soundness`
    projection — not from `range_bus_sound` and not through the Clean
    Component completeness field. -/
lemma memalign_subdoubleword_load_high_bytes_zero
    (main : Valid_Main FGL FGL)
    (mab : Valid_MemAlignByte FGL FGL)
    (marb : Valid_MemAlignReadByte FGL FGL)
    (ma : Valid_MemAlign FGL FGL)
    (r_main : ℕ) (e : MemoryBusEntry FGL)
    (_h_emit : main.b_0 r_main = memory_entry_lo e
              ∧ main.b_1 r_main = memory_entry_hi e
              ∧ e.as = 2 ∧ e.multiplicity = -1)
    (_h_subdw : main.ind_width r_main = 1
             ∨ main.ind_width r_main = 2
             ∨ main.ind_width r_main = 4)
    (_h_mab_core : ∀ r, ZiskFv.Airs.MemAlignByte.core_every_row mab r)
    (_h_marb_core : ∀ r, ZiskFv.Airs.MemAlignReadByte.core_every_row marb r)
    (h_mab_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignByte.RangeLookupWitness mab r)
    (h_marb_lookup :
      ∀ r, ZiskFv.AirsClean.MemAlignReadByte.RangeLookupWitness marb r)
    (h_provider : SubdoublewordLoadProviderWitness main mab marb ma r_main e) :
    high_bytes_zero_for_width e (main.ind_width r_main) := by
  rcases h_provider.provider with
    ⟨r, h_match, h_w_eq⟩ | ⟨r, h_match, h_w_eq⟩ |
      ⟨r, h_match, h_w_eq, h_value_1_zero, h_v0_lt_1, h_v0_lt_2⟩
  · -- MemAlignByte branch: provider's width is literal 1.
    have h_v1 := memalign_byte_load_high_bytes_zero mab r e h_match
    have h_mab_ranges :=
      ZiskFv.AirsClean.MemAlignByte.ranges_of_lookup_aware_const_soundness
        (h_mab_lookup r)
    have h_v0_lt := memalign_byte_load_low_bytes_zero mab r e h_match
      h_mab_ranges.1
    refine ⟨?_, ?_, ?_⟩ <;> intro h_w
    · exact ⟨h_v1, h_v0_lt⟩
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
  · -- MemAlignReadByte branch: provider's width is literal 1. The
    -- `byte_value < 256` bound is derived from the MemAlignReadByte
    -- lookup-aware Clean range projection, not a caller promise.
    have h_v1 := memalign_read_byte_load_high_bytes_zero marb r e h_match
    have h_v0_lt := memalign_read_byte_load_low_bytes_zero marb r e h_match
      (ZiskFv.AirsClean.MemAlignReadByte.byte_value_range_of_lookup_aware_const_soundness
        (h_marb_lookup r))
    refine ⟨?_, ?_, ?_⟩ <;> intro h_w
    · exact ⟨h_v1, h_v0_lt⟩
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
    · exfalso; rw [h_w_eq] at h_w; exact absurd h_w (by decide)
  · -- MemAlign branch: width is the provider's `width` column.
    have h_v1 := memalign_load_high_bytes_zero ma r e h_match h_value_1_zero
    refine ⟨?_, ?_, ?_⟩ <;> intro h_w
    · -- width = 1: also need value_0 < 256.
      have h_w_provider : ma.width r = 1 := by rw [h_w_eq]; exact h_w
      have h_v0_lt := memalign_load_low_bytes_pinned_for_width_1 ma r e h_match
        (h_v0_lt_1 h_w_provider)
      exact ⟨h_v1, h_v0_lt⟩
    · -- width = 2: need value_0 < 65536.
      have h_w_provider : ma.width r = 2 := by rw [h_w_eq]; exact h_w
      have h_v0_lt := memalign_load_low_bytes_pinned_for_width_2 ma r e h_match
        (h_v0_lt_2 h_w_provider)
      exact ⟨h_v1, h_v0_lt⟩
    · -- width = 4: only high chunk needs to be zero.
      exact h_v1

end ZiskFv.Airs.MemoryBus.MemAlignBridge
