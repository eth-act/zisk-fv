import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Binary.BinaryExtensionPackedCorrect
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.Channels.RangeBusSoundness

/-!
# BinaryExtension AIR — universal column-range theorems

Mirrors `ZiskFv/Airs/Binary/BinaryRanges.lean` for the
`BinaryExtension` AIR. PIL declares the per-row column widths
(`zisk/state-machines/binary/pil/binary_extension.pil:82-96`):

```pil
col witness bits(6)  op;
col witness bits(8)  free_in_a[BYTES];    // < 2^8 each (8 bytes)
col witness bits(8)  free_in_b;           // < 2^8 (single shift-amount byte)
col witness bits(32) free_in_c[BYTES][2]; // < 2^32 each (16 entries: 8 byte_i × {c_lo, c_hi})
col witness bits(1)  op_is_shift;         // < 2
col witness bits(32) b[2];                // < 2^32 each
```

Each `bits(N)` annotation compiles in `pil2-compiler` to a row-level
lookup against the standard range-checker bus; lookup-argument
soundness on that bus IS the trust assumption (same class as
`binary_columns_in_range`, `binary_add_columns_in_range`,
`main_columns_in_range`, `bin_table_consumer_wf`).

Trust class: lookup-argument soundness on the standard range-checker
bus.
-/

namespace ZiskFv.Airs.BinaryExtension

open Goldilocks
open ZiskFv.Channels.RangeBusSoundness


/-- **BinaryExtension range-check soundness (derived).** Given the
    row-level `lookup_assumes(RANGE_BUS_ID, …)` interactions induced
    by BinaryExtension's `bits(N)` column annotations, every row's
    witness cells satisfy their declared bit ranges.

    Previously an axiom; now derived from `range_bus_sound` via 27
    applications (one per column).

    PIL citations (`zisk/state-machines/binary/pil/binary_extension.pil:82-96`):
    * `bits(8) free_in_a[BYTES]` → `free_in_a_0..7` < 2⁸
    * `bits(8) free_in_b`        → `free_in_b`     < 2⁸
    * `bits(32) free_in_c[BYTES][2]` → `free_in_c_0..15` < 2³²
    * `bits(32) b[2]`            → `b_0`, `b_1`    < 2³² -/
theorem binary_extension_columns_in_range (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_0 r).val < 256 ∧ (e.free_in_a_1 r).val < 256
  ∧ (e.free_in_a_2 r).val < 256 ∧ (e.free_in_a_3 r).val < 256
  ∧ (e.free_in_a_4 r).val < 256 ∧ (e.free_in_a_5 r).val < 256
  ∧ (e.free_in_a_6 r).val < 256 ∧ (e.free_in_a_7 r).val < 256
  ∧ (e.free_in_b r).val < 256
  ∧ (e.free_in_c_0 r).val < 4294967296 ∧ (e.free_in_c_1 r).val < 4294967296
  ∧ (e.free_in_c_2 r).val < 4294967296 ∧ (e.free_in_c_3 r).val < 4294967296
  ∧ (e.free_in_c_4 r).val < 4294967296 ∧ (e.free_in_c_5 r).val < 4294967296
  ∧ (e.free_in_c_6 r).val < 4294967296 ∧ (e.free_in_c_7 r).val < 4294967296
  ∧ (e.free_in_c_8 r).val < 4294967296 ∧ (e.free_in_c_9 r).val < 4294967296
  ∧ (e.free_in_c_10 r).val < 4294967296 ∧ (e.free_in_c_11 r).val < 4294967296
  ∧ (e.free_in_c_12 r).val < 4294967296 ∧ (e.free_in_c_13 r).val < 4294967296
  ∧ (e.free_in_c_14 r).val < 4294967296 ∧ (e.free_in_c_15 r).val < 4294967296
  ∧ (e.b_0 r).val < 4294967296 ∧ (e.b_1 r).val < 4294967296 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
  · exact range_bus_sound e (fun e r => e.free_in_a_0 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_1 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_2 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_3 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_4 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_5 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_6 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_a_7 r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_b r) 8 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_0 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_1 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_2 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_3 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_4 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_5 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_6 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_7 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_8 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_9 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_10 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_11 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_12 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_13 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_14 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.free_in_c_15 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.b_0 r) 32 trivial r
  · exact range_bus_sound e (fun e r => e.b_1 r) 32 trivial r

/-! ## Specialized accessors -/

lemma be_a_0_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_0 r).val < 256 := (binary_extension_columns_in_range e r).1
lemma be_a_1_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_1 r).val < 256 := (binary_extension_columns_in_range e r).2.1
lemma be_a_2_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_2 r).val < 256 := (binary_extension_columns_in_range e r).2.2.1
lemma be_a_3_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_3 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.1
lemma be_a_4_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_4 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.1
lemma be_a_5_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_5 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.1
lemma be_a_6_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_6 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.2.1
lemma be_a_7_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_a_7 r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.2.2.1
lemma be_b_lt_256 (e : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    (e.free_in_b r).val < 256 := (binary_extension_columns_in_range e r).2.2.2.2.2.2.2.2.1

open ZiskFv.Airs.Tables.BinaryExtensionTable in
/-- **BinaryExtension row → 8-byte table-entry witness.** For every row
    `r` of a `Valid_BinaryExtension` AIR, the 8 per-byte lookups against
    the `BinaryExtensionTable` (per PIL `binary_extension.pil:92`:
    `lookup_assumes(BINARY_EXTENSION_TABLE_ID, [op, j, free_in_a[j],
    free_in_b, free_in_c[j][0], free_in_c[j][1], op_is_shift])`) are
    witnessed by 8 `BinaryExtensionTableEntry` consumers at multiplicity
    1, one per byte slot j ∈ {0..7}.

    The struct `ByteLookupHypotheses` (in
    `Airs/Binary/BinaryExtensionPackedCorrect.lean`) packages these 8
    table entries together with the row→entry projection equations.

    This theorem only constructs the row-shaped lookup entries. Their table
    semantics still flow through `bin_ext_table_consumer_wf`, which is the
    remaining BinaryExtensionTable lookup-soundness boundary. -/
def binary_extension_row_byte_lookups (v : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    ByteLookupHypotheses v r :=
  { e0 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 0
        a_byte := v.free_in_a_0 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_0 r
        c_hi_byte := v.free_in_c_1 r
        op_is_shift := v.op_is_shift r }
    h0 := by simp
    e1 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 1
        a_byte := v.free_in_a_1 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_2 r
        c_hi_byte := v.free_in_c_3 r
        op_is_shift := v.op_is_shift r }
    h1 := by simp
    e2 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 2
        a_byte := v.free_in_a_2 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_4 r
        c_hi_byte := v.free_in_c_5 r
        op_is_shift := v.op_is_shift r }
    h2 := by simp
    e3 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 3
        a_byte := v.free_in_a_3 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_6 r
        c_hi_byte := v.free_in_c_7 r
        op_is_shift := v.op_is_shift r }
    h3 := by simp
    e4 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 4
        a_byte := v.free_in_a_4 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_8 r
        c_hi_byte := v.free_in_c_9 r
        op_is_shift := v.op_is_shift r }
    h4 := by simp
    e5 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 5
        a_byte := v.free_in_a_5 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_10 r
        c_hi_byte := v.free_in_c_11 r
        op_is_shift := v.op_is_shift r }
    h5 := by simp
    e6 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 6
        a_byte := v.free_in_a_6 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_12 r
        c_hi_byte := v.free_in_c_13 r
        op_is_shift := v.op_is_shift r }
    h6 := by simp
    e7 :=
      { multiplicity := 1
        op := v.op r
        byte_index := 7
        a_byte := v.free_in_a_7 r
        shift_amount := v.free_in_b r
        c_lo_byte := v.free_in_c_14 r
        c_hi_byte := v.free_in_c_15 r
        op_is_shift := v.op_is_shift r }
    h7 := by simp }

open ZiskFv.AirsClean.BinaryExtension in
/-- Static-lookup route from the shared C7 witness to the eight semantic
    `wf_properties` facts for BinaryExtension's row-shaped byte lookups. -/
theorem binary_extension_row_byte_lookup_wfs_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : StaticLookupSoundness v) :
    ByteLookupWfHypotheses (binary_extension_row_byte_lookups v r) := by
  have h_wfs := static_lookup_wf_facts v r offset env h_static
  simpa [binary_extension_row_byte_lookups, rowAt,
    ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using h_wfs

/-! ## op_is_shift linkage -/

open ZiskFv.Trusted in
private theorem binary_extension_op_is_shift_pin_of_e0_wf
    (v : Valid_BinaryExtension FGL FGL) (r : ℕ)
    (h_wf :
      ZiskFv.Airs.Tables.BinaryExtensionTable.wf_properties
        (binary_extension_row_byte_lookups v r).e0) :
    ((v.op r = OP_SLL ∨ v.op r = OP_SRL ∨ v.op r = OP_SRA
      ∨ v.op r = OP_SLL_W ∨ v.op r = OP_SRL_W ∨ v.op r = OP_SRA_W)
        → v.op_is_shift r = 1)
  ∧ ((v.op r = OP_SIGNEXTEND_B ∨ v.op r = OP_SIGNEXTEND_H ∨ v.op r = OP_SIGNEXTEND_W)
        → v.op_is_shift r = 0) := by
  open ZiskFv.Airs.Tables.BinaryExtensionTable in
  let hbytes := binary_extension_row_byte_lookups v r
  have h_wf' : wf_properties hbytes.e0 := by
    simpa [hbytes] using h_wf
  rcases h_wf' with
    ⟨_hrange, hSLL, hSRL, hSRA, hSLLW, hSRLW, hSRAW, hSEXTB, hSEXTH, hSEXTW⟩
  constructor
  · intro h_op
    rcases h_op with h_op | h_op | h_op | h_op | h_op | h_op
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SLL,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL]
      have h_flag := (hSLL h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SRL,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL]
      have h_flag := (hSRL h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SRA,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA]
      have h_flag := (hSRA h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SLL_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SLL_W]
      have h_flag := (hSLLW h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SRL_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRL_W]
      have h_flag := (hSRLW h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SRA_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SRA_W]
      have h_flag := (hSRAW h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
  · intro h_op
    rcases h_op with h_op | h_op | h_op
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SIGNEXTEND_B,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_B]
      have h_flag := (hSEXTB h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SIGNEXTEND_H,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_H]
      have h_flag := (hSEXTH h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag
    · have h_op_val : hbytes.e0.op.val = ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W := by
        simp [hbytes, binary_extension_row_byte_lookups, h_op, ZiskFv.Trusted.OP_SIGNEXTEND_W,
          ZiskFv.Airs.Tables.BinaryExtensionTable.OP_SEXT_W]
      have h_flag := (hSEXTW h_op_val).2.2
      ext
      simpa [hbytes, binary_extension_row_byte_lookups] using h_flag

open ZiskFv.Trusted in
/-- Static-lookup variant of `binary_extension_op_is_shift_pin`. This consumes
    the shared C7 static-provider witness rather than
    `bin_ext_table_consumer_wf`. -/
theorem binary_extension_op_is_shift_pin_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v) :
    ((v.op r = OP_SLL ∨ v.op r = OP_SRL ∨ v.op r = OP_SRA
      ∨ v.op r = OP_SLL_W ∨ v.op r = OP_SRL_W ∨ v.op r = OP_SRA_W)
        → v.op_is_shift r = 1)
  ∧ ((v.op r = OP_SIGNEXTEND_B ∨ v.op r = OP_SIGNEXTEND_H ∨ v.op r = OP_SIGNEXTEND_W)
        → v.op_is_shift r = 0) := by
  open ZiskFv.Airs.Tables.BinaryExtensionTable in
  have h_facts :=
    ZiskFv.AirsClean.BinaryExtension.static_lookup_wf_facts v r offset env h_static
  have h_wf :
      wf_properties (binary_extension_row_byte_lookups v r).e0 := by
    simpa [binary_extension_row_byte_lookups,
      ZiskFv.AirsClean.BinaryExtension.StaticBinaryExtensionTableWfFacts,
      ZiskFv.AirsClean.BinaryExtension.rowAt,
      ZiskFv.Channels.BinaryExtensionTable.BinaryExtensionTableMessage.toEntry] using h_facts.1
  exact binary_extension_op_is_shift_pin_of_e0_wf v r h_wf

open ZiskFv.Trusted in
/-- Variant of `binary_extension_op_is_shift_pin_of_static_lookup` for callers
    that already projected the row's BinaryExtensionTable facts. -/
theorem binary_extension_op_is_shift_pin_of_wf_hypotheses
    (v : Valid_BinaryExtension FGL FGL) (r : ℕ)
    (h_wfs : ByteLookupWfHypotheses (binary_extension_row_byte_lookups v r)) :
    ((v.op r = OP_SLL ∨ v.op r = OP_SRL ∨ v.op r = OP_SRA
      ∨ v.op r = OP_SLL_W ∨ v.op r = OP_SRL_W ∨ v.op r = OP_SRA_W)
        → v.op_is_shift r = 1)
  ∧ ((v.op r = OP_SIGNEXTEND_B ∨ v.op r = OP_SIGNEXTEND_H ∨ v.op r = OP_SIGNEXTEND_W)
        → v.op_is_shift r = 0) :=
  binary_extension_op_is_shift_pin_of_e0_wf v r h_wfs.1

open ZiskFv.Trusted in
lemma op_is_shift_one_SLL_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SLL) :
    v.op_is_shift r = 1 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).1
    (Or.inl h_op)

open ZiskFv.Trusted in
lemma op_is_shift_one_SRL_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SRL) :
    v.op_is_shift r = 1 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).1
    (Or.inr (Or.inl h_op))

open ZiskFv.Trusted in
lemma op_is_shift_one_SRA_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SRA) :
    v.op_is_shift r = 1 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).1
    (Or.inr (Or.inr (Or.inl h_op)))

open ZiskFv.Trusted in
lemma op_is_shift_one_SLL_W_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SLL_W) :
    v.op_is_shift r = 1 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).1
    (Or.inr (Or.inr (Or.inr (Or.inl h_op))))

open ZiskFv.Trusted in
lemma op_is_shift_one_SRL_W_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SRL_W) :
    v.op_is_shift r = 1 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_op)))))

open ZiskFv.Trusted in
lemma op_is_shift_one_SRA_W_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SRA_W) :
    v.op_is_shift r = 1 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_op)))))

open ZiskFv.Trusted in
lemma op_is_shift_zero_SIGNEXTEND_B_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SIGNEXTEND_B) :
    v.op_is_shift r = 0 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).2
    (Or.inl h_op)

open ZiskFv.Trusted in
lemma op_is_shift_zero_SIGNEXTEND_H_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SIGNEXTEND_H) :
    v.op_is_shift r = 0 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).2
    (Or.inr (Or.inl h_op))

open ZiskFv.Trusted in
lemma op_is_shift_zero_SIGNEXTEND_W_of_static_lookup
    (v : Valid_BinaryExtension FGL FGL) (r offset : ℕ) (env : Environment FGL)
    (h_static : ZiskFv.AirsClean.BinaryExtension.StaticLookupSoundness v)
    (h_op : v.op r = OP_SIGNEXTEND_W) :
    v.op_is_shift r = 0 :=
  (binary_extension_op_is_shift_pin_of_static_lookup v r offset env h_static).2
    (Or.inr (Or.inr h_op))

open ZiskFv.Trusted in
/-- **BinaryExtension AIR op_is_shift linkage.** The `op_is_shift`
    column is `bits(1)` (per `binary_extension.pil:88`: `col witness
    bits(1) op_is_shift; // 1 if operation is in the shift family;
    0 otherwise`) and the per-byte table lookup at
    `binary_extension.pil:92` binds it to the table entry's
    `op_is_shift` flag — so every row whose `op` is a shift literal
    has `op_is_shift = 1`, and every row whose `op` is a SEXT literal
    has `op_is_shift = 0`.

    Derived from the row-shaped byte lookup entry plus
    `bin_ext_table_consumer_wf`; the table predicates already pin the
    `op_is_shift` flag for every shift and SEXT opcode. -/
theorem binary_extension_op_is_shift_pin (v : Valid_BinaryExtension FGL FGL) (r : ℕ) :
    ((v.op r = OP_SLL ∨ v.op r = OP_SRL ∨ v.op r = OP_SRA
      ∨ v.op r = OP_SLL_W ∨ v.op r = OP_SRL_W ∨ v.op r = OP_SRA_W)
        → v.op_is_shift r = 1)
  ∧ ((v.op r = OP_SIGNEXTEND_B ∨ v.op r = OP_SIGNEXTEND_H ∨ v.op r = OP_SIGNEXTEND_W)
        → v.op_is_shift r = 0) := by
  open ZiskFv.Airs.Tables.BinaryExtensionTable in
  let hbytes := binary_extension_row_byte_lookups v r
  have h_wf := bin_ext_table_consumer_wf hbytes.e0 hbytes.h0.1
  exact binary_extension_op_is_shift_pin_of_e0_wf v r (by simpa [hbytes] using h_wf)

end ZiskFv.Airs.BinaryExtension
