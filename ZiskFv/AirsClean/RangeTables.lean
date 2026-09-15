import Clean.Circuit.Lookup
import ZiskFv.Field.Goldilocks

/-!
# Clean static range tables

Constructive `StaticTable`s for ZisK range lookups.  These tables are
symbolic: `row` decodes an index to the corresponding field element and
`contains_iff` is proved structurally, so large tables such as `2^32`
do not require materializing millions of rows.

## Trust note

No axioms.  `StaticTable.toTable` turns membership into the stated
`Spec`, and every table below proves `contains_iff` from the concrete
indexing function.
-/

namespace ZiskFv.AirsClean.RangeTables

open Goldilocks

/-- A range-check `StaticTable`: rows `0, 1, ..., len - 1` as field
    elements, with membership equivalent to `t.val < len`. -/
def rangeStaticTable (len : ℕ) (h_len : len ≤ GL_prime) (name : String) :
    StaticTable FGL field where
  name := name
  length := len
  row i := (i.val : FGL)
  index t := t.val
  Spec t := t.val < len
  contains_iff := by
    intro t
    constructor
    · rintro ⟨i, rfl⟩
      show ((i.val : FGL)).val < len
      rw [Fin.val_natCast]
      omega
    · intro h
      refine ⟨⟨t.val, h⟩, ?_⟩
      show t = ((t.val : FGL))
      apply Fin.ext
      rw [Fin.val_natCast]
      omega

def rangeTable1 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 1) (by decide) "range-1"

def rangeTable4 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 4) (by decide) "range-4"

def rangeTable7 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 7) (by decide) "range-7"

def rangeTable8 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 8) (by decide) "range-8"

def rangeTable16 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 16) (by decide) "range-16"

def rangeTable17 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 17) (by decide) "range-17"

def rangeTable22 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 22) (by decide) "range-22"

def rangeTable24 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 24) (by decide) "range-24"

def rangeTable29 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 29) (by decide) "range-29"

def rangeTable32 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 32) (by decide) "range-32"

def rangeTable40 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 40) (by decide) "range-40"

set_option maxRecDepth 10000

/-! ## Arith indexed range table

`arith_range_table.pil` compresses 43 chunk range IDs into 68 half-blocks of
`2^15` rows, then appends the carry range under ID 100.  The row decoder below
is the same block layout as upstream `arith_range_table_helpers.rs::OFFSETS`.
-/

def arithRangeHalfBlockSize : ℕ := 32768

def arithRangeChunkRows : ℕ := 2228224

def arithRangeTableLength : ℕ := 4194304

/-- Range ID for a `2^15`-sized half-block in the chunk portion of
    `ArithRangeTable`. Full 16-bit IDs occupy two consecutive half-blocks. -/
def arithRangeHalfBlockId : ℕ → ℕ
  | 0 => 0 | 1 => 0
  | 2 => 1 | 3 => 1
  | 4 => 2 | 5 => 2
  | 6 => 9 | 7 => 9
  | 8 => 10 | 9 => 10
  | 10 => 11 | 11 => 11
  | 12 => 12 | 13 => 12
  | 14 => 13 | 15 => 13
  | 16 => 14 | 17 => 14
  | 18 => 15 | 19 => 15
  | 20 => 16 | 21 => 16
  | 22 => 17 | 23 => 17
  | 24 => 20 | 25 => 20
  | 26 => 23 | 27 => 23
  | 28 => 26 | 29 => 26
  | 30 => 27 | 31 => 27
  | 32 => 28 | 33 => 28
  | 34 => 29 | 35 => 29
  | 36 => 30 | 37 => 30
  | 38 => 31 | 39 => 31
  | 40 => 32 | 41 => 32
  | 42 => 33 | 43 => 33
  | 44 => 34 | 45 => 34
  | 46 => 35 | 47 => 35
  | 48 => 36 | 49 => 36
  | 50 => 3 | 51 => 4 | 52 => 5 | 53 => 18 | 54 => 21
  | 55 => 24 | 56 => 37 | 57 => 38 | 58 => 39
  | 59 => 6 | 60 => 7 | 61 => 8 | 62 => 19 | 63 => 22
  | 64 => 25 | 65 => 40 | 66 => 41 | 67 => 42
  | _ => 0

/-- Whether a half-block stores the upper half of a FULL `0..0xffff` range. -/
def arithRangeHalfBlockHighFull : ℕ → Bool
  | 1 | 3 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 19 | 21 | 23 | 25 | 27 | 29 | 31
  | 33 | 35 | 37 | 39 | 41 | 43 | 45 | 47 | 49 => true
  | _ => false

/-- Whether a half-block stores a NEG `0x8000..0xffff` range. -/
def arithRangeHalfBlockNeg : ℕ → Bool
  | 59 | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 => true
  | _ => false

def arithRangeChunkValue (block rem : ℕ) : ℕ :=
  rem + if arithRangeHalfBlockHighFull block || arithRangeHalfBlockNeg block then 32768 else 0

/-- Field value in the carry portion of the upstream Arith range table.

The PIL/Rust table uses the signed interval `[-0xEFFFF, 0xF0000]`, encoded in
Goldilocks representatives. -/
def arithRangeCarryValue (j : ℕ) (hj : j < 1966080) : FGL :=
  if h : j < 983039 then
    ⟨GL_prime - 983039 + j, by omega⟩
  else
    ⟨j - 983039, by omega⟩

def arithRangeTableRow (i : Fin arithRangeTableLength) : fields 2 FGL :=
  if h_chunk : i.val < arithRangeChunkRows then
    let block := i.val / arithRangeHalfBlockSize
    let rem := i.val % arithRangeHalfBlockSize
    #v[(arithRangeHalfBlockId block : FGL), (arithRangeChunkValue block rem : FGL)]
  else
    #v[(100 : FGL), arithRangeCarryValue (i.val - arithRangeChunkRows) (by omega)]

/-- ZisK's indexed Arith range table as an exact Clean static table.

`Spec` is exact row membership in the constructive decoder above.  Helper
lemmas below project the POS/NEG facts needed by signed-row witnesses. -/
def arithRangeTable : StaticTable FGL (fields 2) where
  name := "arith_range_table"
  length := arithRangeTableLength
  row := arithRangeTableRow
  index t := t[0].val * 65536 + t[1].val
  Spec t := ∃ i : Fin arithRangeTableLength, t = arithRangeTableRow i
  contains_iff := by intro t; rfl

theorem arithRangeTable_spec_iff (t : fields 2 FGL) :
    arithRangeTable.Spec t ↔ ∃ i : Fin arithRangeTableLength, t = arithRangeTableRow i :=
  Iff.rfl

private theorem arithRangeTable_pos_bound_of_spec_aux
    {rangeId : ℕ} {x : FGL}
    (h_pos_id : rangeId = 3 ∨ rangeId = 4 ∨ rangeId = 5 ∨ rangeId = 18
      ∨ rangeId = 21 ∨ rangeId = 24 ∨ rangeId = 37 ∨ rangeId = 38
      ∨ rangeId = 39)
    (h : arithRangeTable.Spec #v[(rangeId : FGL), x]) :
    x.val < 32768 := by
  rcases h with ⟨i, hrow⟩
  by_cases h_chunk : i.val < arithRangeChunkRows
  · simp [arithRangeTableRow, h_chunk, arithRangeHalfBlockSize,
      arithRangeChunkRows, arithRangeChunkValue] at hrow
    rcases hrow with ⟨hid, hx⟩
    have h_block : i.val / 32768 < 68 := by omega
    interval_cases h_block_val : i.val / 32768 <;>
      simp [arithRangeHalfBlockId, arithRangeHalfBlockHighFull,
        arithRangeHalfBlockNeg] at hid hx h_pos_id ⊢ <;> omega
  · simp [arithRangeTableRow, h_chunk] at hrow
    rcases hrow with ⟨hid, _hx⟩
    have hval := congrArg Fin.val hid
    simp at hval
    omega

private theorem arithRangeTable_neg_bound_of_spec_aux
    {rangeId : ℕ} {x : FGL}
    (h_neg_id : rangeId = 6 ∨ rangeId = 7 ∨ rangeId = 8 ∨ rangeId = 19
      ∨ rangeId = 22 ∨ rangeId = 25 ∨ rangeId = 40 ∨ rangeId = 41
      ∨ rangeId = 42)
    (h : arithRangeTable.Spec #v[(rangeId : FGL), x]) :
    32768 ≤ x.val ∧ x.val < 65536 := by
  rcases h with ⟨i, hrow⟩
  by_cases h_chunk : i.val < arithRangeChunkRows
  · simp [arithRangeTableRow, h_chunk, arithRangeHalfBlockSize,
      arithRangeChunkRows, arithRangeChunkValue] at hrow
    rcases hrow with ⟨hid, hx⟩
    have h_block : i.val / 32768 < 68 := by omega
    interval_cases h_block_val : i.val / 32768 <;>
      simp [arithRangeHalfBlockId, arithRangeHalfBlockHighFull,
        arithRangeHalfBlockNeg] at hid hx h_neg_id ⊢ <;> omega
  · simp [arithRangeTableRow, h_chunk] at hrow
    rcases hrow with ⟨hid, _hx⟩
    have hval := congrArg Fin.val hid
    simp at hval
    omega

theorem arithRangeTable_pos_bound_of_spec
    {rangeId : ℕ} {x : FGL}
    (h_pos_id : rangeId = 3 ∨ rangeId = 4 ∨ rangeId = 5 ∨ rangeId = 18
      ∨ rangeId = 21 ∨ rangeId = 24 ∨ rangeId = 37 ∨ rangeId = 38
      ∨ rangeId = 39)
    (h : arithRangeTable.Spec #v[(rangeId : FGL), x]) :
    x.val < 32768 :=
  arithRangeTable_pos_bound_of_spec_aux h_pos_id h

theorem arithRangeTable_neg_bound_of_spec
    {rangeId : ℕ} {x : FGL}
    (h_neg_id : rangeId = 6 ∨ rangeId = 7 ∨ rangeId = 8 ∨ rangeId = 19
      ∨ rangeId = 22 ∨ rangeId = 25 ∨ rangeId = 40 ∨ rangeId = 41
      ∨ rangeId = 42)
    (h : arithRangeTable.Spec #v[(rangeId : FGL), x]) :
    32768 ≤ x.val ∧ x.val < 65536 :=
  arithRangeTable_neg_bound_of_spec_aux h_neg_id h

/-- Signed Arith carry range table.

Rows are the field encodings of `[-0xEFFFF, 0xF0000]`, i.e. the low
non-negative representatives `0..983040` plus the high Goldilocks
representatives `GL_prime - 983040 .. GL_prime - 1`. -/
def signedCarryRangeTable : StaticTable FGL field where
  name := "arith-signed-carry-range"
  length := 1966081
  row i :=
    if h : i.val < 983041 then
      ⟨i.val, by omega⟩
    else
      ⟨GL_prime - 983040 + (i.val - 983041), by omega⟩
  index t :=
    if t.val < 983041 then
      t.val
    else if GL_prime - 983040 ≤ t.val then
      983041 + (t.val - (GL_prime - 983040))
    else
      0
  Spec t := t.val < 983041 ∨ GL_prime - 983040 ≤ t.val
  contains_iff := by
    intro t
    constructor
    · rintro ⟨i, rfl⟩
      dsimp
      split
      · left
        assumption
      · right
        change GL_prime - 983040 ≤ GL_prime - 983040 + (i.val - 983041)
        omega
    · intro h
      rcases h with h_low | h_high
      · refine ⟨⟨t.val, by omega⟩, ?_⟩
        change t =
          (if h : t.val < 983041 then
            (⟨t.val, by omega⟩ : FGL)
          else
            (⟨GL_prime - 983040 + (t.val - 983041), by omega⟩ : FGL))
        split
        · apply Fin.ext
          rfl
        · omega
      · refine ⟨⟨983041 + (t.val - (GL_prime - 983040)), by omega⟩, ?_⟩
        change t =
          (if h : 983041 + (t.val - (GL_prime - 983040)) < 983041 then
            (⟨983041 + (t.val - (GL_prime - 983040)), by omega⟩ : FGL)
          else
            (⟨GL_prime - 983040 +
              ((983041 + (t.val - (GL_prime - 983040))) - 983041), by omega⟩ : FGL))
        split
        · omega
        · apply Fin.ext
          change t.val = GL_prime - 983040 +
            ((983041 + (t.val - (GL_prime - 983040))) - 983041)
          omega

end ZiskFv.AirsClean.RangeTables
