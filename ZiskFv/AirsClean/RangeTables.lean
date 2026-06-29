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

/-! ## Arith indexed range table -/

/-- Rows per half range block in upstream `arith_range_table.pil`. -/
def arithRangeHalfBlockSize : ℕ := 32768

/-- Number of rows occupied by the 68 half-block chunk-range region. -/
def arithRangeChunkRows : ℕ := 2228224

/-- Total upstream `ArithRangeTable` length (`2^22`). -/
def arithRangeTableLength : ℕ := 4194304

/-- Upstream range ID for a half-block of the chunk-range region.

The values are the Rust helper `RANGES/OFFSETS` inverse:
`offset * 0x8000 + adjusted_value`.  FULL ranges occupy two adjacent
half-blocks; POS/NEG ranges occupy one half-block each. -/
def arithRangeHalfBlockId : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 9
  | 7 => 9
  | 8 => 10
  | 9 => 10
  | 10 => 11
  | 11 => 11
  | 12 => 12
  | 13 => 12
  | 14 => 13
  | 15 => 13
  | 16 => 14
  | 17 => 14
  | 18 => 15
  | 19 => 15
  | 20 => 16
  | 21 => 16
  | 22 => 17
  | 23 => 17
  | 24 => 20
  | 25 => 20
  | 26 => 23
  | 27 => 23
  | 28 => 26
  | 29 => 26
  | 30 => 27
  | 31 => 27
  | 32 => 28
  | 33 => 28
  | 34 => 29
  | 35 => 29
  | 36 => 30
  | 37 => 30
  | 38 => 31
  | 39 => 31
  | 40 => 32
  | 41 => 32
  | 42 => 33
  | 43 => 33
  | 44 => 34
  | 45 => 34
  | 46 => 35
  | 47 => 35
  | 48 => 36
  | 49 => 36
  | 50 => 3
  | 51 => 4
  | 52 => 5
  | 53 => 18
  | 54 => 21
  | 55 => 24
  | 56 => 37
  | 57 => 38
  | 58 => 39
  | 59 => 6
  | 60 => 7
  | 61 => 8
  | 62 => 19
  | 63 => 22
  | 64 => 25
  | 65 => 40
  | 66 => 41
  | 67 => 42
  | _ => 0

/-- Whether a FULL range half-block is the upper `0x8000..0xffff` half. -/
def arithRangeHalfBlockHighFull : ℕ → Bool
  | 1 => true
  | 3 => true
  | 5 => true
  | 7 => true
  | 9 => true
  | 11 => true
  | 13 => true
  | 15 => true
  | 17 => true
  | 19 => true
  | 21 => true
  | 23 => true
  | 25 => true
  | 27 => true
  | 29 => true
  | 31 => true
  | 33 => true
  | 35 => true
  | 37 => true
  | 39 => true
  | 41 => true
  | 43 => true
  | 45 => true
  | 47 => true
  | 49 => true
  | _ => false

/-- Whether a chunk half-block represents a NEG range (`0x8000..0xffff`). -/
def arithRangeHalfBlockNeg : ℕ → Bool
  | 59 => true
  | 60 => true
  | 61 => true
  | 62 => true
  | 63 => true
  | 64 => true
  | 65 => true
  | 66 => true
  | 67 => true
  | _ => false

/-- The chunk value emitted by a half-block and row remainder. -/
def arithRangeChunkValue (block rem : ℕ) : ℕ :=
  rem + if arithRangeHalfBlockHighFull block || arithRangeHalfBlockNeg block then 32768 else 0

/-- Field encoding for the upstream carry range `[-0xEFFFF..0xF0000]`. -/
def arithRangeCarryValue (j : ℕ) (hj : j < 1966080) : FGL :=
  if h : j < 983039 then
    ⟨GL_prime - 983039 + j, by omega⟩
  else
    ⟨j - 983039, by omega⟩

/-- Symbolic row function for the upstream `arith_range_table`.

Rows `0 .. 2228223` are the compressed chunk ranges.  The remaining
`1966080` rows are the carry range with range ID `100`. -/
def arithRangeTableRow (i : Fin arithRangeTableLength) : fields 2 FGL :=
  if h : i.val < arithRangeChunkRows then
    let block := i.val / arithRangeHalfBlockSize
    let rem := i.val % arithRangeHalfBlockSize
    #v[(arithRangeHalfBlockId block : FGL), (arithRangeChunkValue block rem : FGL)]
  else
    #v[(100 : FGL), arithRangeCarryValue (i.val - arithRangeChunkRows) (by
      have hi := i.isLt
      dsimp [arithRangeTableLength, arithRangeChunkRows] at hi h ⊢
      omega)]

/-- Exact static model of upstream `arith_range_table.pil`. -/
def arithRangeTable : StaticTable FGL (fields 2) where
  name := "arith_range_table"
  length := arithRangeTableLength
  row := arithRangeTableRow
  index t := t[0].val * 65536 + t[1].val
  Spec t := ∃ i : Fin arithRangeTableLength, t = arithRangeTableRow i
  contains_iff := by
    intro t
    rfl

/-- POS range IDs in upstream `arith_range_table.pil`. -/
def ArithRangePosId (r : FGL) : Prop :=
  r = (3 : FGL) ∨ r = (4 : FGL) ∨ r = (5 : FGL)
    ∨ r = (18 : FGL) ∨ r = (21 : FGL) ∨ r = (24 : FGL)
    ∨ r = (37 : FGL) ∨ r = (38 : FGL) ∨ r = (39 : FGL)

/-- NEG range IDs in upstream `arith_range_table.pil`. -/
def ArithRangeNegId (r : FGL) : Prop :=
  r = (6 : FGL) ∨ r = (7 : FGL) ∨ r = (8 : FGL)
    ∨ r = (19 : FGL) ∨ r = (22 : FGL) ∨ r = (25 : FGL)
    ∨ r = (40 : FGL) ∨ r = (41 : FGL) ∨ r = (42 : FGL)

private theorem arithRangePosId_not_100 : ¬ ArithRangePosId (100 : FGL) := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h <;>
    have hval := congrArg Fin.val h <;> norm_num at hval

private theorem arithRangeNegId_not_100 : ¬ ArithRangeNegId (100 : FGL) := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h <;>
    have hval := congrArg Fin.val h <;> norm_num at hval

set_option maxHeartbeats 1000000 in
private theorem arithRangeChunkValue_lt_32768_of_pos
    {block rem : ℕ} (hblock : block < 68) (hrem : rem < arithRangeHalfBlockSize)
    (hpos : ArithRangePosId (arithRangeHalfBlockId block : FGL)) :
    arithRangeChunkValue block rem < 32768 := by
  unfold arithRangeHalfBlockSize at hrem
  interval_cases block <;>
    simp [ArithRangePosId, arithRangeHalfBlockId, arithRangeChunkValue,
      arithRangeHalfBlockHighFull, arithRangeHalfBlockNeg] at hpos ⊢ <;>
    omega

set_option maxHeartbeats 1000000 in
private theorem arithRangeChunkValue_neg_bounds_of_neg
    {block rem : ℕ} (hblock : block < 68) (hrem : rem < arithRangeHalfBlockSize)
    (hneg : ArithRangeNegId (arithRangeHalfBlockId block : FGL)) :
    32768 ≤ arithRangeChunkValue block rem ∧ arithRangeChunkValue block rem < 65536 := by
  unfold arithRangeHalfBlockSize at hrem
  interval_cases block <;>
    simp [ArithRangeNegId, arithRangeHalfBlockId, arithRangeChunkValue,
      arithRangeHalfBlockHighFull, arithRangeHalfBlockNeg] at hneg ⊢ <;>
    omega

/-- A POS indexed Arith range-table lookup bounds the value below `0x8000`. -/
theorem arithRangeTable_pos_bound_of_spec {rangeId x : FGL}
    (h_id : ArithRangePosId rangeId)
    (h_spec : arithRangeTable.Spec #v[rangeId, x]) :
    x.val < 32768 := by
  rcases h_spec with ⟨i, hrow⟩
  by_cases hchunk : i.val < arithRangeChunkRows
  · let block := i.val / arithRangeHalfBlockSize
    let rem := i.val % arithRangeHalfBlockSize
    have hblock_lt : block < 68 := by
      have hmul : arithRangeHalfBlockSize * block ≤ i.val := by
        dsimp [block]
        exact Nat.mul_div_le _ _
      dsimp [block, arithRangeChunkRows, arithRangeHalfBlockSize] at hchunk hmul ⊢
      omega
    have hrem_lt : rem < arithRangeHalfBlockSize := by
      dsimp [rem]
      exact Nat.mod_lt _ (by norm_num [arithRangeHalfBlockSize])
    have hid : rangeId = (arithRangeHalfBlockId block : FGL) := by
      have h := congrArg (fun t : fields 2 FGL => t[0]) hrow
      simpa [arithRangeTableRow, hchunk, block, rem] using h
    have hx : x = (arithRangeChunkValue block rem : FGL) := by
      have h := congrArg (fun t : fields 2 FGL => t[1]) hrow
      simpa [arithRangeTableRow, hchunk, block, rem] using h
    have h_id' : ArithRangePosId (arithRangeHalfBlockId block : FGL) := by
      simpa [hid] using h_id
    have hval := arithRangeChunkValue_lt_32768_of_pos hblock_lt hrem_lt h_id'
    rw [hx, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega : arithRangeChunkValue block rem < GL_prime)]
    exact hval
  · have hid : rangeId = (100 : FGL) := by
      have h := congrArg (fun t : fields 2 FGL => t[0]) hrow
      simpa [arithRangeTableRow, hchunk] using h
    exact False.elim (arithRangePosId_not_100 (by simpa [hid] using h_id))

/-- A NEG indexed Arith range-table lookup bounds the value to `0x8000..0xffff`. -/
theorem arithRangeTable_neg_bound_of_spec {rangeId x : FGL}
    (h_id : ArithRangeNegId rangeId)
    (h_spec : arithRangeTable.Spec #v[rangeId, x]) :
    32768 ≤ x.val ∧ x.val < 65536 := by
  rcases h_spec with ⟨i, hrow⟩
  by_cases hchunk : i.val < arithRangeChunkRows
  · let block := i.val / arithRangeHalfBlockSize
    let rem := i.val % arithRangeHalfBlockSize
    have hblock_lt : block < 68 := by
      have hmul : arithRangeHalfBlockSize * block ≤ i.val := by
        dsimp [block]
        exact Nat.mul_div_le _ _
      dsimp [block, arithRangeChunkRows, arithRangeHalfBlockSize] at hchunk hmul ⊢
      omega
    have hrem_lt : rem < arithRangeHalfBlockSize := by
      dsimp [rem]
      exact Nat.mod_lt _ (by norm_num [arithRangeHalfBlockSize])
    have hid : rangeId = (arithRangeHalfBlockId block : FGL) := by
      have h := congrArg (fun t : fields 2 FGL => t[0]) hrow
      simpa [arithRangeTableRow, hchunk, block, rem] using h
    have hx : x = (arithRangeChunkValue block rem : FGL) := by
      have h := congrArg (fun t : fields 2 FGL => t[1]) hrow
      simpa [arithRangeTableRow, hchunk, block, rem] using h
    have h_id' : ArithRangeNegId (arithRangeHalfBlockId block : FGL) := by
      simpa [hid] using h_id
    have hval := arithRangeChunkValue_neg_bounds_of_neg hblock_lt hrem_lt h_id'
    rw [hx, Fin.val_natCast]
    rw [Nat.mod_eq_of_lt (by omega : arithRangeChunkValue block rem < GL_prime)]
    exact hval
  · have hid : rangeId = (100 : FGL) := by
      have h := congrArg (fun t : fields 2 FGL => t[0]) hrow
      simpa [arithRangeTableRow, hchunk] using h
    exact False.elim (arithRangeNegId_not_100 (by simpa [hid] using h_id))

set_option maxRecDepth 10000

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
