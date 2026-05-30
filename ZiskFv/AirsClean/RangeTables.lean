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

def rangeTable24 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 24) (by decide) "range-24"

def rangeTable32 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 32) (by decide) "range-32"

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
