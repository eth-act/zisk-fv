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

def rangeTable32 : StaticTable FGL field :=
  rangeStaticTable (2 ^ 32) (by decide) "range-32"

end ZiskFv.AirsClean.RangeTables
