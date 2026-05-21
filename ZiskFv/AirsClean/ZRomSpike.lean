import Clean.Circuit.Lookup
import ZiskFv.Field.Goldilocks

/-!
# C0e — Z-ROM spike: a large `StaticTable` is tractable

Validates the C0e finding: a Clean `StaticTable` over a large ROM has no
kernel-scaling wall. The `decide`-blowup only afflicts the *naive*
construction — a literal row enumeration plus a `decide`-proved
`contains_iff`. Here `row` is an arithmetic *decode* and `contains_iff` is
proved *structurally*; the proof is generic in `len`, so it holds for a
table of ANY size (the 2.2M-row BinaryTable and beyond). `length` is just a
number. The range-check table (rows `0 … len-1`) is itself a genuine ZisK
ROM shape.
-/

namespace ZiskFv.AirsClean.ZRomSpike

open Goldilocks

/-- A range-check `StaticTable`: `len` rows `0, 1, …, len-1` as field
    elements. `row` decodes an index to its field value; `contains_iff` is
    proved structurally — no `decide`, no enumeration — and the proof does
    not depend on `len`, so the construction scales to any table size. -/
def rangeStaticTable (len : ℕ) (h_len : len ≤ GL_prime) :
    StaticTable FGL field where
  name := "z-rom-spike-range"
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

/-- The spike instantiated at a deliberately large size — `2^32` rows —
    elaborates instantly: a witness that table size carries no cost. -/
def bigRangeTable : StaticTable FGL field :=
  rangeStaticTable (2 ^ 32) (by decide)

end ZiskFv.AirsClean.ZRomSpike
