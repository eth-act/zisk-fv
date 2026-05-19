import ZiskFv.AirsClean.MemAlignReadByte.Row

/-!
# MemAlignReadByte Spec + Assumptions

The Clean-side spec for the MemAlignReadByte AIR. The Spec is the
`composed_value` byte-recombination relation pinned by PIL constraint
3 (`mem_align_byte.pil:59`).

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

/-- The byte-position factor for `byte_value`, parameterized by the
    selector bits. PIL `mem_align_byte.pil:59`. -/
@[reducible]
def byte_value_factor (sel_high_2b sel_high_b : FGL) : FGL :=
  16777216 * sel_high_2b * sel_high_b
  + 65536 * sel_high_2b * (1 - sel_high_b)
  + 256 * (1 - sel_high_2b) * sel_high_b
  + (1 - sel_high_2b) * (1 - sel_high_b)

/-- The byte-position factor for `value_8b`. -/
@[reducible]
def value_8b_factor (sel_high_2b sel_high_b : FGL) : FGL :=
  16777216 * sel_high_2b * (1 - sel_high_b)
  + 65536 * sel_high_2b * sel_high_b
  + 256 * (1 - sel_high_2b) * (1 - sel_high_b)
  + (1 - sel_high_2b) * sel_high_b

/-- The byte-position factor for `value_16b`. -/
@[reducible]
def value_16b_factor (sel_high_2b : FGL) : FGL :=
  65536 * (1 - sel_high_2b) + sel_high_2b

/-- Assumptions on a MemAlignReadByte row: range bounds on the byte
    cells (delivered by the range bus). -/
def Assumptions (row : MemAlignReadByteRow FGL) : Prop :=
  row.sel_high_4b.val < 2 ∧ row.sel_high_2b.val < 2 ∧ row.sel_high_b.val < 2

/-- The MemAlignReadByte Spec: `composed_value` equals the weighted
    sum of `byte_value`, `value_8b`, `value_16b` per the per-byte
    selectors. -/
def Spec (row : MemAlignReadByteRow FGL) : Prop :=
  row.composed_value
    = row.byte_value * byte_value_factor row.sel_high_2b row.sel_high_b
    + row.value_8b * value_8b_factor row.sel_high_2b row.sel_high_b
    + row.value_16b * value_16b_factor row.sel_high_2b

end ZiskFv.AirsClean.MemAlignReadByte
