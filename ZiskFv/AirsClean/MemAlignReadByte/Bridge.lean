import ZiskFv.AirsClean.MemAlignReadByte.Soundness
import ZiskFv.Airs.MemAlignReadByte

/-!
# `Valid_MemAlignReadByte` ↔ `MemAlignReadByteRow` compatibility

Connects the existing `Valid_MemAlignReadByte` interface to the
Clean Component's row type.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- Project a `Valid_MemAlignReadByte` at row `r` into a Clean
    `MemAlignReadByteRow FGL`. -/
@[reducible]
def rowAt (v : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL) (r : ℕ)
    : MemAlignReadByteRow FGL where
  sel_high_4b := v.sel_high_4b r
  sel_high_2b := v.sel_high_2b r
  sel_high_b := v.sel_high_b r
  direct_value := v.direct_value r
  composed_value := v.composed_value r
  value_16b := v.value_16b r
  value_8b := v.value_8b r
  byte_value := v.byte_value r
  addr_w := v.addr_w r
  step := v.step r

end ZiskFv.AirsClean.MemAlignReadByte
