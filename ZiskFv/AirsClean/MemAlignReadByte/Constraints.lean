import ZiskFv.AirsClean.MemAlignReadByte.Spec
import Clean.Circuit.Basic

/-!
# MemAlignReadByte circuit operations

The 4 F-typed constraints of ZisK's MemAlignReadByte AIR
(`build/extraction/Extraction/MemAlignReadByte.lean`):

1. `sel_high_4b * (1 - sel_high_4b) = 0`  (sel_high_4b boolean)
2. `sel_high_2b * (1 - sel_high_2b) = 0`  (sel_high_2b boolean)
3. `sel_high_b * (1 - sel_high_b) = 0`    (sel_high_b boolean)
4. `composed_value - (byte_value · b_factor + value_8b · v8_factor
                     + value_16b · v16_factor) = 0`
   (composed_value definitional identity)

The byte_value_factor / value_8b_factor / value_16b_factor are
inlined here because their FGL-typed definitions in
`Spec.lean` don't apply to `Expression FGL`-typed circuit terms.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.MemAlignReadByte

open Goldilocks
open Circuit (assertZero)

/-- The 4 MemAlignReadByte F-typed constraints emitted per row. -/
@[circuit_norm]
def main (row : Var MemAlignReadByteRow FGL) : Circuit FGL Unit := do
  assertZero (row.sel_high_4b * (1 - row.sel_high_4b))
  assertZero (row.sel_high_2b * (1 - row.sel_high_2b))
  assertZero (row.sel_high_b * (1 - row.sel_high_b))
  -- composed_value definitional identity
  -- byte_value_factor: 16777216·s2·sb + 65536·s2·(1-sb) + 256·(1-s2)·sb + (1-s2)·(1-sb)
  -- value_8b_factor:   16777216·s2·(1-sb) + 65536·s2·sb + 256·(1-s2)·(1-sb) + (1-s2)·sb
  -- value_16b_factor:  65536·(1-s2) + s2
  assertZero (row.composed_value
    - (row.byte_value *
        (16777216 * row.sel_high_2b * row.sel_high_b
         + 65536 * row.sel_high_2b * (1 - row.sel_high_b)
         + 256 * (1 - row.sel_high_2b) * row.sel_high_b
         + (1 - row.sel_high_2b) * (1 - row.sel_high_b))
       + row.value_8b *
        (16777216 * row.sel_high_2b * (1 - row.sel_high_b)
         + 65536 * row.sel_high_2b * row.sel_high_b
         + 256 * (1 - row.sel_high_2b) * (1 - row.sel_high_b)
         + (1 - row.sel_high_2b) * row.sel_high_b)
       + row.value_16b *
        (65536 * (1 - row.sel_high_2b) + row.sel_high_2b)))

end ZiskFv.AirsClean.MemAlignReadByte
