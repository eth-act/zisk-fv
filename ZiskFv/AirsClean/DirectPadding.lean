import Mathlib

/-!
# Local source equations for byte-memory padding

`mem/pil/mem_align_byte.pil:106–118` balances physical padding rows by a
positive aligned zero-load Direct update and a negative byte zero-load
Direct update, both with the same segment `padding_size`. This module
fixes the independent numerical equations, not an interpreter of generated
syntax. Source-specific welds must supply the actual accumulator and count
cells. It does not finish a channel or relate an arbitrary count to a trace.
-/

namespace ZiskFv.AirsClean

variable {F : Type} [Field F]

/-- Positive bus-10 tuple `[LOAD,0,0,8,0,0]` with segment multiplicity. -/
def alignedLoadPaddingEquation (paddingSize imDirect alpha gamma : F) : Prop :=
  imDirect * (((((8 * alpha) * alpha) * alpha + 1) * alpha + 10) + gamma) -
    paddingSize = 0

/-- Negative bus-10 tuple `[LOAD,0,0,1,0,0]` with the same multiplicity. -/
def byteLoadPaddingEquation (paddingSize imDirect alpha gamma : F) : Prop :=
  imDirect * ((((alpha * alpha) * alpha + 1) * alpha + 10) + gamma) -
    (0 - paddingSize) = 0

end ZiskFv.AirsClean
