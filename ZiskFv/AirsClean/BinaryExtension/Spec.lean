import ZiskFv.AirsClean.BinaryExtension.Row

/-!
# BinaryExtension Spec + Assumptions (boolean-flag invariants only)

The full BinaryExtension circuit content (32-bit sign-extension of
b / h / w slices through a 2-byte chunk decomposition) lives in
`ZiskFv/Airs/Binary/BinaryExtension.lean`. Spec below captures the
boolean invariants on `op_is_shift`, `b_0`, `b_1`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

def Assumptions (row : BinaryExtensionRow FGL) : Prop :=
  row.flags.op_is_shift.val < 2
  ∧ row.flags.b_0.val < 2 ∧ row.flags.b_1.val < 2

def Spec (row : BinaryExtensionRow FGL) : Prop :=
  row.flags.op_is_shift * (1 - row.flags.op_is_shift) = 0
  ∧ row.flags.b_0 * (1 - row.flags.b_0) = 0
  ∧ row.flags.b_1 * (1 - row.flags.b_1) = 0

end ZiskFv.AirsClean.BinaryExtension
