import ZiskFv.AirsClean.Main.Row

/-!
# Main Spec + Assumptions

Main is the central AIR — every opcode's `EquivCore/<Op>.lean`
proof takes a `Valid_Main` as a parameter. The per-row Spec captures
the 9 F-typed every-row constraints (`ZiskFv/Airs/Main/Main.lean`):

1. flag boolean
2. is_external_op boolean
3-4. internal_op0_zeroes_c0/c1 (when internal op = 0, c is zero)
5-6. internal_op1_copies_b0/b1 (when internal op = 1, c = b)
7. internal_op0_sets_flag (when internal op = 0, flag = 1)
8. internal_op1_clears_flag (when internal op = 1, flag = 0)
9. flag_set_pc_disjoint (flag · set_pc = 0)

The cross-row `pc_handshake` constraint (PC progression including
set_pc, jmp_offset1, jmp_offset2 multiplexer with Nat.sub saturation
at row 0; see `ZiskFv/Airs/Main/Main.lean:181-192`) is NOT in this
per-row Spec — it lives in a separate adjacency theorem in Bridge.

## Constructibility audit

Each Spec clause maps to a constraint in
`build/extraction/Extraction/Main.lean`'s per-row constraint defs.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks

def Assumptions (row : MainRow FGL) : Prop :=
  row.flag.val < 2 ∧ row.is_external_op.val < 2 ∧ row.op.val < 2
  ∧ row.set_pc.val < 2

/-- Per-row Spec: 9 F-typed constraints. -/
def Spec (row : MainRow FGL) : Prop :=
  row.flag * (1 - row.flag) = 0
  ∧ row.is_external_op * (1 - row.is_external_op) = 0
  ∧ (1 - row.is_external_op) * (1 - row.op) * row.c_0 = 0
  ∧ (1 - row.is_external_op) * (1 - row.op) * row.c_1 = 0
  ∧ (1 - row.is_external_op) * row.op * (row.b_0 - row.c_0) = 0
  ∧ (1 - row.is_external_op) * row.op * (row.b_1 - row.c_1) = 0
  ∧ (1 - row.is_external_op) * (1 - row.op) * (1 - row.flag) = 0
  ∧ (1 - row.is_external_op) * row.op * row.flag = 0
  ∧ row.flag * row.set_pc = 0

end ZiskFv.AirsClean.Main
