import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr Binary_air_simplification
register_simp_attr Binary_constraint_and_interaction_simplification

namespace Binary.extraction

-- airgroup: Zisk (id 0)  air: Binary (id 10)
-- witness column names:
--   stage 1 col 0: b_op
--   stage 1 col 1: free_in_a[0]
--   stage 1 col 2: free_in_a[1]
--   stage 1 col 3: free_in_a[2]
--   stage 1 col 4: free_in_a[3]
--   stage 1 col 5: free_in_a[4]
--   stage 1 col 6: free_in_a[5]
--   stage 1 col 7: free_in_a[6]
--   stage 1 col 8: free_in_a[7]
--   stage 1 col 9: free_in_b[0]
--   stage 1 col 10: free_in_b[1]
--   stage 1 col 11: free_in_b[2]
--   stage 1 col 12: free_in_b[3]
--   stage 1 col 13: free_in_b[4]
--   stage 1 col 14: free_in_b[5]
--   stage 1 col 15: free_in_b[6]
--   stage 1 col 16: free_in_b[7]
--   stage 1 col 17: free_in_c[0]
--   stage 1 col 18: free_in_c[1]
--   stage 1 col 19: free_in_c[2]
--   stage 1 col 20: free_in_c[3]
--   stage 1 col 21: free_in_c[4]
--   stage 1 col 22: free_in_c[5]
--   stage 1 col 23: free_in_c[6]
--   stage 1 col 24: free_in_c[7]
--   stage 1 col 25: carry[0]
--   stage 1 col 26: carry[1]
--   stage 1 col 27: carry[2]
--   stage 1 col 28: carry[3]
--   stage 1 col 29: carry[4]
--   stage 1 col 30: carry[5]
--   stage 1 col 31: carry[6]
--   stage 1 col 32: carry[7]
--   stage 1 col 33: mode32
--   stage 1 col 34: result_is_a
--   stage 1 col 35: use_first_byte
--   stage 1 col 36: c_is_signed
--   stage 1 col 37: b_op_or_sext
--   stage 1 col 38: mode32_and_c_is_signed
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]
--   stage 2 col 3: im[2]
--   stage 2 col 4: im[3]

  @[simp]
  def constraint_0_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:83 mode32*(1-mode32)
    (((Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_1_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:84 carry[7]*(1-carry[7])
    (((Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_2_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:85 result_is_a*(1-result_is_a)
    (((Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_3_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:86 use_first_byte*(1-use_first_byte)
    (((Circuit.main c (id := 1) (column := 35) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 35) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_4_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:87 c_is_signed*(1-c_is_signed)
    (((Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_5_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:112 b_op_or_sext-((mode32*((c_is_signed+512)-b_op))+b_op)
    (((Circuit.main c (id := 1) (column := 37) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)) * (((Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0)) + 512) - (Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_6_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary.pil:113 mode32_and_c_is_signed-(mode32*c_is_signed)
    (((Circuit.main c (id := 1) (column := 38) (row := row) (rotation := 0)) - ((Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 36) (row := row) (rotation := 0))))) = 0

  -- constraint_7_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_8_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_9_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_10_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_11_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_12_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_13_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end Binary.extraction
