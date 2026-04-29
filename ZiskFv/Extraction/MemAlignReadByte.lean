import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr MemAlignReadByte_air_simplification
register_simp_attr MemAlignReadByte_constraint_and_interaction_simplification

namespace MemAlignReadByte.extraction

-- airgroup: Zisk (id 0)  air: MemAlignReadByte (id 7)
-- witness column names:
--   stage 1 col 0: sel_high_4b
--   stage 1 col 1: sel_high_2b
--   stage 1 col 2: sel_high_b
--   stage 1 col 3: direct_value
--   stage 1 col 4: composed_value
--   stage 1 col 5: value_16b
--   stage 1 col 6: value_8b
--   stage 1 col 7: byte_value
--   stage 1 col 8: addr_w
--   stage 1 col 9: step
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im_high_degree[0]

  @[simp]
  def constraint_0_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:37 sel_high_4b*(1-sel_high_4b)
    (((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_1_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:38 sel_high_2b*(1-sel_high_2b)
    (((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_2_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:39 sel_high_b*(1-sel_high_b)
    (((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_3_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:61 composed_value-(((byte_value*(byte_value_factor))+(value_8b*(value_8b_factor)))+(value_16b*(value_16b_factor)))
    (((Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)) - ((((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * (((((16777216 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) + ((65536 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) + ((256 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))))) + ((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) * (((((16777216 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((65536 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((256 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) + ((1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))))) + ((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * ((65536 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))))))) = 0

  -- constraint_4_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_5_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_6_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_7_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_8_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_9_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end MemAlignReadByte.extraction
