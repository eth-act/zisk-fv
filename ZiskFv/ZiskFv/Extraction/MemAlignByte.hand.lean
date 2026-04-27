import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr MemAlignByte_air_simplification
register_simp_attr MemAlignByte_constraint_and_interaction_simplification

namespace MemAlignByte.extraction

-- airgroup: Zisk (id 0)  air: MemAlignByte (id 6)
-- witness column names:
--   stage 1 col 0: sel_high_4b
--   stage 1 col 1: sel_high_2b
--   stage 1 col 2: sel_high_b
--   stage 1 col 3: direct_value
--   stage 1 col 4: composed_value
--   stage 1 col 5: written_composed_value
--   stage 1 col 6: written_byte_value
--   stage 1 col 7: value_16b
--   stage 1 col 8: value_8b
--   stage 1 col 9: byte_value
--   stage 1 col 10: addr_w
--   stage 1 col 11: step
--   stage 1 col 12: is_write
--   stage 1 col 13: mem_write_values[0]
--   stage 1 col 14: mem_write_values[1]
--   stage 1 col 15: bus_byte
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]
--   stage 2 col 3: im_high_degree[0]

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
    (((Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)) - ((((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * (((((16777216 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) + ((65536 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) + ((256 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))))) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (((((16777216 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((65536 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((256 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) + ((1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))))) + ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * ((65536 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))))))) = 0

  @[simp]
  def constraint_4_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:73 is_write*(1-is_write)
    (((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_5_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:85 written_composed_value-(((written_byte_value*(byte_value_factor))+(value_8b*(value_8b_factor)))+(value_16b*(value_16b_factor)))
    (((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) - ((((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) * (((((16777216 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) + ((65536 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) + ((256 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))))) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (((((16777216 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((65536 * (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))) + ((256 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) + ((1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)))))) + ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * ((65536 * (1 - (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))))))) = 0

  @[simp]
  def constraint_6_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:89 mem_write_values[0]-((sel_high_4b*(direct_value-written_composed_value))+written_composed_value)
    (((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_7_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:90 mem_write_values[1]-((sel_high_4b*(written_composed_value-direct_value))+direct_value)
    (((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_8_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align_byte.pil:97 bus_byte-((is_write*(written_byte_value-byte_value))+byte_value)
    (((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))))) = 0

  -- constraint_9_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_10_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_11_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_12_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_13_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_14_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_15_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end MemAlignByte.extraction
