import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr Mem_air_simplification
register_simp_attr Mem_constraint_and_interaction_simplification

namespace Mem.extraction

-- airgroup: Zisk (id 0)  air: Mem (id 2)
-- witness column names:
--   stage 1 col 0: addr
--   stage 1 col 1: step
--   stage 1 col 2: sel
--   stage 1 col 3: addr_changes
--   stage 1 col 4: step_dual
--   stage 1 col 5: sel_dual
--   stage 1 col 6: value[0]
--   stage 1 col 7: value[1]
--   stage 1 col 8: wr
--   stage 1 col 9: previous_step
--   stage 1 col 10: increment[0]
--   stage 1 col 11: increment[1]
--   stage 1 col 12: read_same_addr
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]

  -- constraint_0_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_1_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_2_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  @[simp]
  def constraint_3_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:126 sel_dual*(1-sel_dual)
    (((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_4_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:127 (1-sel)*sel_dual
    (((1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_5_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:132 sel*(1-sel)
    (((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_6_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:133 addr_changes*(1-addr_changes)
    (((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_7_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:176 wr*(1-wr)
    (((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_8_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:179 wr*(1-sel)
    (((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))))) = 0

  -- constraint_9_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_10_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_11_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_12_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_13_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_14_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_15_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_16_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_17_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  @[simp]
  def constraint_18_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:389 read_same_addr-((1-addr_changes)*(1-wr))
    (((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) - ((1 - (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)))))) = 0

  -- constraint_19_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_20_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  @[simp]
  def constraint_21_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:425 (addr_changes*(1-wr))*value[0]
    ((((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) = 0

  -- constraint_22_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  @[simp]
  def constraint_23_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem.pil:425 (addr_changes*(1-wr))*value[1]
    ((((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_24_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_25_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_26_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_27_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_28_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_29_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_30_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_31_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_32_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_33_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end Mem.extraction
