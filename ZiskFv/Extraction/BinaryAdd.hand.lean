import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr BinaryAdd_air_simplification
register_simp_attr BinaryAdd_constraint_and_interaction_simplification

namespace BinaryAdd.extraction

-- airgroup: Zisk (id 0)  air: BinaryAdd (id 11)
-- witness column names:
--   stage 1 col 0: a[0]
--   stage 1 col 1: a[1]
--   stage 1 col 2: b[0]
--   stage 1 col 3: b[1]
--   stage 1 col 4: c_chunks[0]
--   stage 1 col 5: c_chunks[1]
--   stage 1 col 6: c_chunks[2]
--   stage 1 col 7: c_chunks[3]
--   stage 1 col 8: cout[0]
--   stage 1 col 9: cout[1]
--   stage 2 col 0: gsum
--   stage 2 col 1: im_cluster
--   stage 2 col 2: im_cluster

  @[simp]
  def constraint_0_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:15 cout[0]*(1-cout[0])
    (((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_1_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:20 (a[0]+b[0])-(((cout[0]*4294967296)+(c_chunks[1]*65536))+c_chunks[0])
    ((((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) - ((((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 4294967296) + ((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * 65536)) + (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_2_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:15 cout[1]*(1-cout[1])
    (((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_3_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:20 ((a[1]+b[1])+cout[0])-(((cout[1]*4294967296)+(c_chunks[3]*65536))+c_chunks[2])
    (((((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) - ((((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 4294967296) + ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * 65536)) + (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0))))) = 0

  -- constraint_4_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_5_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_6_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_7_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_8_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end BinaryAdd.extraction
