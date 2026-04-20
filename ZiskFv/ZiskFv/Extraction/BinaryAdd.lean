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
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]

  @[simp]
  def constraint_0 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:15 cout[0]*(1-cout[0])
    (((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_1 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:20 (a[0]+b[0])-(((cout[0]*4294967296)+(c_chunks[1]*65536))+c_chunks[0])
    ((((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) - ((((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 4294967296) + ((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * 65536)) + (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_2 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:15 cout[1]*(1-cout[1])
    (((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_3 {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- binary/pil/binary_add.pil:20 ((a[1]+b[1])+cout[0])-(((cout[1]*4294967296)+(c_chunks[3]*65536))+c_chunks[2])
    (((((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))) + (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) - ((((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 4294967296) + ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * 65536)) + (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0))))) = 0

  -- constraint_4 skipped: operand kind Challenge(Challenge { stage: 2, idx: 0 }) not yet supported by zisk-pil-extract

  -- constraint_5 skipped: operand kind Challenge(Challenge { stage: 2, idx: 0 }) not yet supported by zisk-pil-extract

  -- constraint_6 skipped: operand kind FixedCol(FixedCol { idx: 0, row_offset: 0 }) not yet supported by zisk-pil-extract

  -- constraint_7 skipped: operand kind AirValue(AirValue { idx: 1 }) not yet supported by zisk-pil-extract

  -- constraint_8 skipped: operand kind FixedCol(FixedCol { idx: 0, row_offset: 1 }) not yet supported by zisk-pil-extract

end BinaryAdd.extraction
