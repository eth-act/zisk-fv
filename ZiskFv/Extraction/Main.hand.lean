import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr Main_air_simplification
register_simp_attr Main_constraint_and_interaction_simplification

namespace Main.extraction

-- airgroup: Zisk (id 0)  air: Main (id 0)
-- witness column names:
--   stage 1 col 0: a[0]
--   stage 1 col 1: a[1]
--   stage 1 col 2: b[0]
--   stage 1 col 3: b[1]
--   stage 1 col 4: c[0]
--   stage 1 col 5: c[1]
--   stage 1 col 6: flag
--   stage 1 col 7: pc
--   stage 1 col 8: a_src_imm
--   stage 1 col 9: a_src_mem
--   stage 1 col 10: a_offset_imm0
--   stage 1 col 11: a_imm1
--   stage 1 col 12: a_src_step
--   stage 1 col 13: b_src_imm
--   stage 1 col 14: b_src_mem
--   stage 1 col 15: b_offset_imm0
--   stage 1 col 16: b_imm1
--   stage 1 col 17: b_src_ind
--   stage 1 col 18: ind_width
--   stage 1 col 19: is_external_op
--   stage 1 col 20: op
--   stage 1 col 21: store_ra
--   stage 1 col 22: store_mem
--   stage 1 col 23: store_ind
--   stage 1 col 24: store_offset
--   stage 1 col 25: set_pc
--   stage 1 col 26: jmp_offset1
--   stage 1 col 27: jmp_offset2
--   stage 1 col 28: m32
--   stage 1 col 29: addr1
--   stage 1 col 30: a_reg_prev_mem_step
--   stage 1 col 31: b_reg_prev_mem_step
--   stage 1 col 32: store_reg_prev_mem_step
--   stage 1 col 33: store_reg_prev_value[0]
--   stage 1 col 34: store_reg_prev_value[1]
--   stage 1 col 35: a_src_reg
--   stage 1 col 36: b_src_reg
--   stage 1 col 37: store_reg
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]
--   stage 2 col 3: im[2]
--   stage 2 col 4: im_extra
--   stage 2 col 5: im_high_degree[0]
--   stage 2 col 6: im_high_degree[1]
--   stage 2 col 7: im_high_degree[2]

  @[simp]
  def constraint_8_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:384 ((1-is_external_op)*(1-op))*c[0]
    ((((1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_9_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:387 ((1-is_external_op)*op)*(b[0]-c[0])
    ((((1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_15_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:384 ((1-is_external_op)*(1-op))*c[1]
    ((((1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_16_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:387 ((1-is_external_op)*op)*(b[1]-c[1])
    ((((1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_17_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:392 ((1-is_external_op)*(1-op))*(1-flag)
    ((((1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) * (1 - (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_18_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:395 ((1-is_external_op)*op)*flag
    ((((1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_19_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:398 flag*set_pc
    (((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_20_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:401 (1-Main.SEGMENT_L1)*(pc-(expected_current_pc))
    (((1 - (Circuit.preprocessed c (column := 0) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) - ((((Circuit.main c (id := 1) (column := 25) (row := row - 1) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 4) (row := row - 1) (rotation := 0)) + (Circuit.main c (id := 1) (column := 26) (row := row - 1) (rotation := 0)))) + ((1 - (Circuit.main c (id := 1) (column := 25) (row := row - 1) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 7) (row := row - 1) (rotation := 0)) + (Circuit.main c (id := 1) (column := 27) (row := row - 1) (rotation := 0))))) + ((Circuit.main c (id := 1) (column := 6) (row := row - 1) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 26) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 27) (row := row - 1) (rotation := 0)))))))) = 0

  @[simp]
  def constraint_24_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:450 flag*(1-flag)
    (((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_30_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- main/pil/main.pil:463 is_external_op*(1-is_external_op)
    (((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))))) = 0

end Main.extraction
