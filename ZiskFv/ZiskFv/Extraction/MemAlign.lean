import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr MemAlign_air_simplification
register_simp_attr MemAlign_constraint_and_interaction_simplification

namespace MemAlign.extraction

-- airgroup: Zisk (id 0)  air: MemAlign (id 5)
-- witness column names:
--   stage 1 col 0: addr
--   stage 1 col 1: offset
--   stage 1 col 2: width
--   stage 1 col 3: wr
--   stage 1 col 4: pc
--   stage 1 col 5: reset
--   stage 1 col 6: sel_up_to_down
--   stage 1 col 7: sel_down_to_up
--   stage 1 col 8: reg[0]
--   stage 1 col 9: reg[1]
--   stage 1 col 10: reg[2]
--   stage 1 col 11: reg[3]
--   stage 1 col 12: reg[4]
--   stage 1 col 13: reg[5]
--   stage 1 col 14: reg[6]
--   stage 1 col 15: reg[7]
--   stage 1 col 16: sel[0]
--   stage 1 col 17: sel[1]
--   stage 1 col 18: sel[2]
--   stage 1 col 19: sel[3]
--   stage 1 col 20: sel[4]
--   stage 1 col 21: sel[5]
--   stage 1 col 22: sel[6]
--   stage 1 col 23: sel[7]
--   stage 1 col 24: step
--   stage 1 col 25: delta_addr
--   stage 1 col 26: sel_prove
--   stage 1 col 27: value[0]
--   stage 1 col 28: value[1]
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]
--   stage 2 col 3: im[2]
--   stage 2 col 4: im[3]
--   stage 2 col 5: im_extra

  -- constraint_0_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_1_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[0]-reg[0])*sel[0])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 8) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_2_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_3_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[1]-reg[1])*sel[1])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 9) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_4_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_5_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[2]-reg[2])*sel[2])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 10) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_6_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_7_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[3]-reg[3])*sel[3])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 11) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_8_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_9_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[4]-reg[4])*sel[4])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 12) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_10_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_11_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[5]-reg[5])*sel[5])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 13) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_12_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_13_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[6]-reg[6])*sel[6])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 14) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  -- constraint_14_every_row skipped: WitnessCol with positive rowOffset 1 not yet supported (PIL typically only uses `'` postfix for row -1)

  @[simp]
  def constraint_15_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:118 (('reg[7]-reg[7])*sel[7])*sel_down_to_up
    (((((Circuit.main c (id := 1) (column := 15) (row := row - 1) (rotation := 0)) - (Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_16_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:122 MemAlign.L1*pc
    (((Circuit.preprocessed c (column := 0) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_17_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[0]*(1-sel[0])
    (((Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_18_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[1]*(1-sel[1])
    (((Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_19_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[2]*(1-sel[2])
    (((Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_20_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[3]*(1-sel[3])
    (((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_21_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[4]*(1-sel[4])
    (((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_22_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[5]*(1-sel[5])
    (((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_23_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[6]*(1-sel[6])
    (((Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_24_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:126 sel[7]*(1-sel[7])
    (((Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_25_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:128 wr*(1-wr)
    (((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_26_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:129 reset*(1-reset)
    (((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_27_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:130 sel_up_to_down*(1-sel_up_to_down)
    (((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_28_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:131 sel_down_to_up*(1-sel_down_to_up)
    (((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_29_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:143 delta_addr-((addr-'addr)*(1-reset))
    (((Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) - (Circuit.main c (id := 1) (column := 0) (row := row - 1) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)))))) = 0

  @[simp]
  def constraint_30_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:166 sel_prove*(sel_assume)
    (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_31_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:188 value[0]-((sel_prove*((((((((sel[0]*(((reg[0]+(reg[1]*256))+(reg[2]*65536))+(reg[3]*16777216)))+(sel[1]*(((reg[1]+(reg[2]*256))+(reg[3]*65536))+(reg[4]*16777216))))+(sel[2]*(((reg[2]+(reg[3]*256))+(reg[4]*65536))+(reg[5]*16777216))))+(sel[3]*(((reg[3]+(reg[4]*256))+(reg[5]*65536))+(reg[6]*16777216))))+(sel[4]*(((reg[4]+(reg[5]*256))+(reg[6]*65536))+(reg[7]*16777216))))+(sel[5]*(((reg[5]+(reg[6]*256))+(reg[7]*65536))+(reg[0]*16777216))))+(sel[6]*(((reg[6]+(reg[7]*256))+(reg[0]*65536))+(reg[1]*16777216))))+(sel[7]*(((reg[7]+(reg[0]*256))+(reg[1]*65536))+(reg[2]*16777216)))))+((sel_assume)*(((reg[0]+(reg[1]*256))+(reg[2]*65536))+(reg[3]*16777216))))
    (((Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (((((((((Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 16777216))) + ((Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 16777216))))) + (((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))) * ((((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 16777216)))))) = 0

  @[simp]
  def constraint_32_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- mem/pil/mem_align.pil:188 value[1]-((sel_prove*((((((((sel[0]*(((reg[4]+(reg[5]*256))+(reg[6]*65536))+(reg[7]*16777216)))+(sel[1]*(((reg[5]+(reg[6]*256))+(reg[7]*65536))+(reg[0]*16777216))))+(sel[2]*(((reg[6]+(reg[7]*256))+(reg[0]*65536))+(reg[1]*16777216))))+(sel[3]*(((reg[7]+(reg[0]*256))+(reg[1]*65536))+(reg[2]*16777216))))+(sel[4]*(((reg[0]+(reg[1]*256))+(reg[2]*65536))+(reg[3]*16777216))))+(sel[5]*(((reg[1]+(reg[2]*256))+(reg[3]*65536))+(reg[4]*16777216))))+(sel[6]*(((reg[2]+(reg[3]*256))+(reg[4]*65536))+(reg[5]*16777216))))+(sel[7]*(((reg[3]+(reg[4]*256))+(reg[5]*65536))+(reg[6]*16777216)))))+((sel_assume)*(((reg[4]+(reg[5]*256))+(reg[6]*65536))+(reg[7]*16777216))))
    (((Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (((((((((Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 16777216))) + ((Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 16777216)))) + ((Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)) * ((((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 16777216))))) + (((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) + (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))) * ((((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * 256)) + ((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * 65536)) + ((Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)) * 16777216)))))) = 0

  -- constraint_33_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_34_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_35_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_36_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_37_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_38_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_39_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end MemAlign.extraction
