import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr Arith_air_simplification
register_simp_attr Arith_constraint_and_interaction_simplification

namespace Arith.extraction

-- airgroup: Zisk (id 0)  air: Arith (id 9)
-- witness column names:
--   stage 1 col 0: carry[0]
--   stage 1 col 1: carry[1]
--   stage 1 col 2: carry[2]
--   stage 1 col 3: carry[3]
--   stage 1 col 4: carry[4]
--   stage 1 col 5: carry[5]
--   stage 1 col 6: carry[6]
--   stage 1 col 7: a[0]
--   stage 1 col 8: a[1]
--   stage 1 col 9: a[2]
--   stage 1 col 10: a[3]
--   stage 1 col 11: b[0]
--   stage 1 col 12: b[1]
--   stage 1 col 13: b[2]
--   stage 1 col 14: b[3]
--   stage 1 col 15: c[0]
--   stage 1 col 16: c[1]
--   stage 1 col 17: c[2]
--   stage 1 col 18: c[3]
--   stage 1 col 19: d[0]
--   stage 1 col 20: d[1]
--   stage 1 col 21: d[2]
--   stage 1 col 22: d[3]
--   stage 1 col 23: na
--   stage 1 col 24: nb
--   stage 1 col 25: nr
--   stage 1 col 26: np
--   stage 1 col 27: sext
--   stage 1 col 28: m32
--   stage 1 col 29: div
--   stage 1 col 30: fab
--   stage 1 col 31: na_fb
--   stage 1 col 32: nb_fa
--   stage 1 col 33: main_div
--   stage 1 col 34: main_mul
--   stage 1 col 35: signed
--   stage 1 col 36: div_by_zero
--   stage 1 col 37: div_overflow
--   stage 1 col 38: inv_sum_all_bs
--   stage 1 col 39: op
--   stage 1 col 40: bus_res1
--   stage 1 col 41: multiplicity
--   stage 1 col 42: range_ab
--   stage 1 col 43: range_cd
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]
--   stage 2 col 3: im[2]
--   stage 2 col 4: im[3]
--   stage 2 col 5: im[4]
--   stage 2 col 6: im[5]
--   stage 2 col 7: im[6]
--   stage 2 col 8: im[7]
--   stage 2 col 9: im[8]
--   stage 2 col 10: im[9]
--   stage 2 col 11: im[10]
--   stage 2 col 12: im_extra
--   stage 2 col 13: im_high_degree[0]
--   stage 2 col 14: im_high_degree[1]

  @[simp]
  def constraint_2_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:53 main_mul*main_div
    (((Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_6_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:59 fab-(((1-(2*na))-(2*nb))+((4*na)*nb))
    (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) - (((1 - (2 * (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)))) - (2 * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)))) + ((4 * (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)))))) = 0

  @[simp]
  def constraint_7_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:60 na_fb-(na*(1-(2*nb)))
    (((Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0)) - ((Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)) * (1 - (2 * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))))))) = 0

  @[simp]
  def constraint_8_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:61 nb_fa-(nb*(1-(2*na)))
    (((Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0)) - ((Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)) * (1 - (2 * (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))))))) = 0

  @[simp]
  def constraint_31_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:206 (eq[0])-(carry[0]*65536)
    (((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0))) - (Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0))) + ((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 15) (row := row) (rotation := 0)))) + ((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)))) - ((2 * (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)))) - ((Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_32_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:208 ((eq[1])+carry[0])-(carry[1]*65536)
    (((((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)))) - (Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0))) + ((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 16) (row := row) (rotation := 0)))) + ((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) - ((2 * (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 0) (row := row) (rotation := 0))) - ((Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_33_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:208 ((eq[2])+carry[1])-(carry[2]*65536)
    ((((((((((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) - (Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0))) + ((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)))) + ((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)))) - ((2 * (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)))) - (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + ((Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 1) (row := row) (rotation := 0))) - ((Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_34_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:208 ((eq[3])+carry[2])-(carry[3]*65536)
    (((((((((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) - (Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0))) + ((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)))) + ((Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)))) - ((2 * (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)))) + (Circuit.main c (id := 1) (column := 2) (row := row) (rotation := 0))) - ((Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_35_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:208 ((eq[4])+carry[3])-(carry[4]*65536)
    ((((((((((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 11) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) + (((Circuit.main c (id := 1) (column := 7) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) - (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) - (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) * (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)))) + ((Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) - ((Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 19) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (Circuit.main c (id := 1) (column := 3) (row := row) (rotation := 0))) - ((Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_36_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:208 ((eq[5])+carry[4])-(carry[5]*65536)
    (((((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0))) + (((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 8) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) + (((Circuit.main c (id := 1) (column := 12) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) - ((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + ((((Circuit.main c (id := 1) (column := 20) (row := row) (rotation := 0)) * 2) * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (Circuit.main c (id := 1) (column := 4) (row := row) (rotation := 0))) - ((Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_37_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:208 ((eq[6])+carry[5])-(carry[6]*65536)
    ((((((((((Circuit.main c (id := 1) (column := 30) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0))) + (((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) + (((Circuit.main c (id := 1) (column := 13) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) - ((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (Circuit.main c (id := 1) (column := 5) (row := row) (rotation := 0))) - ((Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)) * 65536))) = 0

  @[simp]
  def constraint_38_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:210 (eq[7])+carry[6]
    ((((((((((65536 * (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)))) + (((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 32) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) + (((Circuit.main c (id := 1) (column := 14) (row := row) (rotation := 0)) * (Circuit.main c (id := 1) (column := 31) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) - (((65536 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0)))) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) - ((Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (((2 * (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))) * (Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0))) * (1 - (Circuit.main c (id := 1) (column := 29) (row := row) (rotation := 0))))) + (Circuit.main c (id := 1) (column := 6) (row := row) (rotation := 0)))) = 0

  @[simp]
  def constraint_40_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:214 m32*(1-m32)
    (((Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_41_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:215 na*(1-na)
    (((Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 23) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_42_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:216 nb*(1-nb)
    (((Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 24) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_43_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:217 nr*(1-nr)
    (((Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 25) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_44_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:218 np*(1-np)
    (((Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 26) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_45_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:219 sext*(1-sext)
    (((Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0)) * (1 - (Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0))))) = 0

  @[simp]
  def constraint_46_every_row {C : Type → Type → Type} {F ExtF : Type} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=
    -- arith/pil/arith.pil:263 bus_res1-((sext*4294967295)+((1-m32)*(bus_res1_64)))
    (((Circuit.main c (id := 1) (column := 40) (row := row) (rotation := 0)) - (((Circuit.main c (id := 1) (column := 27) (row := row) (rotation := 0)) * 4294967295) + ((1 - (Circuit.main c (id := 1) (column := 28) (row := row) (rotation := 0))) * (((((1 - (Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0))) - (Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0))) * ((Circuit.main c (id := 1) (column := 21) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 22) (row := row) (rotation := 0)) * 65536))) + ((Circuit.main c (id := 1) (column := 34) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 17) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 18) (row := row) (rotation := 0)) * 65536)))) + ((Circuit.main c (id := 1) (column := 33) (row := row) (rotation := 0)) * ((Circuit.main c (id := 1) (column := 9) (row := row) (rotation := 0)) + ((Circuit.main c (id := 1) (column := 10) (row := row) (rotation := 0)) * 65536)))))))) = 0

end Arith.extraction
