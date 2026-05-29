import ZiskFv.AirsClean.Main.Spec

/-!
# Main Soundness

The 9 F-typed per-row constraints map 1:1 to Spec clauses; structural.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks

theorem soundness (row : MainRow FGL)
    (_h_assumptions : Assumptions row)
    (h_flag_bool : row.flag * (1 - row.flag) = 0)
    (h_is_ext_bool : row.is_external_op * (1 - row.is_external_op) = 0)
    (h_io0_zc0 : (1 - row.is_external_op) * (1 - row.op) * row.c_0 = 0)
    (h_io0_zc1 : (1 - row.is_external_op) * (1 - row.op) * row.c_1 = 0)
    (h_io1_cb0 : (1 - row.is_external_op) * row.op * (row.b_0 - row.c_0) = 0)
    (h_io1_cb1 : (1 - row.is_external_op) * row.op * (row.b_1 - row.c_1) = 0)
    (h_io0_sf : (1 - row.is_external_op) * (1 - row.op) * (1 - row.flag) = 0)
    (h_io1_cf : (1 - row.is_external_op) * row.op * row.flag = 0)
    (h_flag_setpc : row.flag * row.set_pc = 0) :
    Spec row :=
  ⟨h_flag_bool, h_is_ext_bool, h_io0_zc0, h_io0_zc1, h_io1_cb0, h_io1_cb1,
   h_io0_sf, h_io1_cf, h_flag_setpc⟩

end ZiskFv.AirsClean.Main
