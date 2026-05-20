import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# ArithDiv row type (Clean ProvableStruct, nested sub-structs)

28-slot witness layout for the Arith AIR viewed through ArithDiv.
Same physical columns as `ArithMulRow`, different named view.

PIL: `zisk/state-machines/arith/pil/arith.pil:17-25`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks

structure ArithDivChunks (F : Type) where
  a_0 : F
  a_1 : F
  a_2 : F
  a_3 : F
  b_0 : F
  b_1 : F
  b_2 : F
  b_3 : F
  c_0 : F
  c_1 : F
  c_2 : F
  c_3 : F
  d_0 : F
  d_1 : F
  d_2 : F
  d_3 : F
deriving ProvableStruct

structure ArithDivFlags (F : Type) where
  na : F
  nb : F
  nr : F
  np : F
  sext : F
  m32 : F
  div : F
  main_div : F
  main_mul : F
  op : F
  bus_res1 : F
  multiplicity : F
deriving ProvableStruct

/-- Auxiliary witness columns for the 4-limb carry chain.

    * `fab`, `na_fb`, `nb_fa` — sign-product witnesses pinned by PIL
      constraints 6, 7, 8 (arith.pil:58-60). On unsigned rows these
      collapse to `(1, 0, 0)`; on signed rows they encode the
      `(1 - 2na)(1 - 2nb)` factorization.
    * `carry_0..carry_6` — the seven 16-bit carry witnesses propagating
      through the 8-chunk packed product / division relation
      (arith.pil:205-209). The 8th equation closes against
      `(eq[7]) + carry[6] = 0` with no further carry. -/
structure ArithDivAux (F : Type) where
  fab : F
  na_fb : F
  nb_fa : F
  carry_0 : F
  carry_1 : F
  carry_2 : F
  carry_3 : F
  carry_4 : F
  carry_5 : F
  carry_6 : F
deriving ProvableStruct

structure ArithDivRow (F : Type) where
  chunks : ArithDivChunks F
  flags : ArithDivFlags F
  aux : ArithDivAux F
deriving ProvableStruct

end ZiskFv.AirsClean.ArithDiv
