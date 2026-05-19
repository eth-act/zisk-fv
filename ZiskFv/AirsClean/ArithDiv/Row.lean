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

structure ArithDivRow (F : Type) where
  chunks : ArithDivChunks F
  flags : ArithDivFlags F
deriving ProvableStruct

end ZiskFv.AirsClean.ArithDiv
