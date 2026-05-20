import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# ArithMul row type (Clean ProvableStruct, nested sub-structs)

28-slot witness layout for the Arith AIR viewed through ArithMul.
Nested as chunks + flags to stay under the macro field limit.

PIL: `zisk/state-machines/arith/pil/arith.pil:17-25`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

structure ArithMulChunks (F : Type) where
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

structure ArithMulFlags (F : Type) where
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

/-- Carry-chain auxiliary witnesses: 7 carries (PIL cols 0–6)
    plus the sign-product helpers `fab`, `na_fb`, `nb_fa`
    (cols 30–32). -/
structure ArithMulCarries (F : Type) where
  carry_0 : F
  carry_1 : F
  carry_2 : F
  carry_3 : F
  carry_4 : F
  carry_5 : F
  carry_6 : F
  fab : F
  na_fb : F
  nb_fa : F
deriving ProvableStruct

structure ArithMulRow (F : Type) where
  chunks : ArithMulChunks F
  flags : ArithMulFlags F
  carries : ArithMulCarries F
deriving ProvableStruct

end ZiskFv.AirsClean.ArithMul
