import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# Binary row type (Clean ProvableStruct, nested sub-structs)

The 38-slot stage-1 witness layout for ZisK's Binary AIR. Split
into nested sub-structs to stay under the `deriving ProvableStruct`
macro field limit.

PIL: `zisk/state-machines/binary/pil/binary.pil`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks

structure BinaryAByteCols (F : Type) where
  free_in_a_0 : F
  free_in_a_1 : F
  free_in_a_2 : F
  free_in_a_3 : F
  free_in_a_4 : F
  free_in_a_5 : F
  free_in_a_6 : F
  free_in_a_7 : F
deriving ProvableStruct

structure BinaryBByteCols (F : Type) where
  free_in_b_0 : F
  free_in_b_1 : F
  free_in_b_2 : F
  free_in_b_3 : F
  free_in_b_4 : F
  free_in_b_5 : F
  free_in_b_6 : F
  free_in_b_7 : F
deriving ProvableStruct

structure BinaryCByteCols (F : Type) where
  free_in_c_0 : F
  free_in_c_1 : F
  free_in_c_2 : F
  free_in_c_3 : F
  free_in_c_4 : F
  free_in_c_5 : F
  free_in_c_6 : F
  free_in_c_7 : F
deriving ProvableStruct

structure BinaryChainCols (F : Type) where
  carry_0 : F
  carry_1 : F
  carry_2 : F
  carry_3 : F
  carry_4 : F
  carry_5 : F
  carry_6 : F
  carry_7 : F
  b_op : F
  b_op_or_sext : F
deriving ProvableStruct

structure BinaryModeCols (F : Type) where
  mode32 : F
  result_is_a : F
  use_first_byte : F
  c_is_signed : F
  mode32_and_c_is_signed : F
deriving ProvableStruct

structure BinaryRow (F : Type) where
  aBytes : BinaryAByteCols F
  bBytes : BinaryBByteCols F
  cBytes : BinaryCByteCols F
  chain : BinaryChainCols F
  mode : BinaryModeCols F
deriving ProvableStruct

end ZiskFv.AirsClean.Binary
