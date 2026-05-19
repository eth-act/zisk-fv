import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# BinaryExtension row type (Clean ProvableStruct, nested sub-structs)

30-slot stage-1 witness layout for ZisK's BinaryExtension AIR.
Nested as `aCols + cCols + cExtCols + flags` to avoid the macro
field limit.

PIL: `zisk/state-machines/binary/pil/binary_extension.pil`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks

structure BinaryExtensionACols (F : Type) where
  free_in_a_0 : F
  free_in_a_1 : F
  free_in_a_2 : F
  free_in_a_3 : F
  free_in_a_4 : F
  free_in_a_5 : F
  free_in_a_6 : F
  free_in_a_7 : F
deriving ProvableStruct

structure BinaryExtensionCColsLo (F : Type) where
  free_in_c_0 : F
  free_in_c_1 : F
  free_in_c_2 : F
  free_in_c_3 : F
  free_in_c_4 : F
  free_in_c_5 : F
  free_in_c_6 : F
  free_in_c_7 : F
deriving ProvableStruct

structure BinaryExtensionCColsHi (F : Type) where
  free_in_c_8 : F
  free_in_c_9 : F
  free_in_c_10 : F
  free_in_c_11 : F
  free_in_c_12 : F
  free_in_c_13 : F
  free_in_c_14 : F
  free_in_c_15 : F
deriving ProvableStruct

structure BinaryExtensionFlags (F : Type) where
  op : F
  free_in_b : F
  op_is_shift : F
  b_0 : F
  b_1 : F
deriving ProvableStruct

structure BinaryExtensionRow (F : Type) where
  aCols : BinaryExtensionACols F
  cColsLo : BinaryExtensionCColsLo F
  cColsHi : BinaryExtensionCColsHi F
  flags : BinaryExtensionFlags F
deriving ProvableStruct

end ZiskFv.AirsClean.BinaryExtension
