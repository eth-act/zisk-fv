import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# Main row type (Clean ProvableStruct)

The 18-slot witness layout for ZisK's Main AIR. Mirrors
`Valid_Main`'s named columns.

PIL: `zisk/state-machines/main/pil/main.pil`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks

structure MainRow (F : Type) where
  a_0 : F
  a_1 : F
  b_0 : F
  b_1 : F
  c_0 : F
  c_1 : F
  flag : F
  pc : F
  is_external_op : F
  op : F
  m32 : F
  ind_width : F
  set_pc : F
  jmp_offset1 : F
  jmp_offset2 : F
  store_pc : F
  im_high_degree_2 : F
  segment_l1 : F
deriving ProvableStruct

end ZiskFv.AirsClean.Main
