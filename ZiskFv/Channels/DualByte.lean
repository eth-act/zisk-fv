import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

namespace ZiskFv.Channels.DualByte
open Goldilocks

/-- Source bus88: ordered `[byte_a, byte_b]`, not a packed scalar. -/
structure DualByteMessage (F : Type) where
  byte_a : F
  byte_b : F
deriving ProvableStruct

/-- Local guarantees deliberately do not assume virtual-table membership.
The provider owns membership; ensemble balance must transport it. -/
instance DualByteChannel : Channel FGL DualByteMessage where
  name := "DualByte88"
  Guarantees _ _ := True

end ZiskFv.Channels.DualByte
