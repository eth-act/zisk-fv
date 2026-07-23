import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# MemAlign byte-range channel

Clean's typed wrapper for the eight single-value Range Check lookups emitted
by `MemAlign` on bus 107.  The static provider owns membership in the exact
byte table; consumers make no local membership claim, and the finished
channel transports that fact through balance.

PIL citation: `zisk/state-machines/mem/pil/mem_align.pil:113-118`; manifest
hints #982/#984/#986/#988/#990/#992/#994/#996.
-/

namespace ZiskFv.Channels.MemAlignRanges

open Goldilocks

/-- The one-slot bus-107 payload: one MemAlign register byte. -/
structure MemAlignRangeMessage (F : Type) where
  value : F
deriving ProvableStruct

/-- The MemAlign register-byte range-check channel. -/
instance MemAlignRangeChannel : Channel FGL MemAlignRangeMessage where
  name := "MemAlignRange107"
  Guarantees _msg _data := True

end ZiskFv.Channels.MemAlignRanges
