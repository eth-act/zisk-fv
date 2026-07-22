import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# MemAlignRom typed channel

Clean channel wrapper for ZisK's virtual MemAlign ROM lookup (`bus_id = 133`).
The static provider owns membership in the six-column ROM; consumers make no
local membership claim and finished-channel balance transports that fact.

PIL citation: `zisk/state-machines/mem/pil/mem_align_rom.pil:6-313`.

## Trust note

No axioms. `MemAlignRomChannel.Guarantees` is `True`; exact membership comes
from the static provider and the finished-channel protocol, not from a
consumer-side promise.
-/

namespace ZiskFv.Channels.MemAlignRom

open Goldilocks

/-- The bus-133 MemAlign ROM payload in its upstream lookup order:
`[PC, DELTA_PC, DELTA_ADDR, OFFSET, WIDTH, FLAGS]`. -/
structure MemAlignRomMessage (F : Type) where
  pc : F
  deltaPc : F
  deltaAddr : F
  offset : F
  width : F
  flags : F
deriving ProvableStruct

/-- Consumer messages on bus 133 carry no local table-membership guarantee.
The static provider and finished balance are the membership route. -/
instance MemAlignRomChannel : Channel FGL MemAlignRomMessage where
  name := "MemAlignRom133"
  Guarantees _msg _data := True

end ZiskFv.Channels.MemAlignRom
