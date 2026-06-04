import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Mem
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.EquivCore.Bridge.SailStateBridge
import ZiskFv.SailSpec.sb
import ZiskFv.SailSpec.sh
import ZiskFv.SailSpec.sw

/-!
# Mem discharge bridge

The legacy lookup-backed load/store bridge entries were retired by the
T4 Clean memory-channel migration. Canonical memory opcodes now use
`Bridge.MemClean`, where explicit Clean provider rows are adapted to the
legacy bus-effect rows without the retired Main/provider memory axioms.
-/

namespace ZiskFv.EquivCore.Bridge.Mem

end ZiskFv.EquivCore.Bridge.Mem
