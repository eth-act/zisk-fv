import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks
import ZiskFv.Channels.MemoryBus

/-!
# MemAlignBus compatibility aliases

The MemAlign-family providers emit the same PIL memory-bus tuple as
Main and Mem:

```
[mem_op, addr, step, width, value_0, value_1]
```

Earlier Clean scaffolding introduced a separate `MemAlignBusChannel`.
Keep these names as reducible compatibility aliases while migrating
callers; they are the unified `MemoryBus` channel, not a second bus.

## Trust note

This file adds NO axiom. The channel's `Guarantees` is `True` — a
structural pipe. Cross-AIR consistency is `Clean.Air.Balance`'s
output (a theorem); per-opcode load semantics are layered in via the
per-opcode wrappers, not the channel guarantee. Mirrors the
no-axiom contract of `Channels/OperationBus.lean` and
`Channels/MemoryBus.lean`.
-/

namespace ZiskFv.Channels.MemAlignBus

open Goldilocks

abbrev MemAlignBusMessage := ZiskFv.Channels.MemoryBus.MemBusMessage

/-- Compatibility alias for the unified PIL-shaped memory-bus channel. -/
abbrev MemAlignBusChannel : Channel FGL MemAlignBusMessage :=
  ZiskFv.Channels.MemoryBus.MemBusChannel

end ZiskFv.Channels.MemAlignBus
