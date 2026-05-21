import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# MemAlignBus typed channel (Phase C1)

ZisK's memory bus (`bus_id = 10 = MEMORY_ID`) is consumed by two
distinct tuple shapes:

* the **12-slot** shape used by the `Mem` AIR
  (`Channels/MemoryBus.lean :: MemBusMessage` — eight byte lanes); and
* the **6-slot** shape used by the **MemAlign\*** family of unaligned
  sub-doubleword access providers,
  `[mem_op, addr, step, width, value_0, value_1]`.

The MemAlign-family proves-side emission is the `permutation_proves`
PIL macro
(`zisk/state-machines/mem/pil/mem_align_byte.pil:96`):

```
permutation_proves(MEMORY_ID, [mem_op, main_addr, step, 1, bus_byte, 0]);
```

`MemAlignBusMessage` mirrors that 6-slot tuple. It is the channel the
MemAlignByte Clean Component (Phase C1) pushes onto, and — once all
MemAlign-family providers are migrated — the consumer side resolves
against it at the family-terminal memory phase (C10).

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

/-- The 6-slot MemAlign-family memory-bus message. Mirrors the
    `permutation_proves(MEMORY_ID, [...])` tuple emitted by the
    MemAlign\* providers (`mem_align_byte.pil:96` and siblings):

    * `mem_op`    — `1 + is_write` (read = 1, write = 2).
    * `addr`      — the byte address `addr_w * 8 + offset`.
    * `step`      — the memory timestamp.
    * `width`     — the access width (1 for the byte providers).
    * `value_0`   — the low value lane.
    * `value_1`   — the high value lane (literal `0` for the byte
      providers — sub-doubleword loads zero-pad the high half). -/
structure MemAlignBusMessage (F : Type) where
  mem_op : F
  addr : F
  step : F
  width : F
  value_0 : F
  value_1 : F
deriving ProvableStruct

/-- The MemAlignBus channel. As with `OpBusChannel` / `MemBusChannel`,
    the guarantee is `True`: cross-AIR consistency is enforced by
    `Air.Balance`, and per-opcode load semantics are layered in via the
    per-opcode wrappers — not bundled into the channel guarantee. -/
instance MemAlignBusChannel : Channel FGL MemAlignBusMessage where
  name := "MemAlignBus"
  Guarantees _msg _data := True

end ZiskFv.Channels.MemAlignBus
