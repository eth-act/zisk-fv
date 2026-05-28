import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction

/-!
# MemoryBus typed channel

ZisK's memory-bus channel: Main pushes register/memory read/write
requests; Mem (the memory AIR) consumes them and emits provider
rows; MemAlign* sub-byte read providers handle aligned loads.

This file introduces the channel as
`Clean.Channel FGL MemBusMessage`. The 6-slot `MemBusMessage` is the
real PIL memory-bus tuple:

```
[mem_op, addr, step, width, value_0, value_1]
```

Clean carries multiplicity as `ChannelInteraction.mult`, so it is not
part of the message. This PIL tuple is intentionally **not** definitionally
identified with the legacy architectural `Interaction.MemoryBusEntry`;
load/store equivalence proofs use explicit adapter lemmas when they need
to translate a PIL-shaped memory interaction into a legacy bus-effect row.

## Trust note

Same pattern as `Channels/OperationBus.lean` — no new axioms. The
memory-bus axioms in `Airs/MemoryBus/{MemBridge,MemAlignBridge}.lean`
can only be retired by proved adapters from this PIL-shaped channel to
the legacy architectural rows consumed by `bus_effect`.
-/

namespace ZiskFv.Channels.MemoryBus

open Goldilocks

/-- The 6-slot memory-bus message emitted on PIL `MEMORY_ID`:
    `[mem_op, addr, step, width, value_0, value_1]`. -/
structure MemBusMessage (F : Type) where
  mem_op : F
  ptr : F
  timestamp : F
  width : F
  value_0 : F
  value_1 : F
deriving ProvableStruct

/-! ## Legacy architectural adapter

The Clean channel message is the real PIL tuple
`[mem_op, ptr, timestamp, width, value_0, value_1]`. The legacy
`Interaction.MemoryBusEntry` consumed by `bus_effect` has
`[multiplicity, as, ptr, value_0, value_1, timestamp]`.

The address-space slot is therefore an explicit argument here. This keeps
the adapter honest: `mem_op = 1/2/3` is a PIL operation code, while
legacy `as = 2` means memory-side and `as = 1` means register-side.
-/

@[reducible]
def MemBusMessage.toEntry
    (msg : MemBusMessage FGL) (multiplicity as : FGL) :
    Interaction.MemoryBusEntry FGL :=
  { multiplicity := multiplicity
    as := as
    ptr := msg.ptr
    value_0 := msg.value_0
    value_1 := msg.value_1
    timestamp := msg.timestamp }

@[reducible]
def MemBusMessage.ofEntry
    (entry : Interaction.MemoryBusEntry FGL) (mem_op width : FGL) :
    MemBusMessage FGL :=
  { mem_op := mem_op
    ptr := entry.ptr
    timestamp := entry.timestamp
    width := width
    value_0 := entry.value_0
    value_1 := entry.value_1 }

theorem MemBusMessage.toEntry_ofEntry
    (entry : Interaction.MemoryBusEntry FGL) (mem_op width : FGL) :
    MemBusMessage.toEntry
      (MemBusMessage.ofEntry entry mem_op width)
      entry.multiplicity entry.as = entry := by
  rfl

theorem MemBusMessage.ofEntry_toEntry
    (msg : MemBusMessage FGL) (multiplicity as : FGL) :
    MemBusMessage.ofEntry
      (MemBusMessage.toEntry msg multiplicity as)
      msg.mem_op msg.width = msg := by
  rfl

/-- The MemoryBus channel. As with `OpBusChannel`, the guarantee is
    `True`: cross-AIR consistency is enforced by `Air.Balance`, and
    per-opcode load/store semantics are layered in via the per-opcode
    wrappers in Phase 4 — not bundled into the channel guarantee. -/
instance MemBusChannel : Channel FGL MemBusMessage where
  name := "MemoryBus"
  Guarantees _msg _data := True

end ZiskFv.Channels.MemoryBus
