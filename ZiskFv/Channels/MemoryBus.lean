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
`Clean.Channel FGL MemBusMessage`. The 11-slot `MemBusMessage`
mirrors `Interaction.MemoryBusEntry` minus the multiplicity (Clean
carries multiplicity as `ChannelInteraction.mult`). A round-trip
equivalence with `Interaction.MemoryBusEntry FGL` is provided.

## Trust note

Same pattern as `Channels/OperationBus.lean` — no new axioms. The
1 memory-bus axiom `lookup_consumer_matches_provider_load` (in
`Airs/MemoryBus/MemBridge.lean`) can be retired in Phase 3 once
Mem + MemAlign* are rewritten as Clean components.
-/

namespace ZiskFv.Channels.MemoryBus

open Goldilocks

/-- The 11-slot memory-bus message. Mirrors
    `Interaction.MemoryBusEntry FGL` minus the multiplicity. -/
structure MemBusMessage (F : Type) where
  as : F
  ptr : F
  x0 : F
  x1 : F
  x2 : F
  x3 : F
  x4 : F
  x5 : F
  x6 : F
  x7 : F
  timestamp : F
deriving ProvableStruct

@[reducible]
def MemBusMessage.toEntry (msg : MemBusMessage FGL) (multiplicity : FGL)
    : Interaction.MemoryBusEntry FGL :=
  { multiplicity := multiplicity
  , as := msg.as
  , ptr := msg.ptr
  , x0 := msg.x0
  , x1 := msg.x1
  , x2 := msg.x2
  , x3 := msg.x3
  , x4 := msg.x4
  , x5 := msg.x5
  , x6 := msg.x6
  , x7 := msg.x7
  , timestamp := msg.timestamp
  }

@[reducible]
def MemBusMessage.ofEntry (entry : Interaction.MemoryBusEntry FGL)
    : MemBusMessage FGL :=
  { as := entry.as
  , ptr := entry.ptr
  , x0 := entry.x0
  , x1 := entry.x1
  , x2 := entry.x2
  , x3 := entry.x3
  , x4 := entry.x4
  , x5 := entry.x5
  , x6 := entry.x6
  , x7 := entry.x7
  , timestamp := entry.timestamp
  }

theorem MemBusMessage.ofEntry_toEntry (msg : MemBusMessage FGL) (mult : FGL) :
    MemBusMessage.ofEntry (MemBusMessage.toEntry msg mult) = msg := by
  rfl

theorem MemBusMessage.toEntry_ofEntry (entry : Interaction.MemoryBusEntry FGL) :
    MemBusMessage.toEntry (MemBusMessage.ofEntry entry) entry.multiplicity = entry := by
  rfl

/-- The MemoryBus channel. As with `OpBusChannel`, the guarantee is
    `True`: cross-AIR consistency is enforced by `Air.Balance`, and
    per-opcode load/store semantics are layered in via the per-opcode
    wrappers in Phase 4 — not bundled into the channel guarantee. -/
instance MemBusChannel : Channel FGL MemBusMessage where
  name := "MemoryBus"
  Guarantees _msg _data := True

end ZiskFv.Channels.MemoryBus
