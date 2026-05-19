import ZiskFv.SailSpec.BusEffect
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.MemoryBus

/-!
# State effect via channel interactions

This file defines `state_effect_via_channels` — the channel-balance-
shaped successor to `bus_effect.2`. The current `equiv_<OP>` canonical
theorem shape is:

```
equiv_<OP> : execute_instruction ... state = (bus_effect exec_row mem_rows state).2
```

where `exec_row, mem_rows` are caller-supplied lists. Phase 4's
`equiv_<OP>_v2` will pivot to:

```
equiv_<OP>_v2 : execute_instruction ... state = state_effect_via_channels cs state
```

where `cs` packages the ensemble's channel-interaction output — the
*provenance* of the bus rows comes from `Clean.Air.Balance` instead
of from caller-supplied row witnesses + per-AIR axioms.

This file establishes:

1. `ChannelEnsembleOutput`: the package of channel-interaction data
   exported by an ensemble's row, sufficient to determine
   `state_effect_via_channels`.

2. `state_effect_via_channels`: the post-state function (same return
   type as `bus_effect.2`).

3. `state_effect_via_channels_eq_bus_effect_2`: the compatibility
   bridge. By definition for the trivial extractors, the equality is
   `rfl`. Phase 3 will introduce derived extractors that route
   through channel-balance theorems.

## Trust note

No axiom added. The point of this file is to establish the
*signature* that Phase 4 wrappers will target; the *justification*
that `cs.execMessages` / `cs.memMessages` are well-formed comes from
the ensemble's `BalancedInteractions` proof (a theorem in
`Clean.Air.Balance`, not an axiom).
-/

namespace ZiskFv.Vm

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusMessage)
open ZiskFv.Channels.MemoryBus (MemBusMessage)

/-- Channel-interaction output sufficient to compute the post-state
    for one executed instruction. Mirrors the shape currently
    threaded as `(exec_row, mem_rows)` in `bus_effect`, but routes
    through typed channel messages.

    The fields are concrete `Interaction.*BusEntry` lists for now —
    the trust improvement is in *how* the caller obtains them
    (channel balance vs per-AIR axioms), not in changing the
    underlying data representation. -/
structure ChannelEnsembleOutput where
  execRows : List (Interaction.ExecutionBusEntry FGL)
  memRows  : List (Interaction.MemoryBusEntry FGL)

namespace ChannelEnsembleOutput

/-- Lift an `OpBusMessage` push-side interaction to the execution-
    bus entry list. Convenience for Phase 3 derivation lemmas. The
    `msg` is the source of the `pc` / `timestamp` projections — left
    implicit here because the execution bus only takes pc+timestamp,
    not the full op tuple. -/
@[reducible]
def execEntryOfOpBus (multiplicity : FGL) (_msg : OpBusMessage FGL)
    (pc : FGL) (timestamp : FGL) : Interaction.ExecutionBusEntry FGL :=
  { multiplicity := multiplicity, pc := pc, timestamp := timestamp }

/-- Convert a `MemBusMessage` channel-interaction into a memory-bus
    entry by supplying the multiplicity. -/
@[reducible]
def memEntryOfMemBus (multiplicity : FGL) (msg : MemBusMessage FGL)
    : Interaction.MemoryBusEntry FGL :=
  ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry msg multiplicity

end ChannelEnsembleOutput

/-- The post-state of executing one instruction, computed from
    channel-interaction output. By definition, this routes through
    `bus_effect.2` after projecting the `ChannelEnsembleOutput`'s
    list fields.

    The "via channels" name reflects *provenance*: in the new
    architecture, `cs` is supplied by an ensemble-soundness theorem
    (not by direct caller witness), so the bus rows are
    channel-balanced. -/
@[reducible]
def state_effect_via_channels
    (cs : ChannelEnsembleOutput)
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    : EStateM.Result (Sail.Error exception) (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult :=
  (bus_effect cs.execRows cs.memRows state).2

/-- The compatibility bridge. By definition, the channel-routed
    post-state equals the direct `bus_effect.2` post-state when the
    channel output's row lists agree with the caller's. -/
theorem state_effect_via_channels_eq_bus_effect_2
    (execRows : List (Interaction.ExecutionBusEntry FGL))
    (memRows : List (Interaction.MemoryBusEntry FGL))
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) :
    state_effect_via_channels ⟨execRows, memRows⟩ state
      = (bus_effect execRows memRows state).2 := by
  rfl

end ZiskFv.Vm
