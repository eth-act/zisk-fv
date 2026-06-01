import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.OperationBus.OperationBus

/-!
# OperationBus typed channel

ZisK's primary cross-AIR channel. Main pulls a per-row tuple
describing the executed instruction; the corresponding provider AIR
(BinaryAdd / Binary / BinaryExtension / Arith*) pushes a matching
tuple.

This file introduces the channel as a `Clean.Channel FGL OpBusMessage`.
The 11-slot `OpBusMessage` mirrors the existing `OperationBusEntry`
record (minus the multiplicity, which Clean carries as a separate
`ChannelInteraction.mult`). A round-trip equivalence with
`OperationBusEntry` lives at the bottom — Phase 2 will use it to
state `state_effect_via_channels_eq_bus_effect_2`.

## Trust note

This file does NOT add any axiom. The channel's `Guarantees` is
*defined* — whether a particular provider's push discharges the
guarantee is each provider AIR's local proof obligation, and the
cross-AIR consistency is `Clean.Air.Balance.BalancedInteractions`'s
output, which is a theorem (not an axiom).

The 1 operation-bus axiom currently in
`trust/generated/baseline-axioms.txt::op_bus_permutation_sound`
(consolidated form on `clean-integration`) can be retired in Phase 3
once each provider AIR is rewritten as a Clean component.
-/

namespace ZiskFv.Channels.OperationBus

open Goldilocks

/-- The 11-slot operation-bus message. Mirrors `OperationBusEntry`
    minus the multiplicity (Clean carries multiplicity as a separate
    `ChannelInteraction.mult`).

    Slot semantics match `Airs/OperationBus/OperationBus.lean::OperationBusEntry`. -/
structure OpBusMessage (F : Type) where
  op : F
  a_lo : F
  a_hi : F
  b_lo : F
  b_hi : F
  c_lo : F
  c_hi : F
  flag : F
  main_step : F
  extended_arg : F
  extra_args_0 : F
deriving ProvableStruct

/-- Convert a `Clean.OpBusMessage` to the existing zisk-fv
    `OperationBusEntry`, supplying a multiplicity. The multiplicity
    is the bridge: in Clean's model it lives on the channel
    interaction; in zisk-fv's `OperationBusEntry` it's a record field. -/
@[reducible]
def OpBusMessage.toEntry (msg : OpBusMessage FGL) (multiplicity : FGL)
    : ZiskFv.Airs.OperationBus.OperationBusEntry FGL :=
  { multiplicity := multiplicity
  , op := msg.op
  , a_lo := msg.a_lo
  , a_hi := msg.a_hi
  , b_lo := msg.b_lo
  , b_hi := msg.b_hi
  , c_lo := msg.c_lo
  , c_hi := msg.c_hi
  , flag := msg.flag
  , main_step := msg.main_step
  , extended_arg := msg.extended_arg
  , extra_args_0 := msg.extra_args_0
  }

/-- Inverse direction — project an `OperationBusEntry` to a `OpBusMessage`.
    The multiplicity is dropped (recovered separately). -/
@[reducible]
def OpBusMessage.ofEntry (entry : ZiskFv.Airs.OperationBus.OperationBusEntry FGL)
    : OpBusMessage FGL :=
  { op := entry.op
  , a_lo := entry.a_lo
  , a_hi := entry.a_hi
  , b_lo := entry.b_lo
  , b_hi := entry.b_hi
  , c_lo := entry.c_lo
  , c_hi := entry.c_hi
  , flag := entry.flag
  , main_step := entry.main_step
  , extended_arg := entry.extended_arg
  , extra_args_0 := entry.extra_args_0
  }

theorem OpBusMessage.ofEntry_toEntry (msg : OpBusMessage FGL) (mult : FGL) :
    OpBusMessage.ofEntry (OpBusMessage.toEntry msg mult) = msg := by
  rfl

theorem OpBusMessage.toEntry_ofEntry (entry : ZiskFv.Airs.OperationBus.OperationBusEntry FGL) :
    OpBusMessage.toEntry (OpBusMessage.ofEntry entry) entry.multiplicity = entry := by
  rfl

/-- Field projection for evaluated Clean op-bus messages. This is intentionally
    stated once at the channel boundary so downstream balance proofs can read
    the opcode slot without unfolding a whole provider row expression. -/
theorem OpBusMessage.eval_op
    (env : Environment FGL) (msg : OpBusMessage (Expression FGL)) :
    (eval env msg).op = Expression.eval env msg.op := by
  rw [ProvableStruct.eval_eq_eval]
  cases msg
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

/-- The 64-bit packed value of the `a` lane. -/
@[reducible]
def OpBusMessage.aPacked (msg : OpBusMessage FGL) : ℕ :=
  msg.a_lo.val + msg.a_hi.val * 2 ^ 32

@[reducible]
def OpBusMessage.bPacked (msg : OpBusMessage FGL) : ℕ :=
  msg.b_lo.val + msg.b_hi.val * 2 ^ 32

@[reducible]
def OpBusMessage.cPacked (msg : OpBusMessage FGL) : ℕ :=
  msg.c_lo.val + msg.c_hi.val * 2 ^ 32

/-- The OperationBus channel — uninhabited semantic gate.

    `Guarantees` is `True` for now: the channel acts as a structural
    pipe whose payload's *consistency* across pushes and pulls is
    enforced by `Clean.Air.Balance`. Per-opcode semantic guarantees
    (e.g. ADD's `c-packed = a-packed + b-packed mod 2^64`) are
    layered in *separately* via `OpEnvelope`-dispatched per-opcode
    proofs in Phase 4, not bundled into the channel guarantee.

    This keeps the channel as a single shared bus across all opcodes
    while letting per-opcode semantics be discharged in their own
    files. -/
instance OpBusChannel : Channel FGL OpBusMessage where
  name := "OperationBus"
  Guarantees _msg _data := True

/-- Equal evaluated Clean op-bus message arrays give equal legacy
    `OperationBusEntry` payloads when both sides are viewed with
    multiplicity `1`.

This is the small message-level bridge used by the Clean balance path: balance
proves equality of raw channel message arrays, while legacy opcode proofs
consume `matches_entry` over `OperationBusEntry` records. -/
theorem matches_entry_of_eval_msg_eq
    {mainMsg providerMsg : OpBusMessage (Expression FGL)}
    {mainMult : Expression FGL}
    {mainEnv providerEnv : Environment FGL}
    (h_msg :
      (((OpBusChannel.pushed providerMsg).toRaw).eval providerEnv).msg =
        (((OpBusChannel.emitted mainMult mainMsg).toRaw).eval mainEnv).msg) :
    ZiskFv.Airs.OperationBus.matches_entry
      (OpBusMessage.toEntry (eval mainEnv mainMsg) 1)
      (OpBusMessage.toEntry (eval providerEnv providerMsg) 1) := by
  have h_vec :
      Vector.map (Expression.eval providerEnv) (toElements providerMsg) =
        Vector.map (Expression.eval mainEnv) (toElements mainMsg) := by
    apply Vector.toArray_injective
    simpa [ChannelInteraction.toRaw, AbstractInteraction.eval] using h_msg
  have h_eval : eval providerEnv providerMsg = eval mainEnv mainMsg := by
    have h_from := congrArg
      (fun xs => (fromElements xs : OpBusMessage FGL)) h_vec
    simpa [ProvableType.fromElements_eval_toElements] using h_from
  rw [h_eval]
  simp [ZiskFv.Airs.OperationBus.matches_entry]

end ZiskFv.Channels.OperationBus
