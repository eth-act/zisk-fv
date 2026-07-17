import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Airs.Tables.BinaryExtensionTable

/-!
# BinaryExtensionTable typed channel

Clean channel wrapper for ZisK's BinaryExtensionTable lookup bus
(`bus_id = 124`).

`BinaryExtension` rows emit one negative consumer message per byte. The static
provider owns exact membership; finished-channel balance transports that
membership to the consumer. This wrapper deliberately adds no per-emission
semantic guarantee.

## Trust note

No axioms. `BinaryExtensionTableChannel.Guarantees` is `True`; the provider's
exact static-table specification and finished-channel balance are the
soundness route.
-/

namespace ZiskFv.Channels.BinaryExtensionTable

open Goldilocks
open ZiskFv.Airs.Tables.BinaryExtensionTable

/-- The seven-slot BinaryExtensionTable lookup payload, without
    multiplicity. Clean carries multiplicity on the channel interaction. -/
structure BinaryExtensionTableMessage (F : Type) where
  op : F
  byte_index : F
  a_byte : F
  shift_amount : F
  c_lo_byte : F
  c_hi_byte : F
  op_is_shift : F
deriving ProvableStruct

/-- Convert the Clean channel message to the legacy BinaryExtensionTable
    entry, supplying the interaction multiplicity. -/
@[reducible]
def BinaryExtensionTableMessage.toEntry
    (msg : BinaryExtensionTableMessage FGL) (multiplicity : FGL) :
    BinaryExtensionTableEntry FGL :=
  { multiplicity := multiplicity
    op := msg.op
    byte_index := msg.byte_index
    a_byte := msg.a_byte
    shift_amount := msg.shift_amount
    c_lo_byte := msg.c_lo_byte
    c_hi_byte := msg.c_hi_byte
    op_is_shift := msg.op_is_shift }

/-- The BinaryExtensionTable channel. Consumer emissions make no local
    membership claim; the provider and finished balance establish it. -/
instance BinaryExtensionTableChannel : Channel FGL BinaryExtensionTableMessage where
  name := "BinaryExtensionTable"
  Guarantees _msg _data := True

end ZiskFv.Channels.BinaryExtensionTable
