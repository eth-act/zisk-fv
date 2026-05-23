import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Airs.Tables.BinaryExtensionTable

/-!
# BinaryExtensionTable typed channel

Clean channel wrapper for ZisK's BinaryExtensionTable lookup bus
(`bus_id = 124`).

`BinaryExtension` rows pull one message per byte. Pulling from the channel
gives the same table semantic guarantee currently represented by
`Airs/Tables/BinaryExtensionTable.lean::bin_ext_table_consumer_wf`, but as a
Clean channel guarantee rather than as an ambient axiom. The balanced
provider side is terminal C7 work; this file only introduces the typed
payload and guarantee.

## Trust note

No axioms. `BinaryExtensionTableChannel.Guarantees` is a definition over the
existing `wf_properties` predicate.
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

/-- The BinaryExtensionTable channel. A pull receives the table row
    semantics for the pulled message; C7 supplies the balanced
    static/provider side. -/
instance BinaryExtensionTableChannel : Channel FGL BinaryExtensionTableMessage where
  name := "BinaryExtensionTable"
  Guarantees msg _data :=
    wf_properties (BinaryExtensionTableMessage.toEntry msg 1)

end ZiskFv.Channels.BinaryExtensionTable
