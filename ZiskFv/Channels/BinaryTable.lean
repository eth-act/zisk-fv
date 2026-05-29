import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Airs.Tables.BinaryTable

/-!
# BinaryTable typed channel

Clean channel wrapper for ZisK's BinaryTable lookup bus (`bus_id = 125`).

`Binary` rows pull one message per byte. Pulling from the channel gives the
same table semantic guarantee currently represented by
`Airs/Tables/BinaryTable.lean::bin_table_consumer_wf`, but as a Clean channel
guarantee rather than as an ambient axiom. The balanced provider side is
terminal C7 work; this file only introduces the typed payload and guarantee.

## Trust note

No axioms. `BinaryTableChannel.Guarantees` is a definition over the existing
`wf_properties` predicate.
-/

namespace ZiskFv.Channels.BinaryTable

open Goldilocks
open ZiskFv.Airs.Tables.BinaryTable

/-- The seven-slot BinaryTable lookup payload, without multiplicity.
    Clean carries multiplicity on the channel interaction. -/
structure BinaryTableMessage (F : Type) where
  pos_ind : F
  op : F
  a_byte : F
  b_byte : F
  cin : F
  c_byte : F
  flags : F
deriving ProvableStruct

/-- Convert the Clean channel message to the legacy BinaryTable entry,
    supplying the interaction multiplicity. -/
@[reducible]
def BinaryTableMessage.toEntry (msg : BinaryTableMessage FGL) (multiplicity : FGL) :
    BinaryTableEntry FGL :=
  { multiplicity := multiplicity
    pos_ind := msg.pos_ind
    op := msg.op
    a_byte := msg.a_byte
    b_byte := msg.b_byte
    cin := msg.cin
    c_byte := msg.c_byte
    flags := msg.flags }

/-- The BinaryTable channel. A pull receives the table row semantics for the
    pulled message; C7 supplies the balanced static/provider side. -/
instance BinaryTableChannel : Channel FGL BinaryTableMessage where
  name := "BinaryTable"
  Guarantees msg _data := wf_properties (BinaryTableMessage.toEntry msg 1)

end ZiskFv.Channels.BinaryTable
