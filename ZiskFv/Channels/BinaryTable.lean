import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Airs.Tables.BinaryTable

/-!
# BinaryTable typed channel

Clean channel wrapper for ZisK's BinaryTable lookup bus (`bus_id = 125`).

`Binary` rows emit one negative consumer message per byte. The static provider
owns exact membership; finished-channel balance transports that membership to
the consumer. This wrapper deliberately adds no per-emission semantic
guarantee.

## Trust note

No axioms. `BinaryTableChannel.Guarantees` is `True`; the provider's exact
static-table specification and finished-channel balance are the soundness
route.
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

/-- The BinaryTable channel. Consumer emissions make no local membership
    claim; the provider and finished balance establish it. -/
instance BinaryTableChannel : Channel FGL BinaryTableMessage where
  name := "BinaryTable"
  Guarantees _msg _data := True

end ZiskFv.Channels.BinaryTable
