import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# PcContinuation typed channel (XCAP #100 / PR-X100.1 PROBE — THROWAWAY)

THROWAWAY de-risk probe. Mirrors `Channels/SegmentContinuation.lean`'s
`SeamContChannel` but carries a PC + tag (for the cross-row Main PC handshake,
issue #100). The tag is the per-row chain position; the value lane carries `pc`.

`Guarantees := True`, exactly like `SeamContChannel`: the cross-row handshake is
a GLOBAL balance fact, not a per-row channel guarantee.
-/

namespace ZiskFv.Channels.PcContinuation

open Goldilocks

/-- The 2-slot PC-continuation message: `[pc, tag]`. (The seam template carries 5
    slots; PC only needs the value lane + tag, but we keep a small struct to
    mirror `SeamMessage`.) -/
structure PcMessage (F : Type) where
  pc : F
  tag : F
deriving ProvableStruct

/-- The PC-continuation channel. As with `SeamContChannel`, the guarantee is
    `True`: the cross-row PC link is enforced by `Air.Balance` over the ensemble. -/
instance PcContChannel : Channel FGL PcMessage where
  name := "PcContinuation"
  Guarantees _msg _data := True

end ZiskFv.Channels.PcContinuation
