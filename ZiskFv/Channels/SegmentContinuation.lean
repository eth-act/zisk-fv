import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# SegmentContinuation typed channel (XCAP #103 / XS-PR1 framework, Step 1)

ZisK's Mem AIR proves a per-segment permutation accumulator
(`ZiskFv/Airs/Mem.lean:1351/1361` `direct_gsum_0/1`, summed by
`permutation_every_row :1398`) whose GLOBAL cancellation across segments is
what forces the cross-segment seam
`seg.segment_last_* = next_seg.previous_segment_*`. The live single-table /
per-row Clean Mem component (`ZiskFv/AirsClean/Mem/Circuit.lean`) cannot today
EXPRESS that cross-segment fact: it emits only the (row-local) MemBus channel,
and the segment-boundary columns are not even reachable through its row.

This file introduces the **segment-continuation channel** as a
`Clean.Channel FGL SeamMessage` carrying the RAW boundary tuple

```
[value_0, value_1, addr, step, segment_id]
```

so that — once the ensemble is migrated to the `SoundVmEnsemble` driver
(XS-PR1 Step 2) — global balance forces element-wise equality of the matched
pulled/pushed message via `exists_push_of_pull` (validated go/no-go PoC
`tagged_seam_forced`, branch `xseg`), with NO hash-injectivity /
Schwartz-Zippel step. Carrying the tuple RAW is the validated route-(a) relief
the plan (PLAN_ENDGAME_XCAP §2.2 / Risk #4) names (issue #103).

## Trust note

Same pattern as `Channels/MemoryBus.lean` and `Channels/OperationBus.lean` —
**no new axioms**. The channel `Guarantees` is `True`: the cross-segment seam is
NOT bundled into a per-row channel guarantee. It is a GLOBAL balance fact,
discharged by `Air.Balance` once the seam is hosted as a VM channel of a
`SoundVmEnsemble`. This mirrors `MemBusChannel`'s documented `Guarantees := True`
(`Channels/MemoryBus.lean:99-105`): cross-AIR/cross-segment consistency lives in
balance, not in the channel guarantee.

**Scope honesty (XS-PR1 Step 1 boundary).** `permutation_every_row` is a
NON-VANISHING constraint on a Horner HASH (`im_direct_i * direct_gsum_i + 1 = 0`,
i.e. `direct_gsum_i ≠ 0`); it carries NO raw-tuple statement. The raw-tuple seam
fact this channel carries is therefore NOT derivable as a row-local guarantee
from `permutation_every_row` — it is a balance fact of the migrated ensemble
(Step 2). This module delivers only the structural CAPABILITY to expose the
segment-continuation channel from row-local columns; it does not, and cannot at
the row-emission layer, derive the seam.
-/

namespace ZiskFv.Channels.SegmentContinuation

open Goldilocks

/-- The 5-slot segment-boundary message carried on the segment-continuation
    channel: `[value_0, value_1, addr, step, segment_id]`.

    `segment_id` is the per-segment TAG. The ZisK accumulator tags the PULL of
    `previous_segment_*` with `segment_id` (`direct_gsum_0`) and the PUSH of
    `segment_last_*` with `segment_id + 1` (`direct_gsum_1`); carrying the tag
    RAW is what lets balance select the unique matching push per segment
    (validated go/no-go PoC `tagged_seam_forced`). -/
structure SeamMessage (F : Type) where
  value_0 : F
  value_1 : F
  addr : F
  step : F
  segment_id : F
deriving ProvableStruct

/-- The segment-continuation channel. As with `MemBusChannel`/`OpBusChannel`,
    the guarantee is `True`: the cross-segment seam is enforced by `Air.Balance`
    over a `SoundVmEnsemble` (XS-PR1 Step 2), not bundled into the channel
    guarantee. A segment row PULLs its `previous_segment_*` boundary and PUSHes
    its `segment_last_*` boundary — a VM transition. -/
instance SeamContChannel : Channel FGL SeamMessage where
  name := "SegmentContinuation"
  Guarantees _msg _data := True

end ZiskFv.Channels.SegmentContinuation
