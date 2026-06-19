import Clean.Circuit.Channel
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import ZiskFv.Field.Goldilocks

/-!
# Mem row type (Clean ProvableStruct)

The 13-slot witness layout for ZisK's Mem AIR (memory provider).
Mirrors `Valid_Mem`'s named columns minus stage-2 accumulators.

PIL: `zisk/state-machines/mem/pil/mem.pil`.

## Trust note

No axiom added.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks

structure MemRow (F : Type) where
  addr : F
  step : F
  sel : F
  addr_changes : F
  step_dual : F
  sel_dual : F
  value_0 : F
  value_1 : F
  wr : F
  previous_step : F
  increment_0 : F
  increment_1 : F
  read_same_addr : F
  -- segment-boundary columns (XCAP #103, route (b)): the raw cross-segment seam
  -- tuple components + tag. They carry the segment-continuation channel
  -- (`ZiskFv/Channels/SegmentContinuation.lean`) RAW so that — once the seam
  -- channel is added to the ensemble via `SoundEnsemble.addChannel` — global
  -- balance forces `seg_n.segment_last_* = seg_{n+1}.previous_segment_*`. They
  -- do NOT participate in the per-row Mem `Spec` (value/addr/ordering), which is
  -- about the 13 base columns above and is preserved unchanged.
  segment_id : F
  previous_segment_value_0 : F
  previous_segment_value_1 : F
  previous_segment_addr : F
  previous_segment_step : F
  segment_last_value_0 : F
  segment_last_value_1 : F
  segment_last_addr : F
  segment_last_step : F
  -- last-segment gating column: the outgoing PUSH of `segment_last_*` is
  -- multiplied by `(1 - is_last_segment)` so the final segment emits NO push
  -- (`mem.pil:241` `direct_gsum_1` gated `* (1 - is_last_segment)`).
  is_last_segment : F
  -- SEGMENT_LAST gating column (XCAP #103 deep refactor, step B). `1` exactly on
  -- the LAST row of a segment (`mem.pil:87` `SEGMENT_LAST = SEGMENT_L1'`), `0`
  -- elsewhere. The seam emission is gated by it so a k-row segment emits exactly
  -- ONE live pull + ONE live push (the `seg_last = 1` row) and `k - 1` DEAD
  -- (multiplicity-0) emissions — making the per-segment continuation faithful to
  -- a multi-row Mem trace (the ungated per-row emission only balanced at k = 1).
  seg_last : F
deriving ProvableStruct

end ZiskFv.AirsClean.Mem
