Active plan: docs/ai/plan/PLAN_ENDGAME_XCAP.md §4.B (XS-PR1, framework — cross-segment Mem seam).
Branch: xcap-xseg (off origin/main eb19cc8f). Worktree: .worktrees/xcap-xseg.

## Current focus: XS-PR1 Step 1 (structural seam-channel exposure) — DONE, green.

Landed the MINIMAL first green increment of XS-PR1: the live Clean Mem layer can
now EXPOSE a segment-continuation channel from row-local columns — the capability
the per-row component "structurally cannot" do today (PLAN §1 TL;DR).

New files (additive; nothing in the live ensemble imports them — 28 families
byte-identical green):
- ZiskFv/Channels/SegmentContinuation.lean — SeamMessage (raw 5-tuple
  [value_0,value_1,addr,step,segment_id]) + SeamContChannel (Guarantees := True,
  mirroring MemBusChannel).
- ZiskFv/AirsClean/Mem/SeamCircuit.lean — MemSeamRow (MemRow + 9 segment-boundary
  Var fields) + circuitWithSeamAndMemBus / componentWithSeamAndMemBus: emits dual
  MemBus + pull(previous_segment_*) + push(segment_last_*). Soundness/completeness
  closed; 0 PROJECT axioms (kernel-only).
- ZiskFv.lean: + import of SeamCircuit (build coverage only).

Gates: full lake build green (8690 jobs); check-all.sh (V1) ALL PASS;
check-all-semantic.sh (V2) ALL PASS. 63-theorem baselines unchanged (additive).

## Blocking / reported residual (CRITICAL — see PR body)

The firstGreenIncrement asked the seam emission's Requirements/Guarantees be
PROVEN from permutation_every_row. That half is NOT delivered, and is a genuine
reportable obstacle (NOT faked / NOT axiomatized):
- permutation_every_row is ABSENT from the live Clean Mem component (it + the
  SegmentColumns/PermutationColumns live only as Valid_Mem-parameterized defs in
  Airs/Mem.lean + dead defs in Mem/Constraints.lean — grep confirms 0 refs under
  AirsClean/ outside Constraints.lean).
- permutation_every_row is a NON-VANISHING constraint on a Horner HASH
  (im_direct_i * direct_gsum_i + 1 = 0); it carries NO raw-tuple statement, so the
  raw-tuple seam emission cannot be derived from it row-locally (Risk #1).
- The seam fact is a BALANCE fact (exists_push_of_pull over SoundVmEnsemble), per
  the validated route — Channel.Guarantees := True deliberately carries nothing.

## Next step (XS-PR1 Step 2, separate later PR — DISRUPTIVE)

Build memSegVm : VmTables over componentWithSeamAndMemBus; migrate
fullRv64imEnsemble SoundEnsemble→SoundVmEnsemble + non-empty verifier; absorb the
Balance.lean re-proves (shifted channel list, prepended tables, non-empty
verifier); derive SeamColumnEquality from balance + the tag pins. The tag-pin
derivation from segment_every_row + boot saturation (Risk #3) and the
verifier-endpoint discharge (PLAN §7.5) are the Step-2 make-or-break.
