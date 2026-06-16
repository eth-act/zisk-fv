Active plan: docs/ai/plan/PLAN_ENDGAME_XCAP.md §4.B (XS-PR1 — cross-segment Mem seam).
Branch: xcap-seam-tag (off xcap-xseg / PR #104). Worktree: .worktrees/xcap-seam-tag.

## Current focus: XS-PR1 Step 2b (VM re-root migration) — VERIFIED BLOCKED.

VERDICT: BLOCKED at a framework-level wall (NOT a tactic gap, NOT a half-broken
foundation). The whole project stays GREEN and byte-identical for every canonical
theorem; only the additive `memSegVmFull` host was added.

What was done this increment (additive, green, kernel-only):
- `memSegVmFull : VmTables FGL SeamMessage` in SeamVm.lean — the REAL dual-bus VM
  host (hosts `Mem.componentWithSeamAndMemBus`: MemBus provider emit + seam
  pull/push from the SAME rows), NOT the seam-only projection. Sound, 0 PROJECT
  (ZiskFv.*) axioms (kernel-only).

The make-or-break (`addVm` re-root) resolved NO. Constructing the migrated
`SoundEnsemble FGL SeamMessage` skeleton (Mem out of base, OpBus+MemBus finished)
and attempting `skeleton.addVm memSegVmFull` produces three obligations; the third,
`reqs_disjoint_finished`, is PROVABLY FALSE. Verified residual goal:
  `∀ ch ∈ finished, ¬ch=SeamCont ∧ ¬ch=MemoryBus ∧ ¬ch=SeamCont`
and for `ch = MemBusChannel.toRaw ∈ finished` the middle conjunct
`¬MemBusChannel.toRaw = MemoryBus.toRaw` is false.

ROOT CAUSE (architectural): by `Operations.ChannelsLawful` a `MemBus.emit`
(assumeGuarantees=false) is classified into `channelsWithRequirements`, and
`addVm` (Vm.lean:688) forbids any FINISHED channel from appearing in a VM table's
`channelsWithRequirements`. This is mathematically essential — the VM-channel
soundness argument (`guarantees_of_requirements_append`) requires VM tables to
contribute no provider interactions to a finished channel. The Mem rows ARE the
MemBus providers, so MemBus cannot be finished WITHOUT them, yet the migration
moves exactly those rows into the VM. Contradiction. Leaving MemBus unfinished is
also dead (no soundness path: neither finished nor the VM channel). The
Clean/Air/OrderedChannel.lean:440-445 doc states this directly: a both-push-and-
pull (VM) channel "does not hold SoundChannels for ANY list of channels."

CONSEQUENCE: re-rooting onto the seam via the existing Clean `addVm` API is
impossible while MemBus stays finished/sound. Needs a framework change to
Clean/Air/Vm.lean (an `addVm` variant admitting VM tables that also PROVIDE an
already-finished channel; or a multi-channel VM hosting BOTH MemBus and seam).
`fullRv64imEnsemble`, Balance.lean, AcceptedTrace.lean, the 28 families: LEFT
BYTE-IDENTICAL — none re-proved, none can be (the migration never reaches them).

Gates: full lake build GREEN (8691 jobs). memSegVmFull + 5 prior SeamVm decls all
kernel-only [propext,Classical.choice,Quot.sound] = 0 PROJECT (ZiskFv.*) axioms;
global theorem + fullRv64imEnsemble + construction_add/sub_sound = 0 PROJECT
axioms (external Sail/kernel only). check-all.sh: all pass EXCEPT check 16 =
pre-existing FileNotFound on uninitialized zisk/ submodule (unrelated).
check-all-semantic.sh (V2): ALL PASS. Checks 4/7/8 floors byte-identical
(0 axioms / 63 equiv / hypothesis-count / caller-burden unchanged).

--- prior (Step 1) ---

## XS-PR1 Step 1 (structural seam-channel exposure) — DONE, green.

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
