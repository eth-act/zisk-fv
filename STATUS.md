Active plan: docs/ai/plan/PLAN_ENDGAME_P4_103.md (#103 cross-segment memory seam, route (b)).
Branch: p4-103-landing. Worktree: .worktrees/xcap-seam-tag.

## Current focus: ROUTE (b) LANDED on the real fullRv64imEnsemble — GREEN.

The seam is now UNIFIED into the real Mem component (route b, the L4.5 fallback),
so the load/store Mem-timeline machinery (keyed on componentWithDualMemBus / MemRow
/ real Mem.Spec) keeps applying. Whole project GREEN, 0 PROJECT axioms, all
protected baselines/families/Equivalence BYTE-IDENTICAL.

## What landed (3 green commits)

- Stage 1+2 (commit aa09babf): unify the seam into componentWithDualMemBus/MemRow.
  - MemRow + 9 segment columns + is_last_segment (13 base columns untouched →
    real per-row Mem.Spec preserved verbatim).
  - memWithDualMemBus: two MemBus emits BYTE-IDENTICAL; ALSO emits the seam via
    emit(-1) prev / emit(1-is_last) last (requirements bucket; seam OUT of
    channelsWithGuarantees). New projection componentWithDualMemBus_interactionsWith_seam.
  - Valid_Mem + 10 segment per-row columns with `:= fun _ => 0` DEFAULTS (so every
    existing Valid_Mem literal/proof is untouched); rowAt/memOfTable thread them so
    rowAt_memOfTable stays a faithful full-row equality (the bridge rowAt_eq the
    load/store timeline consumes). Segment cols are NOT in Spec nor the MemBus
    message → timeline path unaffected.
  - Obsolete SEPARATE scaffold deleted: Mem/SeamCircuit.lean + Mem/SeamEnsemble.lean.
    KEPT the reusable channel-level derivation Channels/SeamTagChain.lean.
- Stage 3 (commit b21cb1ba): seam on the REAL ensemble.
  - FullEnsemble.lean: .addChannel SeamContChannel.toRaw (no soundness obligation;
    its balance becomes a BalancedChannels conjunct).
  - Balance.lean: seam_balanced_of_witness (BalancedChannels → seam
    BalancedInteractions on the real ensemble).
  - AcceptedTrace.lean: AcceptedTrace.seam_balanced — seam BALANCED on EVERY
    accepted trace, from the trace's existing `balanced` field, NO extra hypothesis.
    Non-vacuous: quantifies over AcceptedTrace (the structure the proved global
    theorem consumes).

## Gates

- Whole-project nix develop --command lake build: GREEN (8689 jobs).
- 0 PROJECT (ZiskFv.*) axioms; fullRv64imEnsemble + both new seam theorems are
  kernel-only (propext/Classical.choice/Quot.sound).
- 28 construction families + 63 canonical equiv_<OP> + all 4 trust baselines
  BYTE-IDENTICAL (md5 + git diff --stat empty; V2 axiom-dep/binder match).
- V2 semantic gate: ALL PASS. V1 syntactic: 17/17 substantive pass (check 16
  Aeneas boundary = PRE-EXISTING uninitialized-submodule FileNotFoundError,
  unrelated).

## Remaining (next concrete step)

The full N-segment cross-segment VALUE-seam derivation (SeamTagChain.tag_chain_derived
against the ensemble balance) needs the boot/end seam ENDPOINT also emitted into
fullRv64imEnsemble: as wired, Mem rows emit pull(tag=segment_id)/gated-push(
tag=segment_id+1) but NO table emits the tag-0 boot push (mem.pil:253
direct_global_update), so a NONZERO multi-segment seam chain only balances once the
verifier endpoint is hosted on the seam channel. That endpoint + the general-N tag
chain = L1; the #76 load/store consumption = L5.
