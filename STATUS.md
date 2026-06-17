Active plan: docs/ai/plan/PLAN_ENDGAME_P4_103.md (#103 cross-segment memory seam, PATH 1 / addChannel).
Branch: p4-103-landing. Worktree: .worktrees/xcap-seam-tag.

## Current focus: L2 + L3 + L4 LANDED on the real production component — GREEN.

This increment landed the confirmed PATH-1 (addChannel) route on the production
Mem-with-both-buses component, non-vacuously, with 0 PROJECT axioms.

- L2 (ZiskFv/AirsClean/Mem/SeamCircuit.lean): componentWithSeamAndMemBus now emits
  the seam via SeamContChannel.emit — prev: emit (-1); last: emit (1 - is_last_segment)
  (the gated push). channelsWithGuarantees = [MemBus] only (seam OUT of guarantees,
  in requirements → escapes subset_finished). + is_last_segment column +
  componentWithSeamAndMemBus_interactionsWith_seam projection.

- L3 (ZiskFv/AirsClean/Mem/SeamEnsemble.lean): seamEnsemble = bootComp (verifier
  endpoint: boot push tag 0 + final pull tag tf) + two production
  componentWithSeamAndMemBus tables + addChannel SeamContChannel. Extraction:
  theList2_balanced_of_balancedChannels pulls the seam balance out of
  BalancedChannels (the addChannel conjunct). NON-VACUITY: good_balancedChannels
  PROVES the antecedent satisfiable on a concrete boot+2-segment MemSeamRow witness.

- L4 (same file): seam_value_equality discharges SeamTagChain.tag_chain_derived to
  force seg_n.segment_last_* = seg_{n+1}.previous_segment_* (honest permutation
  disjunction) on the real-component ensemble. good_seam_holds runs it non-vacuously.

- Tag-chain derivation moved out of Spike/ → ZiskFv/Channels/SeamTagChain.lean
  (production module; trust-gate check 13 wording fixed).

## Gates

- Whole-project `nix develop --command lake build`: GREEN (8692 jobs).
- 0 PROJECT axioms everywhere (seam = kernel-only; global theorem + equiv_ADD/MUL
  unchanged externs only — no ZiskFv.* axioms).
- V1 check-all.sh: ALL PASS except check 16 (Aeneas production boundary —
  PRE-EXISTING, uninitialized zisk submodule, missing zisk/core/src/aeneas_extract.rs).
- V2 check-all-semantic.sh: ALL PASS (63 canonical equiv_<OP> + global theorem
  axiom-closure baseline BYTE-IDENTICAL). hypothesis-count / caller-burden
  baselines byte-identical.

## Key design decision (faithfulness vs HARD constraint)

fullRv64imEnsemble is UNTOUCHED (Balance.lean's 11-way rcases + AcceptedTrace are
brittle to its table list; touching it breaks the 28 families). The seam lands on
a SEPARATE seamEnsemble built from the production seam component + boot endpoint.
The 28 families root on the untouched ensemble and do not consume the seam yet
(that is L5/#76). The 10 non-Mem provider tables of the real ensemble contribute
[] to the seam balance, so they add no seam-soundness content; embedding the seam
component into the full 11-table fullRv64imEnsemble for the #76 consumer is L5.

## Next steps (deferred, separate increments)

- L1: general-N tag-chain derivation (currently N=2 via theList2). The Newton
  power-sum chain forces {0..N-1} for any N; induction is the work.
- L5: hook the derived seam into the 11 loads/stores cross-entry obligations (#76,
  PLAN_ENDGAME_P4_MEMORY.md). Needs embedding the seam component + boot endpoint
  into fullRv64imEnsemble (Balance.lean rcases widening) OR a relation from
  seamEnsemble's seam to AcceptedTrace's Mem rows.
