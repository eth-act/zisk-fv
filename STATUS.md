Active plan: docs/ai/plan/PLAN_ENDGAME_P4_103.md (#103 cross-segment memory seam, route (b)).
Branch: p4-103-landing. Worktree: .worktrees/xcap-seam-tag.

## Current focus: L1 GENERAL-N TAG-CHAIN DERIVATION — DONE, GREEN.

The seam tag-chain derivation is generalized from N=2 to ARBITRARY segment count
N, in ZiskFv/Channels/SeamTagChain.lean (channel-level lemma file; ensemble /
families / global UNTOUCHED). Whole project GREEN (8691), 0 PROJECT axioms; only
SeamTagChain.lean changed (460 additions, 0 deletions vs the L4.6 commit).

## What landed for L1 (3 green commits)

- c720503f (per-segment seam): bootChainN (boot push tag 0 + N segments, each
  pull(t_i)+gated push(t_i+1), last gated off) + bootChainN_seam: for ALL N, every
  segment i<N has prev_i = boot (t_i=0) OR prev_i = last_j for a non-last j with
  t_i=t_j+1 (THE SEAM). Proof = exists_push_of_pull + push classification +
  SeamVal.msg_inj. Tag-indexed (permutation-tolerant); honest finding: per-PHYSICAL
  -index order is NOT forced for N>=3 (the balanced witness t=(1,0,2) at N=3 shows
  it), which needs the is_first_segment row pin (the documented L5 follow-up).
- e6d5e05e (N=3 non-vacuity): goodBootChain3 = concrete BALANCED N=3 chain;
  goodBootChain3_seams runs bootChainN_seam on all 3 segments (seam fires each).
- 9eb8c912 (tag arithmetic + headline): weightedSum_bootChainN (Finset.range form)
  + sum_segGate telescoping → bootChainN_last_tag (t (N-1) = N-1 for all N>=1).
  boot_chain_derived_generalN = the headline analogue of boot_chain_derived (N=2):
  for all N>=1, (1) per-segment value seam for every i AND (2) t (N-1) = N-1.

Approach: DIRECT telescoping (exists_push_of_pull + classification) for the seam;
weighted-balance telescoping for the last tag. NOT full Newton. The FULL
tag-multiset = {0..N-1} (only the SET, since the assignment permutes for N>=3) needs
symmetric-function / Newton inversion and is the documented bounded follow-up; the
value seam (the #76 deliverable) and the last-tag are proved for ALL N.

## Gates

- Whole-project nix develop --command lake build: GREEN (8691 jobs).
- All new theorems kernel-only (propext/Classical.choice/Quot.sound); 0 PROJECT
  axioms; NO sorry/admit/native_decide.
- 28 construction families + global theorem + all protected baselines BYTE-IDENTICAL
  (git diff d986ca03 HEAD: only ZiskFv/Channels/SeamTagChain.lean changed).
- V1 syntactic: 17/17 substantive pass (check 16 = uninitialized zisk/ submodule
  FileNotFoundError on zisk/core/src/aeneas_extract.rs, pre-existing, unrelated —
  needs nix run .#populate; my change never touches the submodule). V2 semantic:
  ALL PASS (per-theorem axiom-closure baselines byte-identical).

## Remaining (L1 follow-up + L5)

- L1 follow-up (optional strengthening): the full tag-multiset = {0..N-1} (the SET)
  via Newton/symmetric-function inversion, and the is_first_segment row pin to
  collapse the permutation to physical order. The value seam (load-bearing) is done.
- L5 (#76 consumption): hook the derived seg.previous_* = prev_seg.last_* (now
  bootChainN_seam / boot_chain_derived_generalN, general N) into the 11 loads/stores'
  cross-entry Mem obligations (PLAN_ENDGAME_P4_MEMORY.md). The intra-segment load
  machinery already exists; #103 supplies the cross-segment link.
