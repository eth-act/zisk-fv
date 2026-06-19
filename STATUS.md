Active plan: docs/ai/plan/PLAN_ENDGAME_P4_MEMORY.md (#76 PR-76.5) +
docs/ai/research/RESEARCH_XCAP.md §3 (#103 deep refactor B→A→C→D…).
Branch: p76-memory. Worktree: .worktrees/p76-memory.

## Current focus: PR-76.5 STEP D (seg_last-gated REAL Mem AIR) — DONE, GREEN. GO.

STEP D landed the `seg_last` (SEGMENT_LAST) selector into the REAL `MemRow`,
gated the `memWithDualMemBus` seam emission by it (one live pull/push per
segment + k-1 dead rows), rippled the new column through the full
componentWithDualMemBus/MemRow/rowAt/memOfTable blast radius, and re-proved a
k≥2 (2-rows-per-segment) cross-segment seam from balance on a REAL multi-row
`mkTable` witness. Whole project GREEN (8692). 0 PROJECT axioms (kernel-only).
V2 semantic gate ALL PASS; V1 substantive all pass (only pre-existing check-13
"spike"-wording hit on the parent's committed Spike file remains, untouched).

GO/NO-GO: **GO**. (a) the seg_last-gated REAL Mem AIR compiles across the full
blast radius (no #103-L4.5 dispatch break); (b) the k≥2 cross-segment seam
(`multiRow_seam_value_equality` / `good_multiRow_seam_holds`) is derived from
balance on a real 4-row Mem trace (2 segments × [dead, live]), dead rows
balance-inert. Remaining for E/F/G: airval↔column bridge
(MemTimeline/Construction/Linkage), SegmentLastRowTie from the segment Spec (not
h_tie), and the #76 `initialAgreement` wiring.

## (Superseded) Prior focus: #103 L5 STEP 1 (the "tie", step B) — DONE, GREEN.

The seam boundary columns are now TIED to real Mem-row state. The L1 seam forced
seg_{i+1}.previous_segment_* = seg_i.segment_last_* on the CHANNEL/emission
columns; this step pins those columns to actual Mem-row memory via mem.pil's
SEGMENT_LAST clauses, and derives the cross-segment REAL-memory continuity #76
needs. New file ZiskFv/AirsClean/Mem/SeamRowTie.lean (+ one import line in
ZiskFv.lean); families/global/baselines BYTE-IDENTICAL. Whole project GREEN (8692).

## What landed for L5 step 1 (commit 362c6e83)

- MemRow.SegmentLastRowTie: the row-local SEGMENT_LAST tie (mem.pil:212-230,
  SEGMENT_LAST=1 on a segment's last row). Pins segment_last_value/addr/step to
  the row's genuine memory state (mem.pil:215/220/226). Constructible — exactly
  the PIL clauses, NOT stronger.
- segment_last_seam5_eq_row_state_of_tie: the tie as a seam5 tuple equality
  (segment_last_* boundary = (value_0,value_1,addr,effectiveStep), same tag).
- cross_segment_real_memory_continuity (THE PAYOFF): composes the
  balance-derived seam (SeamNonVacuity.seam_value_equality:
  seg1.previous_segment_* = seg0.segment_last_*) with the SEGMENT_LAST tie on
  seg0 to give seg1.previous_segment_* = seg0's REAL last Mem-row state
  (value/addr/effectiveStep), tagged. No free emission column dangles.
- good_seg0_tie / good_seg1_tie: the existing non-vacuity witnesses goodSeg0 /
  goodSeg1 STILL satisfy the strengthened tie (segment_last_* = row's
  value/addr/step; sel_dual=0).
- good_cross_segment_continuity: NON-VACUITY end-to-end on the REAL ensemble —
  run on the concrete balanced 2-nonzero-segment witness; seg1's incoming
  boundary = seg0's real last state (1,0,100,5).

## Gates

- Whole-project nix develop --command lake build: GREEN (8692 jobs; +1 = the new
  SeamRowTie module).
- All 5 new theorems kernel-only (propext/Classical.choice/Quot.sound); 0 PROJECT
  axioms; NO sorry/admit/native_decide.
- 28 construction families + global theorem + all protected baselines
  (hypothesis-count, caller-burden, equiv-axiom-deps, axioms,
  zisk-riscv-compliant) BYTE-IDENTICAL (git status: only ZiskFv.lean +
  SeamRowTie.lean changed).
- V1 syntactic: 17/18 substantive pass (check 16 = uninitialized zisk/ submodule
  FileNotFoundError on zisk/core/src/aeneas_extract.rs, pre-existing, unrelated —
  needs nix run .#populate). V2 semantic: ALL PASS.

## Remaining (L1 follow-up + L5 step 2)

- L5 step 2 (the 11 loads/stores consumption, part A): feed
  cross_segment_real_memory_continuity (seg.previous = prev_seg's real last
  Mem-row state) into the per-opcode cross-entry Mem obligations the 11
  loads/stores consume (PLAN_ENDGAME_P4_MEMORY.md). The intra-segment load
  machinery (LoadDerivation / SextLoadBridge / MemAlignBridge) already exists;
  L5 step 1 now supplies the cross-segment link as a REAL-memory equation.
- L1 follow-up (optional strengthening): full tag-multiset = {0..N-1} (the SET)
  via Newton inversion, + the is_first_segment row pin to collapse the
  permutation to physical order. Value seam (load-bearing) already done.
