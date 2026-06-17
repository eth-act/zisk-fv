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

## L4.5 (in-place real-ensemble integration): BLOCKED — verdict recorded 2026-06-17

Attempted the in-place swap (componentWithDualMemBus → componentWithSeamAndMemBus
+ .addChannel SeamContChannel) in fullRv64imEnsemble and built. RESULT: the swap
does NOT stay confined to Balance.lean enumeration infra — it breaks the Mem
timeline machinery that the GLOBAL theorem's load/store dispatch transitively
consumes. Root cause (structurally proven, not an overclaim):

1. The seam component is built on a DIFFERENT row type (MemSeamRow, 22 fields) than
   componentWithDualMemBus (MemRow, 13 fields), and its per-row Spec is TRIVIAL
   (`Spec _ _ _ := True`, SeamCircuit.lean:191).
2. Balance.lean has 145 references to componentWithDualMemBus, most in the deep Mem
   replay/timeline machinery (memOfTable / MemTableGeneratedRowsBridge / memReplay /
   memoryTimelineEvidence, lines ~3195-end). MemTableGeneratedRowsBridge.component
   REQUIRES `table.component = componentWithDualMemBus` and rowAt_eq projects
   componentWithDualMemBus.rowInputVar (a MemRow). After the swap the ensemble's Mem
   table component is the seam component, so this bridge is UNSATISFIABLE for the real
   ensemble.
3. Dependency chain confirmed: Compliance.lean (global theorem) → Dispatch/LDSD →
   Compliance/OpEnvelope → ZiskCircuit/MemTimeline/Construction (references
   componentWithDualMemBus.rowInputVar + MemReplayRowsEmbeddedInTrace directly) →
   Balance.lean Mem machinery. The load/store path needs the Mem per-row Spec
   (value/addr/ordering) that componentWithDualMemBus provides via
   spec_of_componentWithDualMemBus_spec; the seam component's trivial Spec provides
   NONE of it, so the path becomes unprovable, not merely mechanically different.

NOT a construction-family break: the 28 ALU/shift/W-ALU construction families
(Construction*.lean) reference ONLY Main machinery (mainOfTable, rowAt_mainOfTable,
*_from_binding) — verified — so they stay clean. The break is in the GLOBAL theorem's
load/store dispatch via the Mem timeline. Acceptance ("whole project builds, global
theorem green") cannot be met by the in-place swap as designed.

Tree fully reverted to the L4 green baseline (8278 jobs GREEN). No partial swap left.

FALLBACK (the plan's named alternative): keep fullRv64imEnsemble's Mem table as
componentWithDualMemBus and supply the seam by a DIFFERENT mechanism — either
(a) add a SEPARATE seam-bearing Mem table alongside (not replacing) the DualMemBus
table, OR (b) extend MemRow / componentWithDualMemBus itself to carry the 9 segment
columns + emit the seam (so MemSeamRow and componentWithDualMemBus unify into one
component on one row type with the REAL Mem Spec). (b) is the only route that keeps
the Mem timeline machinery AND adds the seam in-place; it is a larger refactor of
Mem/Constraints.lean + the 145 Balance.lean refs, not the additive swap L4.5 assumed.

## Next steps (deferred, separate increments)

- L1: general-N tag-chain derivation (currently N=2 via theList2). The Newton
  power-sum chain forces {0..N-1} for any N; induction is the work.
- L5: hook the derived seam into the 11 loads/stores cross-entry obligations (#76,
  PLAN_ENDGAME_P4_MEMORY.md). Now gated on resolving L4.5's block via fallback (b)
  (unify the seam into componentWithDualMemBus/MemRow) OR a proven relation from
  seamEnsemble's seam to AcceptedTrace's Mem rows.
