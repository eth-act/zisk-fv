# PLAN — #103 cross-segment memory seam: LANDING (the confirmed `addChannel` route)

**Status:** route **CONFIRMED** (PATH 1 / `addChannel`, no Clean fork) — landing
**NOT done** (0 new merged opcodes yet). This plan captures the forward path AND
the dead-ends, so the long inquiry that produced it is not lost or re-walked.

**One-liner:** land the cross-segment memory seam (`SeamColumnEquality`:
`seg_n.segment_last_* = seg_{n+1}.previous_segment_*`) on the real
`fullRv64imEnsemble` via the `SoundEnsemble.addChannel` idiom, then consume it in
the 11 loads/stores (#76). No `addVm`, no Clean change.

---

## §0. Pointers (read these before touching anything)

- **The why / full inquiry record + ZisK bug analysis:**
  [`docs/ai/NOTE_103_MEMORY_CONTINUATION_SEAM.md`](../NOTE_103_MEMORY_CONTINUATION_SEAM.md)
  — has the RESOLUTION banner, the dead-end history (§4–6), the soundness
  argument, and §7's source-grounded ZisK-soundness audit.
- **The proofs (evidence branches, throwaway/not-for-merge):**
  - `seam-path1-evidence` → `ZiskFv/Spike/SeamNonVacuousProbe.lean` (the confirmed
    non-vacuous end-to-end PATH-1 instance) + `SeamVmTagChain.lean` (the tag-chain
    derivation).
  - `spike-tagchain-evidence` → `SeamVmTagChain.lean` (make-or-break tag-chain GO).
- **Structural exposure already done:** PR #104 on `xcap-xseg`
  (`ZiskFv/Channels/SegmentContinuation.lean` = `SeamContChannel`/`SeamMessage`;
  `ZiskFv/AirsClean/Mem/SeamCircuit.lean` = `MemSeamRow` + `componentWithSeamAndMemBus`).
- **External trail:** GitHub issue eth-act/zisk-fv#103 (comment chain).
- **Memory:** `project_p4_construction.md`.
- **SUPERSEDED:** `PLAN_ENDGAME_XCAP.md` — its `addVm`/`SoundVmEnsemble` route is
  DEAD (see §2). Do not execute it. Its cross-row (#100) framing is still useful
  as background but the *mechanism* it proposes is wrong.
- **Downstream consumer plan:** `PLAN_ENDGAME_P4_MEMORY.md` (#76 loads/stores).

---

## §1. The confirmed route (PATH 1) — what is true

The continuation channel must contribute its **balance** as an assumed antecedent
(same trust class as `trace.balanced`); from that balance the seam value-equality
is derived. The mechanism (all source-verified + compile-confirmed non-vacuously):

1. The seam-bearing Mem rows emit the continuation channel via
   **`SeamContChannel.emit (-1) prev` / `emit (1 - is_last_segment) last`**
   (the `emit` family → `assumeGuarantees := false` → `channelsWithRequirements`),
   keeping the component's `channelsWithGuarantees = []`. **Not `.pull`** (see §4
   gotcha).
2. Add the seam channel to the ensemble with **`SoundEnsemble.addChannel`**
   (`Clean/Air/OrderedChannel.lean:683`) — it joins `ens.channels` with **no
   soundness obligation**; its balance becomes a conjunct of `BalancedChannels`
   (`Clean/Air/FlatEnsemble.lean:336`).
3. Extract that balance (`witness.interactionsWith SeamContChannel.toRaw`) and feed
   it to the tag-chain derivation (`tag_chain_derived`, weighted-balance + Newton +
   `exists_push_of_pull`), which forces the per-tag value seam.

**Why sound, not laundering:** balance is the existing channel-balance trust class
(ZisK's global grand-product check genuinely provides it); nothing consumes the
seam channel's *guarantees* (`SeamContChannel.Guarantees := True`), only its
*balance*; and the NOTE §7 audit independently found ZisK's continuation sound
*given* that balance. No `addVm`, no Clean change, **Mem rows are not moved**, so
the MemBus provider/balance is untouched.

**Confirmed (do not re-litigate):** the mechanism compiles green, kernel-only
axioms, on a **non-vacuous** boot+2-segment instance with the **real**
`SeamContChannel`/`SeamMessage`, adversarially verified (reviewer independently
proved the balance antecedent inhabited + the seam boundary genuinely
cross-segment). Evidence: `seam-path1-evidence:SeamNonVacuousProbe.lean`.

---

## §2. DEAD ENDS — do NOT retry (this is the expensive part of the lesson)

| Route | Why it is dead | Source anchor |
|---|---|---|
| **`addVm`** (continuation as a VM channel) | doubly blocked: (1) `reqs_disjoint_finished` (`Vm.lean:688`) forbids a VM table from *requiring* a finished channel, and the Mem rows push (=require) the finished MemBus; (2) even relaxed, moving the MemBus *provider* into the VM falsifies `PartialBalancedChannel witness' MemBus` (MemBus unbalanced over the old tables). | `Vm.lean:688`; `OrderedChannel.lean:378-388` |
| **Fork Clean to generalize `addVm`** | the "minimal" disjunctive-precondition patch is *insufficient* (the provider-in-VM balance premise above is a different, deeper obligation); the real change is substantial metatheory — and **unnecessary**, because `addChannel` already does the job. | implementation BLOCKED, see NOTE §4 |
| **Make the continuation a *finished* channel** (incl. producer/consumer split) | it is a both-push-and-pull *chain*; `OrderedChannel.lean:440-445` — "does not hold `SoundChannels` for ANY list"; splitting tags doesn't help (obstruction is per-channel). | `OrderedChannel.lean:440-445` |
| **A new `AcceptedTrace.continuation_balanced` field** | works but strictly dominated by `addChannel` (adds a record field / caller-burden, reads as a bespoke promise; `addChannel` gets the balance for free via `BalancedChannels`). | — |

If a future attempt is tempted by any of these, the answer is already known: use
`addChannel` + `emit` (§1).

---

## §3. Landing checklist (the forward path)

Confidence tags: **[mechanical]** known-shape, **[proof]** real proof work,
**[integration-risk]** untested at production scale.

- [x] **L1 — General-N tag-chain derivation.** **DONE** (commits `c720503f`,
  `e6d5e05e`, `9eb8c912` on `p4-103-landing`). Generalized the boot tag-chain from
  N=2 (`boot_chain_derived`) to ARBITRARY N in `ZiskFv/Channels/SeamTagChain.lean`
  (channel-level file only; ensemble/families/global UNTOUCHED, byte-identical).
  - `bootChainN N boot prev last t` = boot push (tag 0) + N segments (each
    `pull(t_i)` + `push(t_i+1)` gated, last gated off), built via `List.range`
    flatMap. `bootChainN_seam`: for ALL N, every segment `i<N` has `prev_i = boot`
    (`t_i=0`) OR `prev_i = last_j` for a non-last `j` with `t_i = t_j+1` (THE SEAM).
    Proof = `exists_push_of_pull` + push-message classification + `SeamVal.msg_inj`
    (a DIRECT telescoping, not full Newton). `bootChainN_last_tag`: `t (N-1) = N-1`
    for all N≥1 via weighted-balance telescoping (`weightedSum_bootChainN` +
    `sum_segGate`). `boot_chain_derived_generalN` = the headline `∀ N≥1` analogue of
    `boot_chain_derived`, bundling the seam (every i) + last-tag.
  - NON-VACUITY: `goodBootChain3` (concrete BALANCED N=3 chain) + `goodBootChain3_seams`
    runs the seam on all 3 segments; `goodBootChain3_last_tag` runs the tag arithmetic.
  - HONEST FINDING: the seam is tag-INDEXED (permutation-tolerant). Per-PHYSICAL-index
    order ("seg i+1 follows seg i") is NOT forced by balance alone for N≥3 (the
    balanced witness `t=(1,0,2)` at N=3 shows it); the value continuation IS forced
    for all N. Collapsing the permutation needs the `is_first_segment` row pin (L5).
  - REMAINING (optional strengthening, NOT load-bearing for #76): the full
    tag-multiset = `{0,…,N-1}` (the SET) via Newton/symmetric-function inversion.
    The value seam + last-tag (what #76 consumes) are proved for ALL N.
  - Whole project GREEN (8691), 0 PROJECT axioms (kernel-only on all new decls),
    V1 17/17 substantive pass + V2 ALL PASS (check 16 = uninitialized zisk/ submodule,
    pre-existing/environmental).
- [x] **L2 — Production seam component.** **DONE** (commit `c3643041`).
  `componentWithSeamAndMemBus` (`Mem/SeamCircuit.lean`) now emits the seam via
  `SeamContChannel.emit` — prev `emit (-1)`, last `emit (1 - is_last_segment)` (the
  gated push). `channelsWithGuarantees = [MemBus]` only (seam in requirements →
  escapes `subset_finished`). Added the `is_last_segment` column and the
  `componentWithSeamAndMemBus_interactionsWith_seam` projection. Builds green, 0
  PROJECT axioms. (The `segment_every_row`-style local pin tying `segment_last_*`
  to actual Mem rows is the L5 concern, not needed for the balance seam.)
- [x] **L3 — Wire into a real-component ensemble (additive, not in-place).** **DONE**
  (commits `28a78816`, `4d5af9bd`). Decision: `fullRv64imEnsemble` is UNTOUCHED —
  `Balance.lean`'s 11-way `rcases` + `AcceptedTrace` are brittle to its table list;
  swapping the Mem slot there breaks the 28 families. Instead built a SEPARATE
  `seamEnsemble` (`Mem/SeamEnsemble.lean`) = `bootComp` (verifier endpoint) + two
  production `componentWithSeamAndMemBus` tables + `.addChannel SeamContChannel`.
  It composes at production scale (the `MemSeamRow` `interactionsWith`/`channelsLawful`
  cost was tractable). NON-VACUITY proven: `good_balancedChannels` exhibits a
  concrete boot+2-segment `MemSeamRow` witness whose seam balance holds. The 10
  non-Mem provider tables of the real ensemble contribute `[]` to the seam balance,
  so embedding into the full 11-table ensemble (for #76) is deferred to L5.
- [x] **L4 — Connect balance → seam on the real-component ensemble.** **DONE**
  (commit `4d5af9bd`). `mkWitness_interactionsWith` reduces the witness's seam
  interactions to the 6-element boot+2-segment list; `balanceOf` is channel-blind
  so it projects onto `SeamTagChain.theList2`; `theList2_balanced_of_balancedChannels`
  extracts the seam balance from `BalancedChannels` (the `addChannel` conjunct);
  `seam_value_equality` discharges `tag_chain_derived` to obtain
  `seg_n.segment_last_* = seg_{n+1}.previous_segment_*` (honest permutation
  disjunction). `good_seam_holds` runs it non-vacuously. **N=2 only** — general N
  is L1, deferred cleanly. (Tag-chain derivation now lives at
  `ZiskFv/Channels/SeamTagChain.lean`, moved out of `Spike/` for trust-gate check 13.)
- [B] **L4.5 — REAL-ensemble integration (in-place swap).** **BLOCKED** (verified
  by build 2026-06-17, not by analysis). The naive in-place swap (`addTable`
  `componentWithSeamAndMemBus` in the Mem slot + `.addChannel SeamContChannel`) is
  ADDITIVE for the ensemble itself and the 28 construction families, BUT breaks the
  GLOBAL theorem. The hypothesis "the 28 families don't reference Mem → only
  `Balance.lean` infra changes" is HALF right: the 28 `Construction*.lean` families
  reference only Main machinery (`mainOfTable` / `rowAt_mainOfTable` / `*_from_binding`),
  so they stay clean. The break is NOT a family — it is the GLOBAL theorem's load/store
  dispatch (`Compliance.lean` → `Dispatch/LDSD` → `Compliance/OpEnvelope` →
  `ZiskCircuit/MemTimeline/Construction` → `Balance.lean` Mem replay machinery). That
  machinery (145 `componentWithDualMemBus` refs; `MemTableGeneratedRowsBridge.component`
  pins `table.component = componentWithDualMemBus` and projects its `MemRow`
  `rowInputVar`) becomes UNSATISFIABLE for the real ensemble once the Mem table is the
  seam component, AND the seam component's per-row `Spec := True` provides none of the
  Mem value/addr/ordering facts the load/store path needs (vs
  `spec_of_componentWithDualMemBus_spec` = the real `Mem.Spec`). So the swap is a
  whole-project build break, not a Balance-infra widening.
  **FALLBACK (the real forward path):** route (b) — UNIFY the seam into
  `componentWithDualMemBus` / `MemRow` itself (extend `MemRow` + `memWithDualMemBus`
  with the 9 segment columns + the seam `emit`, so one component on one row type carries
  BOTH the real Mem `Spec` AND the seam). This keeps every `MemRow`-typed Mem-timeline
  lemma applicable while adding the seam in-place. It is a larger refactor of
  `Mem/Constraints.lean` + the 145 `Balance.lean` refs (mechanical: `MemRow` →
  unified row, `componentWithDualMemBus` → unified component), NOT the additive swap
  L4.5 assumed. Route (a) — a SEPARATE seam-bearing Mem table alongside the DualMemBus
  table — is also viable but adds a redundant Mem table to the trace skeleton. The
  scaffold-bridge fallback (relate `seamEnsemble`'s seam to `AcceptedTrace`'s Mem rows)
  remains available but does not put the seam on the real ensemble.
- [x] **L4.5-routeB — RESOLVED via route (b).** **DONE** (commits `aa09babf`,
  `b21cb1ba`, `6a7ad798`; pushed; adversarially verified). The in-place SWAP was
  BLOCKED (record above), but route (b) — folding the seam INTO the real
  `componentWithDualMemBus`/`MemRow` — succeeded: `MemRow` extended +10 segment
  columns (real `Mem.Spec` over the 13 base cols INTACT, NOT weakened), seam emitted
  via `emit` from `memWithDualMemBus`, `.addChannel SeamContChannel` on
  `fullRv64imEnsemble`. Propagation was SMALL (the `Valid_Mem := fun _ => 0` default
  trick → ~8 files; `MemTimeline/Construction` + the 7 loads UNCHANGED). 28 families +
  global theorem BYTE-IDENTICAL, whole project green (8689), 0 PROJECT axioms. Scaffold
  (`SeamCircuit`/`SeamEnsemble`) deleted; `SeamTagChain.lean` kept.
  `AcceptedTrace.seam_balanced` extracts the seam balance from `trace.balanced`.
- [x] **L4.6 — BOOT ENDPOINT (NON-VACUITY, surfaced by route b). DONE**
  (commits `fdd9e288`, `f5b6ecfe`). Route (b) put the seam in `AcceptedTrace`'s
  `BalancedChannels`; the Mem rows emit `pull(tag=segment_id)` / gated
  `push(tag=segment_id+1)` but no table emitted the tag-0 boot push, so the chain
  dangled for nonzero multi-segment Mem traces (latent vacuity).
  **CONFIRMED balance structure:** with `segment_id = 0..N-1` and the last segment
  `is_last_segment = 1` (push gated OFF), a single tag-0 boot push (mult +1)
  telescopes the chain to zero — **NO separate final pull needed** (the
  `is_last` gate closes the high end, unlike the deleted scaffold `bootComp` whose
  two segments were both non-last). The gating also forces the tags UNIQUELY
  (`t0=0, t1=1`), no permutation disjunction.
  **FIX (route a — boot table):** `Mem.bootComp` (a tiny
  `GeneralFormalCircuit`-backed `Component`) emits the single tag-0 boot push via
  `emit` (requirements bucket; seam OUT of guarantees); added to
  `fullRv64imEnsemble` via `.addTable`. `Balance.lean`'s 11-way enumeration widened
  to 12. The analogue of ZisK's `mem.pil:253 direct_global_update_proves`.
  **NON-VACUITY PROVEN** (`FullEnsemble/SeamNonVacuity.lean`): a concrete
  `EnsembleWitness` over the REAL `fullRv64imEnsemble` with 2 NONZERO Mem segments
  + boot, whose seam channel BALANCES (`good_seam_balancedChannel`) and lands the
  cross-segment value seam (`good_seam_holds`,
  `seg1.previous_segment_* = seg0.segment_last_*`). Surfaced as
  `AcceptedTrace.seam_conjunct_satisfiable`. All kernel-only, 0 PROJECT axioms;
  28 families + global + all 6 protected baselines BYTE-IDENTICAL; whole project
  green; V1 17/17 substantive + V2 ALL PASS.
- [~] **L5 — #76 consumption.** **[proof]** Once L4.5/L4.6 put the seam (balanced &
  satisfiable) on the real ensemble and L1 gives general N, hook the derived
  `seg.previous_* = prev_seg.last_*` into the per-opcode Mem cross-entry
  obligations the 11 loads/stores actually consume (see `PLAN_ENDGAME_P4_MEMORY.md`;
  the intra-segment load machinery `LoadDerivation.lean`/`SextLoadBridge.lean`/
  `MemAlignBridge.lean` already exists — #103 supplies only the cross-segment link).
  - [!] **L5 step 1 — the TIE.** **CORRECTION 2026-06-17: the "DONE" below is
    OVERSTATED.** The work is on DANGLING commit `362c6e83`, NOT an ancestor of
    `origin/p4-103-landing` (head `cac77248`) — recover it before GC. And the tie as
    written is row-local, validated only by the one-row witnesses, so it is a
    deliverable of the #103 DEEP refactor (= #76 PR-76.5 / XCAP track 103), not a
    banked result. See `../research/RESEARCH_XCAP.md`. Historical claim follows:
    **DONE** (commit `362c6e83` on `p4-103-landing`). New file
    `ZiskFv/AirsClean/Mem/SeamRowTie.lean`. `MemRow.SegmentLastRowTie` = the
    row-local SEGMENT_LAST tie (`mem.pil:212-230`, SEGMENT_LAST=1 on a segment's
    last row), pinning `segment_last_value/addr/step` to the row's genuine memory
    state (`mem.pil:215/220/226`); CONSTRUCTIBLE (exactly the PIL clauses, not
    stronger — `good_seg0_tie`/`good_seg1_tie` confirm the existing non-vacuity
    witnesses still satisfy it). `cross_segment_real_memory_continuity` composes
    the balance-derived seam (`SeamNonVacuity.seam_value_equality`) with the tie
    to give `seg1.previous_segment_* = seg0`'s REAL last Mem-row state
    (`value/addr/effectiveStep`), tagged — the genuine cross-segment continuation
    #76 needs, no free emission column dangling. NON-VACUOUS end-to-end
    (`good_cross_segment_continuity` on the real 2-nonzero-segment witness).
    Whole project GREEN (8692), 0 PROJECT axioms (kernel-only on all 5 new
    decls), V1 17/18 substantive + V2 ALL PASS; 28 families + global + all
    protected baselines BYTE-IDENTICAL (only `ZiskFv.lean` + the new file).
  - [ ] **L5 step 2 — loads/stores consumption (part A).** Feed
    `cross_segment_real_memory_continuity` into the 11 loads/stores' per-opcode
    cross-entry Mem obligations (`PLAN_ENDGAME_P4_MEMORY.md`).

**Anti-laundering / acceptance:** every landed piece must keep 0 PROJECT axioms,
the 63-theorem + hypothesis-count + caller-burden baselines byte-identical, and be
**non-vacuous** (the seam-balance antecedent must be exhibited satisfiable, not a
degenerate single-row instance — that was the trap the first probe fell into).

---

## §4. Key facts / gotchas (the convention that bit us)

- **`pull` vs `emit` bucket:** `pull` → `mult -1`, `assumeGuarantees=true` →
  `channelsWithGuarantees`. `push`/`emit` → `assumeGuarantees=false` →
  `channelsWithRequirements`. (`Operations.lean:1084/1087`, `Channel.lean`.)
- **`subset_finished` trap:** `SoundEnsemble.subset_finished` forces
  `channelsWithGuarantees ⊆ finished`. So a channel you do NOT want finished must
  be emitted via `emit` (requirements), never `pull` — else it's dragged into
  `finished` and you must prove a soundness it can't have.
- **Faithful emission:** `direct_gsum_0` pull tag = `segment_id`; `direct_gsum_1`
  push tag = `segment_id + 1`, gated `(1 - is_last_segment)`; one global boot push
  tag 0 (`direct_global_update_proves`, mem.pil:253). `Airs/Mem.lean:1351-1370`.
- **The four builders:** `addTable` / `addFinishedChannel` / **`addChannel`** /
  `addVm`. (Now also documented in Clean's `AGENTS.md` — the refinement this
  inquiry produced.)

---

## §5. The #100 bonus (HYPOTHESIS — verify, don't assume)

The cross-**row** PC handshake (#100, for branches + JAL/JALR) is the *same*
both-push-and-pull chain shape (Main pushes next-pc, pulls prev-pc). So the
`addChannel` idiom **very likely** unblocks #100 too — which would cover branches
(6) + JAL/JALR (2). **Not verified.** A cheap check: does Main's PC handshake have
the same structure, and does `addChannel` + the tag-chain (or a pc+4 analogue)
carry it? If yes, one idiom unblocks ~19 of the 35 remaining opcodes (11 loads/
stores + 6 branches + 2 JAL/JALR).

---

## §6. Discipline notes (so the meta-lesson survives)

This inquiry produced **four overclaims**, each refuted one layer deeper by an
actual build/adversarial check: (1) "route fully de-risked end-to-end"; (2) the
fork design "SOUND-AND-MINIMAL ready to implement"; (3) the first probe
"PATH-CONFIRMED" (it was VACUOUS); only (4) the non-vacuous probe + adversarial
inhabitation proof was trustworthy. For this kind of framework-integration work:

- **Trust compiling, non-vacuous code over design analysis.** End investigations in
  a compile probe, not an argument.
- **Check whether the framework ALREADY supports it** (enumerate the full API)
  before assuming a fork is needed. The breakthrough came from exactly this.
- **Guard non-vacuity explicitly** — a green `Statement → …` theorem is worthless if
  `Statement` is unsatisfiable.
- Keep delegating with the **adversarial verify** phase; it caught every overclaim.
