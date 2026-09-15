# PLAN — XCAP: the cross-X ensemble capability (cross-row #100 + cross-segment #103)

> # ⛔⛔ #100 TRACK = FAITHFULNESS DEAD END (2026-06-17, PIL-verified)
> The per-row `PcContChannel` route for #100 (X100.0 PoC → X100.1 wiring → X100.1b pins →
> X100.1a seam → the Gap-C/PR-X100.1c discharge) is a **fabricated channel** — ZisK has NO
> per-row `pc`-tagged bus. Within-segment PC is a per-row POLYNOMIAL constraint
> (`main.pil:410`, the existing `pc_handshake`); cross-segment PC is a `direct_update` AIRVAL
> bus (`main.pil:501-529`). So **#100 ≠ #103**: #103's cross-SEGMENT carry IS a bus (addChannel
> faithful, capability real); #100's cross-ROW within-segment PC is a CONSTRAINT (addChannel
> type-illegal/fabricated). The "ADDCHANNEL for #100 confirmed" probe verdict missed the PIL
> check. The #100 commits on `xcap-gapc` (7b62d4d0/cb2a677f/4d0fad1d) are sound Lean over a
> non-existent channel — KEEP as dead-end evidence, do NOT pursue. **Genuine #100 path = route
> A:** get the per-row `pc_handshake` constraint (`main.pil:410`) into the live single-row
> Clean component — the ORIGINAL cross-row obstruction (single-row component can't state a
> row↔row-1 constraint). That is a different, deep workstream. Evidence:
> [`../research/RESEARCH_GAP_C.md`](../research/RESEARCH_GAP_C.md) top banner. The #103
> (cross-segment) track below is UNAFFECTED.

**Slug:** `Endgame XCAP` · **Issues:** #100 (cross-row PC), #103 (cross-segment Mem),
#101 (Binary-EQ, parallel) · **Rewritten:** 2026-06-17 (supersedes the 607-line
`PLAN_ENDGAME_XCAP.archive-2026-06-16.md`, whose `addVm`/`SoundVmEnsemble` build is a
confirmed dead end). **Status:** planned; #103 capability banked, #100 route confirmed,
neither production-wired.

Navigable spine. Depth: [`../research/RESEARCH_XCAP.md`](../research/RESEARCH_XCAP.md) +
[`../research/RESEARCH_76_GAP_MAPS.md#seam103`](../research/RESEARCH_76_GAP_MAPS.md) +
`PLAN_ENDGAME_P4_103.md` (the #103 landing checklist + the full dead-end table). Raw:
`../research/_raw/xcap-scope.json`.

## TL;DR

XCAP breaks the single-row `Air.Flat.Component` ceiling that blocks ~23 of the 33 missing
P4 arms. **#100 and #103 are the SAME mechanism**: re-express a cross-X fact as **channel
balance** via a continuation channel (`Guarantees:=True`) whose rows **`.emit`** a tagged
prev/next pair + a boot endpoint, added with **`SoundEnsemble.addChannel`**, balance
feeding the channel-agnostic **`SeamTagChain.boot_chain_derived_generalN`** engine.
**`addVm` is dead for both** (production Main/Mem require finished channels). The engine is
banked (for #103) and reusable verbatim for #100.

The capability is the *easy* half. The wall is **production wiring** (especially #100:
Main is referenced by all 28 construction families — higher blast radius than the #103 Mem
swap, which itself BLOCKED on build at L4.5). Channel-level GO does NOT de-risk it.

## §1 Route (settled) (→ [RESEARCH_XCAP#route](../research/RESEARCH_XCAP.md#route))

- **#103:** addChannel seam — **banked** on `p4-103-landing`, general-N value seam from
  balance, 0 PROJECT axioms. But **vacuous-as-banked** (per-row emission).
- **#100:** addChannel `PcContChannel` — route **CONFIRMED** by probe `wbghidb2k`; the old
  `addVm` Spike A only worked on an empty ensemble (no finished OpBus/MemBus).
- **DEAD (do not revisit):** `addVm`/`SoundVmEnsemble` (doubly-blocked, both #100/#103),
  finished-channel (both-push-and-pull), fork-Clean, bespoke-AcceptedTrace-field. Full
  record: `PLAN_ENDGAME_P4_103.md §2` + the archive.

## §2 PR staging — CHECKLIST (keep current)

**Track 100 (cross-row PC):**
- [x] **PR-X100.0 — channel-level route probe — GO (2026-06-17).** Built
      `ZiskFv/Spike/PcHandshakeProbe.lean` (worktree `xcap-seam-tag`, branch
      `xcap-x100-probe`, commit `a541f3ac`): reused the channel-agnostic
      `SeamTagChain.boot_chain_derived` with the `SeamVal.v0` lane = PC. `balance` is
      load-bearing (drives the seam `seg1.prev = seg0.last ⟹ p1v0 = l0v0`), the row-local
      pin `l0v0 = p0v0+4` + the seam give `pc1 = pc0+4`, certified **non-vacuous** by a
      PROVEN `pcBootList2_balanced` witness. Green, **kernel-only axioms (0 `ZiskFv.*`)**,
      adversarially verified. **Scope confirmed = the CHANNEL half only**: the pin is a
      hypothesis (= SPINE-#2 / `constraint_18` mux), and wiring `.emit`+`addChannel` into
      the *real* `fullRv64imEnsemble` is **NOT** done — that is PR-X100.1 (the un-de-risked
      production wall). The engine relabels to PC cleanly; the route is confirmed.
- [~] **PR-X100.1 — Production wiring — DE-RISK PROBE GREEN (2026-06-17), blast radius
      REFUTED.** Wired a real `PcContChannel` into the live `componentWithRomMemAndOpBus`
      (`ZiskFv/Channels/PcContinuation.lean` + Main/Constraints + Main/Circuit, commit
      `9d1fe5be` on `xcap-x100-wiring`, ~71 lines, zero sorry, full downstream cone GREEN).
      **NO new `MainRow` column needed** — `main_step` (existing `MainRomRow` col) is the
      tag (LOW blast radius). The 28 `construction_<op>_sound` do **NOT** ripple (they use
      only the row projection `rowInputVar`, never the channel set) — confirmed by compile.
      The soundness wrapper fixed by the #103 `circuitWithDualMemBus` idiom verbatim. So
      the production wiring is **additive, like #103's addChannel — NOT the wall I feared.**
      Remaining sub-PRs (the genuine work, now isolated):
  - [ ] **PR-X100.1a — `.addChannel PcContChannel` + boot endpoint** on `fullRv64imEnsemble`
        (mirror `Mem.bootComp` / the `.addChannel` wiring); re-establish ensemble balance.
  - [x] **PR-X100.1b — the two SEMANTIC PINS — DONE/GO (2026-06-17, commit `74afae9b`).**
        (i) real next-PC mux written in the emit (row-local, green); (ii) `main_step`
        consecutiveness via a faithful `SEGMENT_STEP` fixed column (mirror Mem's SEGMENT_L1)
        + the `main.pil:90` STEP relation → `main_step_consecutive`
        (`ZiskFv/AirsClean/Main/SegmentStep.lean`), kernel-only, **zero blast radius** (full
        build green, 28 constructions untouched). **So the channel seam now gives a genuine
        cross-row handshake `pc(i+1) = nextpc(row i)` ON THE REAL Main pc columns.**
  - [ ] **PR-X100.1c — Gap (c): the exec-bus↔real-pc bridge — PLANNED via ROUTE C (scoped
        2026-06-17 → [`RESEARCH_GAP_C.md`](../research/RESEARCH_GAP_C.md)).** `h_nextPC_matches`
        (carried by ALL 30 sound arms) constrains the foreign `exec_row[1]!.pc`, not the real
        `pc(i+1)`. **Reframed:** discharging it is a 3-equality chain, only ONE new —
        (1) `exec_row[1].pc = pc(i+1)` [NEW; `exec_row` is caller-chosen, so populate it
        faithfully from the trace — `bus_effect` *defines* `exec_row[1].pc` as the producer
        next-PC = the next row's pc, so this is the unique faithful choice, definitional not a
        premise]; (2) `pc(i+1) = nextpc(row i)` [the seam, = X100.1a]; (3) `nextpc(row i) =
        Sail nextPC` [already exists per-row, sequential]. **Route A rejected** (re-adds a
        foreign bus); **Route B** (restate off `bus_effect`) is the heavier P6 follow-on.
        Route C is the #103-L5 compose-seam-with-tie pattern, **resident in P5's env builder**.
        Sub-PRs (PR-GapC.0 the bridge lemma is **startable NOW** with the seam stubbed):
    - [ ] **PR-GapC.0** — `nextPC_matches_of_seam` (sequential), seam as a stubbed hyp; thread
          into `construction_add_sound`; the `h_nextPC_matches` binder REMOVED (caller-burden
          net-shrink), kernel-only, k≥2 non-vacuous witness. GO/NO-GO.
    - [ ] **PR-GapC.1** — faithful `execRowOf trace binding i` (from `mainOfTable.pc (i+1)`,
          gated by `stepCoherent`) — P5-resident (refines `PLAN_ENDGAME_P5.md` PR-P5.2).
    - [ ] **PR-GapC.2** — replicate across the 10 construction files / all 30 arms; refresh
          baselines (net removal of `h_nextPC_matches`).
    - [ ] **PR-GapC.3** — discharge the stubbed seam hyp from the real-ensemble seam theorem
          (X100.1a). Scope: closes SEQUENTIAL `pc+4` for all; branch/jump targets still need
          SPINE-#2 + #101. Surviving residual: `stepCoherent` + the exec_row SHAPE (→ P6/Route B).
  - **Sequencing (corrected):** Gap (c) is the **LAST step of #100's payoff, not a blocker of
    its earlier steps.** Order: **X100.1a** (seam theorem) → **Gap (c)/Route C** → **X100.2**.
- [ ] **PR-X100.2 — Discharge `h_nextPC_matches` (sequential).** Re-root the orphaned
      next-PC math (`pc_handshake_to_next_pc`/`_branch`/`_jump`, `Airs/Main/Main.lean`)
      onto the channel-derived handshake; discharge `h_nextPC_matches` for the sequential
      `pc+4` case across the 30 constructions (net residual removal).
- [ ] **PR-X100.3 — SPINE Prereq #2: re-extract the `constraint_18` mux** as a Main
      row-local constraint (for branch/jump *targets*; sequential pc+4 doesn't need it).
      Possibly the real bottleneck for branch/jump targets — scope separately.

**Track 101 (Binary-EQ flag — INDEPENDENT, parallelizable now):**
- [~] **PR-X101.0 — Part A DONE / Part B blocked by #100 (2026-06-17).** Part A: proved
      `binary_eq_chunks_eq_bv_eq_of_wf` (`BinaryPackedCorrect.lean:2476`, commit `da663dc4`
      on `xcap-x101`) mirroring `binary_ltu_chunks_eq_bv_ult_of_wf` — `fl7%2=1 ↔ a64=b64`,
      green, kernel-only (0 `ZiskFv.*`), adversarially verified. **Finding: #101 is NOT
      fully independent of XCAP after all** — Part B (re-plumb BEQ/BNE) is BLOCKED by #100:
      the branch flag is *fused into* `nextPC_matches` (next-row PC = Sail next-PC), so
      cashing the lemma in needs the cross-row PC handshake (#100) to split flag→PC. The
      lemma is the banked prerequisite, ready once #100 lands. No residual removed yet.

**Track 103 (cross-segment Mem deep refactor — = #76 PR-76.5):**
- [ ] **PR-X103.0 — Recover dangling `362c6e83`** (`SeamRowTie.lean`) onto a branch off
      `p4-103-landing`; correct `PLAN_ENDGAME_P4_103.md`'s "L5 DONE" overstatement.
- [ ] **PR-X103.1..6 — The deep refactor (B→A→C→D→E→F→G):** SEGMENT_LAST selector column →
      gate emission → re-establish balance (**re-prove a k≥2 non-vacuity witness**) →
      ripple the 146 `componentWithDualMemBus` / 50 `MemRow` refs (mechanical) → airval↔
      column bridge → discharge `SegmentLastRowTie` from Spec → wire into #76
      `initialAgreement`. Detail: [`RESEARCH_XCAP#xseg`](../research/RESEARCH_XCAP.md#xseg).

## §3 What each piece unblocks (→ [RESEARCH_XCAP#deps](../research/RESEARCH_XCAP.md#deps))

- **#100** → sequential `pc+4` (every opcode) + JAL/JALR (2) + cross-row half of branches.
- **#101** → BEQ/BNE flag (other half of the 6 branches).
- **#103 deep refactor** → cross-segment seed for all 11 loads/stores (#76 PR-76.5).
- Branches (6) = #100 + #101 + SPINE-#2; JAL/JALR (2) = #100 + SPINE-#2; loads/stores (11)
  = #103 + #76.

## §4 Recommended order

1. **PR-X100.0** (cheap GO/NO-GO; confirms the route end-to-end on the real ensemble).
2. **PR-X101.0** in parallel (independent, clean residual removal, ~unblocks branch flags).
3. Then the expensive production wiring — **decide PR-X100.1 (cross-row, JAL/JALR + branch
   PC) vs PR-X103.1.. (cross-segment, loads/stores)** based on which blast radius to take
   first. Both are deep; X100.1 is higher-risk (Main), X103 is more mechanical but larger
   (146-ref ripple) and chains into #76.

## §5 Anti-laundering + risks (→ [RESEARCH_XCAP#risks](../research/RESEARCH_XCAP.md#risks))

- Cross-X fact must stay a **derived `BalancedChannels` conjunct**, never a caller premise
  or axiom; baselines net-shrink. "0 PROJECT (`ZiskFv.*`) axioms; Sail + kernel external."
- **Vacuity:** every channel claim witnessed on a realistic multi-row (k≥2) balanced
  trace; never the one-row/`rfl` floor (#103's first probe was vacuous).
- **R1 production blast radius (#100 Main) — REFUTED 2026-06-17** by the PR-X100.1
  de-risk probe (commit `9d1fe5be`): the wiring is additive (no `MainRow` column change;
  constructions don't ripple). The risk MOVED to **R1' the semantic pins** (PR-X100.1b):
  the next-PC mux + `main_step` consecutiveness are cross-row constraints not in the live
  model — extracting/pinning them is the new unknown (untested).
- **R2 SPINE-#2** (mux re-extraction) gates branch/jump *targets*, and is now also on the
  critical path as PR-X100.1b(i) — separate from the (proven additive) channel wiring.
- **R4** recover `362c6e83` before GC (NOTE: the #103 TIE is actually on local
  `p4-103-landing` head `84be0251` in the `xcap-seam-tag` worktree, not truly lost).

## §6 What changed vs the archive

Archive proposed `addVm`/`SoundVmEnsemble` for both #100 and #103 — **dead** (doubly
blocked). This rewrite: #103 via banked `addChannel` (deep refactor remains); #100 route
**confirmed** as the *same* `addChannel` idiom (probe `wbghidb2k`); #101 split out as an
independent parallel track; the production wiring (not the channel math) identified as the
wall; the cross-row/cross-segment **framing** and the full **dead-end record** carried
forward (here + `PLAN_ENDGAME_P4_103.md §2`).
