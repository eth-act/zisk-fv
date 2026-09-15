# ENDGAME ROADMAP — from envelope-conditional theorem to trace-level statement

This is the metaplan for the campaign that takes the project from its current
state (global theorem universally quantified over proof-bearing `OpEnvelope`
packages, three named hypotheses, zero project axioms) to the endgame public
statement (a trace-level theorem over raw committed trace data, with
`OpEnvelope` and its burden-management machinery retired).

## How this file works

- One section per phase below; each phase is executed via ONE plan file
  (`PLAN_ENDGAME_P<n>.md`), sized at roughly **5 PRs of up to ~1k diff lines
  each**. Plan files are written ONLY when their phase is about to be
  staffed — late plans encode reality, not guesses.
- This file is updated ONLY at stream boundaries (plan written, PR merged,
  phase gate passed). Granular state lives in each worktree's STATUS.md.
- Re-orientation chain: this file (campaign) → `docs/ai/PROJECTS.md`
  (active streams) → worktree `STATUS.md` (current work).
- Since 2026-06-17, plan files are short **navigable spines**; the detailed
  evidence (gap maps, route probes) lives under `docs/ai/research/RESEARCH_*.md`,
  with raw multi-agent workflow output in `docs/ai/research/_raw/`.
- GitHub issues are the durable public anchors with full technical content:
  #61 (umbrella: bucket audit + construction theorem + export theorem),
  #74 (trace instantiation → P5), #75 (kernel-only closure), #76 (memory
  argument), #77 (differential testing), #78 (external re-check), and the P4
  foundational prerequisites #100 (cross-row Main PC), #101 (Binary-EQ
  aggregation), #103 (cross-segment Mem).

## 0. Structure & navigation map (READ FIRST — we are nested ~4 levels deep)

The work is a DAG, not a clean tree. This map is the single re-orientation anchor;
the per-node docs/issues carry the detail.

```
L1  ENDGAME CAMPAIGN          this file (ENDGAME_ROADMAP.md)  ·  umbrella issue #61
    goal: envelope-conditional global theorem  →  trace-level public statement
    P1 Foundations .................. DONE (merged)
    P2 Validation (#77/#78) ......... off critical path, not started
    P3 Memory reshape ............... DONE (merged)
    P4 CONSTRUCTION THEOREM  ◀ WE ARE HERE  (30/63 sound)
    P5 Trace-level export (#74) ..... PLAN WRITTEN 2026-06-17 (held for full theorem); blocked on P4
    P6 OpEnvelope retirement ........ blocked on P5

L2  P4 = the construction theorem (AcceptedTrace → OpEnvelope)   index: PLAN_ENDGAME_P4_METAPLAN.md  ·  #61
       30 / 63 opcodes sound + MERGED to main (#98/#99/#102 + #106 LUI/AUIPC); head a5679e5b.

L3    P4 internal streams:
      ├─ SPINE   kill laundering #94/#97 + template + audit gate .. DONE/merged   · PLAN_ENDGAME_P4_SPINE.md
      ├─ SWEEP   28 sound: RV64I ALU + 12 shifts + W-ALU .......... DONE/merged   · PLAN_ENDGAME_P4_SWEEP.md
      ├─ (LUI/AUIPC) 2 sound: provider-free U-type .............. DONE/merged #106
      ├─ M-EXT   ~6 unsigned constructible + 7 signed defect-carved  NOT STARTED   · (plan TBD)
      ├─ MEMORY  loads/stores, 11 ops (#76) ......... PLAN REWRITTEN 2026-06-17    · PLAN_ENDGAME_P4_MEMORY.md
      │            (route Z, store-driven Fold B; PARTIAL discharge to a named residual; cross-seg half = #103)
      └─ AENEAS  aeneasBridgeTrust discharge (separate residual) . NOT STARTED    · PLAN_ENDGAME_AENEAS.md

L4    P4 foundational prerequisites (block the L3 families):
      ├─ #100  cross-ROW (Main PC handshake)  → blocks branches + ALL next-PC
      ├─ #101  Binary-EQ aggregation          → blocks BEQ/BNE flag (independent of XCAP)
      └─ #103  cross-SEGMENT (Mem seam)       → blocks MEMORY/#76
            │   (#103 was discovered AS a prerequisite of #76 when #76's spike went NO-GO)
            ▼
        XCAP — the capability that DELIVERS #100 + #103   re-scoped 2026-06-17 · PLAN_ENDGAME_XCAP.md → RESEARCH_XCAP.md
            insight: #100 & #103 are the SAME mechanism — re-express the cross-X fact as
                     channel BALANCE via a continuation channel (.emit + SoundEnsemble.addChannel)
                     feeding the channel-agnostic SeamTagChain engine. addVm is DEAD for both.
            #103:    addChannel seam BANKED (origin/p4-103-landing) but VACUOUS-AS-BANKED
                     (per-row emission) → needs the deep refactor (SEGMENT_LAST gating + ~145
                     Balance projections + SegmentLastRowTie); = #76 PR-76.5.
            #100:    route CONFIRMED = ADDCHANNEL (probe wbghidb2k); old addVm Spike A only
                     worked on an empty ensemble. No construction yet.
            wall:    PRODUCTION WIRING (esp. #100 Main, blast radius across all 30 sound
                     constructions), NOT the channel math. Next = PR-X100.0 (cheap route probe). Awaiting go.
```

**The key dependency (DAG edges):** the **XCAP build** unblocks **#100** (branches +
all next-PC + JAL/JALR) AND **#103** (→ #76 → loads/stores) = **~19 of the 33 remaining
opcodes** (loads/stores 11 + branches 6 + JAL/JALR 2; necessary-not-sufficient for the 6
branches, which also need #101 + SPINE-#2). **#101** is separately needed for the BEQ/BNE flag; **SPINE-#2** (re-extract
the `constraint_18` PC mux as a Main row constraint) for branch/jump *targets*. **M-EXT**
and **AENEAS** are independent of XCAP. Remaining 33 split: loads/stores 11 (#103+#76) ·
branches 6 (#100+#101+SPINE-#2) · JAL/JALR 2 (#100+SPINE-#2) · M-ext ~13 (~6 unsigned
constructible + 7 signed defect-carved) · FENCE 1 (defect). (LUI/AUIPC done via #106.)

**Re-orientation chain:** `STATUS.md` (current work) → this map → the named
`PLAN_ENDGAME_*.md` for the active node → its GitHub issue for durable detail.

## Phase status table

| Phase | Content | Issues | Plan file | Depends on | Status |
|---|---|---|---|---|---|
| P1 | Foundations & verdict: completeness-stream finalization, kill `native_decide` (kernel-only closure), envelope survey + ADD instantiation, bucket audit, lean4lean scouting | #75, #74 (stages 0–2), #61 (audit), #78 (scout) | `PLAN_ENDGAME_P1.md` | — | DONE (merged 2026-06-13, #79/#80/#89; bucket audit via #83) |
| P2 | Validation tooling: Sail-Lean differential testing; lean4lean build-out (if scout says go) | #77, #78 | not yet written | — (independent) | QUEUED |
| P3 | The memory argument: reshape `h_memory_timeline` → named auditable residual; #74 stage 3 | #76, #74 (stage 3) | `PLAN_ENDGAME_P3_CLOSEOUT.md` | #84–#87 + #90/#91 merged 2026-06-13; #88 closed | DONE (reshape only — memory-trust reduction is P4) |
| P4 | Construction theorem: `AcceptedTrace → OpEnvelope`, family by family | #61, #100, #101, #103 | `PLAN_ENDGAME_P4_METAPLAN.md` + `_SPINE` + `_SWEEP` + `_MEMORY` + `XCAP` | P1+P3 DONE | IN PROGRESS — **30 of 63 opcodes sound, MERGED to main** (RV64I R/I ALU + 12 shifts + W-ALU via #98/#99/#102; +LUI/AUIPC via #106; head `a5679e5b`); #94/#97 closed. 0 project axioms; all `pass`. Remaining **33**: M-ext (~13: ~6 unsigned + 7 defect-carved), branches (6, #100/#101/SPINE-#2), loads/stores (11, #76+#103), JAL/JALR (2, #100/SPINE-#2), FENCE (defect). **Active P4-prereq = XCAP** (#100 route confirmed addChannel; #103 banked-but-vacuous; plans rewritten 2026-06-17). #76 plan rewritten (route Z). |
| P5 | Trace-level export theorem + gate re-rooting (new public statement) | #61, #74 | `PLAN_ENDGAME_P5.md` → `RESEARCH_DERIVE_ENV.md` | P4 | PLAN WRITTEN 2026-06-17; **HELD for full theorem** (Cody, blocked on P4=63/63). env is scaffolding; removal is an assembly/quantification gap (env⊥bus_effect); NOT premise-free |
| P6 | Envelope retirement: fuse construction into per-family proofs, flatten wrapper layer, delete `OpEnvelope` + burden machinery, re-baseline gates (Phase-E-style negative-diff campaign) | issue to be filed at P5 | not yet written | P5 | BLOCKED on P5 |

Background items (no phase): defect carve-outs retire when the patched ZisK
release lands — schedule the flake re-pin BETWEEN phases (forces
re-extraction/cold rebuild); signed-Arith completeness disjuncts and
table-op scope extensions are optional follow-ups, not on the critical path.

## Critical path

P1(#74 survey) → P1(bucket audit) → P4 → P5 → P6, with P3 the one large
pure-proof stream running beside P1/P2. P2 is fully off the critical path.
**P4 (the current gate) is itself gated by:** XCAP (cross-row #100 + cross-segment
#103) + #76 (loads/stores memory) + M-ext extractors + defect retirements (FENCE,
signed-M). XCAP is the highest-leverage P4-prereq (~19 of the 33 remaining arms).

## Invariants for every phase (inherited from the wave campaign)

- Plans follow the strengthened-wave format: verified groundwork, mechanical
  recipes, hard invariants, exact verification commands, per-PR checklists,
  and the PR protocol: open the PR yourself when gates are green, first body
  line `Queued for Claude review — do not merge.`, then STOP.
- Zero new axioms anywhere; ledgers/baselines byte-identical unless a plan
  explicitly says otherwise (P5/P6 re-baselining is plan-governed).
- Manual worktrees from `origin/main`; `lake exe cache get` first; plan-file
  edits limited to ticking your own boxes + prefixed log lines.
- Anti-laundering principle verbatim in every sub-agent prompt; promise
  discharge (P3, P4) must shrink the metrics.

## Log

(one line per boundary event)

- 2026-06-12: roadmap created; Waves 1–5 (PRs #69–#73) merged; P1 plan
  written; P2–P6 queued.
- 2026-06-13: P1-PR1 (#79) + P1-PR2 (#80) merged; P1-PR3/4/5 (#81/#82/#83)
  open, queued for review (do not merge). #83 is stacked on #82.
- 2026-06-13: P3 plan written (`PLAN_ENDGAME_P3.md`, 5 PRs). Survey verdict:
  #76's salvage is already on `main` via #65, so P3 is the derivation of
  `MemoryTimelineEvidence` from extracted Mem AIR constraints + channel
  balance, not a salvage import. The residual is `stateBytesAtPrefix` (the
  Sail-side/time-order half).
- 2026-06-13: P3 PRs #84–#88 executed. Reviewed: #84–#87 sound (with fixes);
  #88 ("reduce memory timeline boundary") REJECTED — it renames
  `h_memory_timeline`→`h_memory_construction` with every audited metric flat,
  unmeasured and undocumented, indistinguishable from a rename. Deep follow-up
  established the corrected thesis: the memory residual is genuinely
  trace-global / P4-bound, so P3 cannot shrink — only reshape-to-named-P4-fact +
  make auditable. `PLAN_ENDGAME_P3_PR5_REWORK.md` written (supersedes PR 5):
  adds a global-theorem-binder gate baseline (the missing audit signal), the
  obligation map, a non-degenerate alignment witness, and an honest residual
  ledger. Also surfaced: real prefix-read-soundness derivation exists but is
  ORPHANED (`Balance.lean:6334`) — it is P4's to wire.
- 2026-06-13: #83 genuinely landed on main via #89 (`cf2a4aa6`) — P1 complete.
  Feasibility survey VERDICT: P3 cannot reduce memory trust — the orphaned
  prefix-read chain is single-segment and outputs the weaker
  `AcceptedMemoryReplayEvidence` (no `initialAgreement`); the load residual needs
  whole-trace cross-segment assembly = P4. P3's honest goal is reshape +
  auditability + a precise P4 obligation ledger. `PLAN_ENDGAME_P3_CLOSEOUT.md`
  is the authoritative close-out (supersedes PR 5 + the rework). Memory-trust
  reduction is entirely P4.
- 2026-06-13: P3 CLOSED. #84/#85/#86/#87/#90/#91 merged to main (`4456a9e5`);
  #88 (the rename) closed as superseded. On main: named residual
  `memoryTimelineConstructionEvidence`, the global-theorem-binder audit gate, the
  obligation map, the non-degenerate alignment witness. Canonical baselines
  byte-identical to pre-P3 (no laundering). The reshape is one auditable line in
  `baseline-global-theorem-binders.txt`. P4 is now READY and is the first phase
  that actually reduces memory trust.
- 2026-06-13: P4 plan written (`PLAN_ENDGAME_P4.md`, 7 PRs). Survey verdict: the
  construction target is the whole `OpEnvelope`; `AcceptedTrace` must be defined
  (= `EnsembleWitness (fullRv64imEnsemble …)` + `BalancedChannels`); channel
  balance is ASSUMED (the balance→match theorems are already proven but unconsumed,
  so bucket-(a) discharge is integration), EXCEPT two novel proofs front-loaded as
  de-risking spikes — the cross-segment whole-trace memory chain and store
  preserved-byte soundness. Decode = named bucket-(b) `ProgramBinding` input. After
  P4 the residual premises are aeneasBridgeTrust + program-binding/boot +
  NoKnownDefect, and the dynamic memory timeline is constructed.
- 2026-06-14: Aeneas-wiring plan written (`PLAN_ENDGAME_AENEAS.md`, 6 PRs) —
  discharge `aeneasBridgeTrust` by importing the Aeneas-extracted transpiler
  (`trust/aeneas/ProductionM2.lean`, on main via #93) and proving the row facts
  from it. Survey verdict: the `extractedRow → *OfExtractedShape →
  aeneasBridgeTrust` discharge chain is ALREADY complete for all 63 arms; the only
  gap is producing a real `MainRowProvenance` from the extracted transpiler. HONEST
  framing (binding): this DISCHARGES the hypothesis but does NOT eliminate Rust↔Lean
  trust — it trades 63 hand-asserted row facts for one named ROM-population premise
  + Charon/Aeneas faithfulness + the fork pin, validated by a new Rust-side
  differential test (the #77 counterpart). Gating blocker: the Lean-toolchain
  mismatch fencing ProductionM2 out of main Lake (PR1 spike, shim-first, go/no-go).
  Composes with P4 (Valid_Main spine + ProgramBinding); feeds P5 (shrinks the
  export premise list). 0 axioms preserved.
- 2026-06-15: P4 construction CLOSEOUT (`PLAN_ENDGAME_P4_SPINE.md`,
  `RESEARCH_PR94_CLOSEOUT.md`). The first construction attempt (#94 + stacked #97)
  was found to be **laundering** — bucket-(a)/(c) facts carried in caller-supplied
  `*RowBinding`/`MainRowProvenance` records (37×), dead `trace.constraints`/
  `balanced`, a structurally blind audit gate. Deep research also resolved the
  "extract more?" question: the cross-row PC constraint is extracted only into the
  dead legacy model; the live single-row Clean `Air.Flat.Component` cannot hold it,
  so next-PC is a foundational residual (issue #100), and the branch flag needs the
  missing Binary-EQ aggregation lemma (issue #101); ZisK has no exec bus
  (`bus_effect` is a foreign openvm import). Closed-and-replanned-with-salvage,
  delegated via 4 orchestrated workflows. Landed (open, do-not-merge): **PR #98**
  (audit reclassification + decision record + salvage manifest) and **PR #99**
  (supersedes #94/#97: strips the relabel `AcceptedTrace.lean` 10814→656 lines,
  adds the first honest `construction_sub_sound` — 17 named residual binders +
  `execRow` ∀-binder, data effect derived from `trace.balanced`, 0 PROJECT axioms
  — and the recursive Option-X audit gate; full `nix run .#test` green). #61
  comment posted; prerequisites #100/#101 filed. REMAINING: Cody merges #98/#99
  (closing #94/#97); then the SWEEP applies the proven §2 template across families.
- 2026-06-15: P4 SWEEP executed (`PLAN_ENDGAME_P4_SWEEP.md`), 6 verified waves,
  each adversarially `pass`, 0 PROJECT axioms, deep baseline grows by honest flat
  binders only. PR #99 READY front (W1 OR/XOR/SLT/SLTU; W2 the 5 I-types; W3 m32=0
  shifts; W4 m32=1 W-shifts) = 23 families. Stacked PR #102 NEEDS-WORK (W5 ADD/ADDI
  — provider disjunction, both arms discharged; W6 ADDW/SUBW/ADDIW — authored the
  m32=1 binary lane lemma input_r1_packed_a32_row). **28 of 63 RV64IM opcodes now
  have sound constructions; remaining 35 need new plans (M-ext) or unblocking
  (#76 loads/stores, #100 branches+next-PC, #101 BEQ/BNE).**
- 2026-06-16: P4 stack MERGED to main — #98 (`2854b81b`), #99 (`effef9e6`),
  #102 (`eb19cc8f`, rebased onto main + retargeted); #94/#97 CLOSED as superseded;
  0 open PRs. 28/63 opcodes sound now on `origin/main`. main is unprotected (no CI).
- 2026-06-16: #76 memory plan written (`PLAN_ENDGAME_P4_MEMORY.md`) but Spike #1
  (cross-segment seam) ran NO-GO → filed prerequisite #103 (cross-segment Mem),
  the Mem-side analogue of #100's cross-row ceiling.
- 2026-06-16: FOUNDATIONAL cross-X capability plan written
  (`PLAN_ENDGAME_XCAP.md`) addressing #100 + #103 — a new phase BETWEEN P4's sweep
  and its memory/branch families. Spike-first (2 go/no-go spikes). KEY: Clean ships
  an unused VM-channel state-transition framework (Clean/Air/Vm.lean) that fits both
  ceilings (PC handshake + segment seam are both VM transitions) — route is "adopt
  it," not "fork Clean's per-row model." Unblocks ~23 of the 35 remaining opcodes.
  NOT executed (framework change; awaiting go). Other buildable-now: M-ext, LUI/AUIPC.
- 2026-06-16: XCAP go/no-go spikes RAN — route VALIDATED. Spike A (cross-row #100)
  = GO clean (derived row1.pc=row0.pc+4 from SoundVmEnsemble balance, 0 PROJECT
  axioms, non-vacuous). Spike B (cross-segment #103) = GO-WITH-CAVEATS (the
  SoundEnsemble→SoundVmEnsemble migration compiles + the VM channel hosts the seam;
  #103 carries a bounded tagged-channel extraction sub-prereq). Verdicts posted on
  #100/#103. NEXT (awaiting go): the XCAP build (SoundVmEnsemble migration + Main/Mem
  VM tables + the #103 tagged-channel extraction) — a multi-PR framework phase that
  unblocks ~23 of the 35 remaining opcodes.
- 2026-06-17: **P4 → 30/63.** LUI/AUIPC provider-free sound constructions merged via
  #106 (head `a5679e5b`); remaining 33. (Corrects the stale 28/`eb19cc8f` above.)
- 2026-06-17: **XCAP route CORRECTED — supersedes the 2026-06-16 "route VALIDATED"
  entry.** The `addVm`/`SoundVmEnsemble` route is a **DEAD END for BOTH #100 and #103**:
  production Main and Mem each REQUIRE finished channels (OpBus/MemBus), so
  `addVm.reqs_disjoint_finished` (`Vm.lean:688`) is false. Spike A/B "GO" only held on
  an empty ensemble and does NOT transfer to production. The live route for BOTH is the
  **`SoundEnsemble.addChannel` idiom** (`.emit`-not-`.pull` continuation channel +
  channel-agnostic `SeamTagChain.boot_chain_derived_generalN`). #103 seam is BANKED on
  `origin/p4-103-landing` but **vacuous-as-banked** (per-row emission) → needs the deep
  refactor. #100 route **CONFIRMED = addChannel** (probe `wbghidb2k`). `PLAN_ENDGAME_XCAP.md`
  rewritten (old archived as `*.archive-2026-06-16.md`); evidence `RESEARCH_XCAP.md`. The
  real wall is **production wiring**, not the channel math (esp. #100 Main, blast radius
  across all 30 sound constructions). Next = PR-X100.0 (cheap real route probe), awaiting go.
- 2026-06-17: **#76 (P4 MEMORY) plan REWRITTEN** (`PLAN_ENDGAME_P4_MEMORY.md` →
  `RESEARCH_76_{GAP_MAPS,DESIGN}.md`). Route Z (within-segment + named residual); the
  core is a **store-driven "Fold B"** (a red-team corrected an earlier whole-state
  framing that was a non-sequitur). #76 is a **PARTIAL** discharge to a named residual
  (boot + cross-segment seed + trace coherence), **never premise-free** (conservation
  law: the replay engine only transports memory agreement). Leads with make-or-break
  spike PR-76.0. The cross-segment seed half = #103 deep refactor (= PR-76.5).
- 2026-06-17: **P5 "deriving env" plan WRITTEN** (`PLAN_ENDGAME_P5.md` →
  `RESEARCH_DERIVE_ENV.md`). Key findings: `env` is scaffolding, so removal is an
  **assembly/quantification gap, not a derivation gap** (the 30 `construction_<op>_sound`
  already bypass env; decode + rfl-equality already exist); env-elimination is
  **orthogonal to `bus_effect` retirement**; the theorem does NOT become unconditional.
  Cody chose scope **A (hold for the full theorem)** — blocked on P4=63/63 — and picked
  **XCAP as the next unblocker**. (Roadmap P5 row updated from "not yet written".)
- 2026-06-17: docs/ai/plan cleaned — done/superseded plans moved to `archive/` (with a
  status-marked `README.md`); active set = ROADMAP + P4_METAPLAN + P4_103 + P4_MEMORY +
  P5 + XCAP + AENEAS.
- 2026-06-17: **XCAP PR-X100.0 EXECUTED — GO.** Channel-level PC-handshake probe
  (`ZiskFv/Spike/PcHandshakeProbe.lean`, worktree `xcap-seam-tag`, branch
  `xcap-x100-probe`, commit `a541f3ac`): `SeamTagChain.boot_chain_derived` relabels to PC,
  `balance` load-bearing, `pc1 = pc0+4` derived NON-vacuously (proven `pcBootList2_balanced`);
  green, kernel-only (0 PROJECT axioms), adversarially verified. Confirms the **channel
  half**; the next-PC pin is a hypothesis (= SPINE-#2) and real-ensemble wiring is **NOT**
  done (= PR-X100.1, the un-de-risked production wall). Route end-to-end at the channel
  level is now proven, not just probed.
- 2026-06-17: **XCAP PR-X101.0 Part A EXECUTED — GO; Part B blocked by #100.** Proved
  `binary_eq_chunks_eq_bv_eq_of_wf` (`BinaryPackedCorrect.lean:2476`, branch `xcap-x101`,
  commit `da663dc4`) — the BEQ/BNE flag `fl7%2=1 ↔ a64=b64`, mirroring the proven LTU
  aggregation; green, kernel-only (0 PROJECT axioms), adversarially verified. **Finding:
  #101 is NOT fully independent of XCAP** — the re-plumb (Part B) is blocked because the
  branch flag is *fused into* `nextPC_matches`, so cashing the lemma in needs #100 to
  split flag→PC. Lemma banked. Both cheap XCAP pieces (X100.0, X101.0-A) reinforce that
  **#100 is the lynchpin**. Next = the production wall (PR-X100.1 vs PR-X103) — Cody's
  track decision.
- 2026-06-17: Cody chose the **#100 (Main) track**. **PR-X100.1 DE-RISK PROBE = GREEN —
  the production wall is REFUTED.** Wired a real `PcContChannel` into the LIVE
  `componentWithRomMemAndOpBus` (`ZiskFv/Channels/PcContinuation.lean` + Main/Constraints +
  Main/Circuit, branch `xcap-x100-wiring`, commit `9d1fe5be`, ~71 lines, zero sorry, full
  downstream cone GREEN). **NO new `MainRow` column** (`main_step` is the tag); the 28
  constructions do **NOT** ripple (they use only the row projection, never the channel
  set). So #100 production wiring is **additive, like #103's addChannel — not a
  #103-L4.5-style wall.** The risk MOVED to the two cross-row **semantic pins** (PR-X100.1b,
  SPINE-#2 class, not in the live model): the real next-PC mux + `main_step` consecutiveness.
  This also RE-RATES the #103 track: if a Mem column refactor is similarly insulated, the
  ~145-projection fear may be overstated — worth re-checking before committing to X103's
  heavy refactor. Checkpoint: X100.0 GO + X101.0-A + X100.1 de-risk GREEN, all verified +
  committed on do-not-merge probe branches.
- 2026-06-17: Cody said "run the #100 track." **PR-X100.1b pins = GO; the GATE found a
  deeper WALL (Gap c).** (commit `74afae9b`) (i) real next-PC mux in the emit; (ii)
  `main_step` consecutiveness via a faithful `SEGMENT_STEP` fixed column (mirror Mem
  SEGMENT_L1) + main.pil:90 STEP relation → `main_step_consecutive`
  (`ZiskFv/AirsClean/Main/SegmentStep.lean`), kernel-only, ZERO blast radius. The seam now
  yields a genuine cross-row handshake `pc(i+1)=nextpc(row i)` ON THE REAL Main pc columns
  — the #100 channel CAPABILITY is built. **⛔ Gap (c) WALL:** `h_nextPC_matches` is about
  `exec_row[1]!.pc` (the foreign execution-bus artifact, free ∀-binder, bucket-c), NOT the
  real `pc(i+1)` column; no exec-bus channel / no linking theorem exists, so the seam does
  NOT discharge `h_nextPC_matches`. Closing it = an exec-bus↔real-pc bridge =
  **bus_effect-retirement-class work** (new, untested). **#100's PAYOFF is blocked at Gap
  (c); X100.1a/X100.2 don't close it.** RE-RATING: discharging next-PC (#100) is ENTANGLED
  with bus_effect retirement (env-ELIMINATION ⊥ bus_effect still holds; the next-PC
  DISCHARGE does not). Awaiting Cody: (1) attempt the Gap-(c) bridge, (2) bank #100
  capability + pivot to an independent track (M-ext), or (3) rescope.
- 2026-06-17: **Gap (c) PLAN made — Route C** (scope workflow `wp9ubg80g` →
  `docs/ai/research/RESEARCH_GAP_C.md`; plan in `PLAN_ENDGAME_XCAP.md` PR-X100.1c). Reframed
  favorably: discharging `h_nextPC_matches` is a **3-equality chain, only ONE new** —
  (1) `exec_row[1].pc = pc(i+1)` [exec_row is CALLER-CHOSEN; the P5 env builder populates it
  FAITHFULLY from the trace, definitional not a premise — `bus_effect` defines exec_row[1].pc
  as the producer next-PC = next row's pc], (2) the #100 seam (X100.1a), (3) the column↔Sail
  bridge (already exists, sequential). **Route C** (P5-resident, the #103-L5 compose-seam-with-tie
  pattern) is cheapest-sound; **Route A rejected** (re-adds a foreign bus), **Route B**
  (restate off bus_effect) = the heavier P6 follow-on. Gap (c) is **UNIVERSAL** (all 30 arms),
  the **last mile for #101**, **shared with #76**. **PR-GapC.0 (the bridge lemma, seam stubbed)
  is startable NOW.** Surviving residual: `stepCoherent` + the exec_row SHAPE (→ P6). The §3
  orthogonality claim in RESEARCH_DERIVE_ENV corrected.
- 2026-06-17: **EXECUTED the gap-c plan → FUNDAMENTAL FAITHFULNESS NO-GO (PIL-verified).**
  Built GapC.0 (bridge lemma `nextPC_matches_of_seam`, 7b62d4d0), GapC.1 (binder analysis +
  flag elimination, cb2a677f), X100.1a (`pc_seam_of_balanced` channel-level seam theorem,
  4d0fad1d) — all kernel-only. THEN the wall-(a) probe checked `main.pil` and found the
  **per-row `PcContChannel` is a FABRICATED channel**: ZisK has NO per-row `pc`-tagged bus —
  within-segment PC is a per-row POLYNOMIAL constraint (`main.pil:410`, the existing
  `pc_handshake`), cross-segment PC is a `direct_update` AIRVAL bus (`main.pil:501-529`). So
  the seam is type-illegal/non-existent, `pc_seam_of_balanced` is sound over a fabricated
  model but unbalanceable on real traces, and the gap-c plan CANNOT close faithfully. **#100 ≠
  #103** (cross-segment IS a bus; cross-row within-segment PC is a CONSTRAINT). The earlier
  "ADDCHANNEL for #100 confirmed" / "same mechanism as #103" verdicts were WRONG (no PIL
  faithfulness check). The #100 channel commits are sound-Lean-over-a-nonexistent-channel —
  dead-end evidence, do NOT pursue. **Genuine #100 path = route A:** the per-row `pc_handshake`
  constraint (`main.pil:410`) into the live single-row Clean component (the ORIGINAL cross-row
  obstruction) — a different deep workstream. #103 (cross-segment) UNAFFECTED. Banners added to
  RESEARCH_GAP_C / RESEARCH_XCAP / PLAN_ENDGAME_XCAP. LESSON: route-feasibility probes MUST
  verify PIL faithfulness (does the bus/channel exist in ZisK?) before committing — compile +
  kernel-only ≠ faithful.
- 2026-06-18: **#103 CLOSED (not-planned), folded into #76.** The banked cross-segment seam
  capability (origin/p4-103-landing cac77248) + the local-only L5 TIE (SeamRowTie.lean,
  p4-103-landing 84be0251, UNPUSHED) feed #76 PR-76.5 (cross-segment seed). Branch references
  in the #103 closing comment + the #76 pointer comment. #103's bus is genuine (unlike #100's
  fabricated PC channel) — the remaining fix is per-segment SEGMENT_LAST gating. Keep
  p4-103-landing do-not-merge.
