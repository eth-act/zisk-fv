# PLAN_ENDGAME_P4_METAPLAN — P4 umbrella & progress index

**P4 goal (one line):** Replace the OpEnvelope per-arm caller-supplied promise burden with *sound* per-family **construction theorems** — `AcceptedTrace + ProgramBinding + profile + h_bridge + h_defects → OpEnvelope at row i`, where every bucket-(a) data effect (op-bus match, row shape, circuit-internal rd arithmetic, MemBus shape, lane→rd) is DERIVED from `trace.balanced`/`trace.constraints` and only genuine bucket-(b)/(c) facts survive as explicit top-level binders.

---

## Headline progress

**30 of 63 RV64IM opcodes have sound constructions, ALL MERGED to `origin/main`** (head `a5679e5b`): the 28 RV64I ALU/shift/W-ALU (#98/#99/#102) + **LUI/AUIPC** (#106, the first *provider-free* `is_external_op=0` families). 0 PROJECT axioms throughout.

> **SESSION UPDATE 2026-06-17 (where the rest stands — all DEEP, no more easy wins):**
> - **#103 cross-segment seam CAPABILITY built + banked** on `origin/p4-103-landing` (channel-level general-N value seam via the **`addChannel` idiom — NO Clean fork**, 0 axioms). The `addVm` route + a Clean fork were proven DEAD ENDS (see `NOTE_103_MEMORY_CONTINUATION_SEAM.md`). **Do NOT merge `p4-103-landing`** (per-row seam-on-`AcceptedTrace` ⇒ the construction families go vacuous for real multi-row traces).
> - **#76 loads/stores (11)** = the DEEP cross-row Mem-timeline work that consumes the #103 capability: per-segment seam-emission redesign + structural refactor + airval↔column bridge + which-row-is-last (recorded in `PLAN_ENDGAME_P4_MEMORY.md`'s 2026-06-17 header). NOT a quick consumption.
> - **MULW/MUL** blocked on a NEW `na = MSB` sign-range bridge (operand-soundness razor); the rest of M-ext (secondary-msg + ArithDiv) blocked on a `FullEnsemble` Arith dual-emission change; 7 signed M-ext defect-gated.
> - **branches + JAL/JALR (8)** → #100 cross-row PC; likely the SAME `addChannel` idiom (cross-row analogue, unverified — cheap to scope next).
> - FENCE → defect.
> Decision (Cody): #103 banked, easy wins (LUI/AUIPC) merged, **pause/consolidate** here; pick the next deep workstream fresh.

- **SOUND DONE: 28 families.** SUB, AND (SPINE) + the READY front (OR, XOR, SLT, SLTU, ANDI, ORI, XORI, SLTI, SLTIU, SLL, SRL, SRA, SLLI, SRLI, SRAI, SLLW, SRLW, SRAW, SLLIW, SRLIW, SRAIW) on **PR #99**; + the NEEDS-WORK families (ADD, ADDI via the provider disjunction; ADDW, SUBW, ADDIW via the authored m32=1 binary lane lemma `input_r1_packed_a32_row`) on stacked **PR #102**. Each: data effect derived from the trace; explicit named residual binders + genuine `execRow` ∀-binder; **0 PROJECT (`ZiskFv.*`) axioms** (Sail-translation + Lean-kernel axioms external as documented); each wave adversarially verified `pass`, **no RED**.
- **Executed in 6 verified waves** (see `STATUS.md` for per-wave detail): on #99 — W1 logic+compare (OR/XOR/SLT/SLTU), W2 the 5 I-types, W3 m32=0 shifts (`one_sub_zero_mul` route), W4 m32=1 W-shifts (ring route); on #102 — W5 ADD/ADDI (provider disjunction, both arms discharged), W6 ADDW/SUBW/ADDIW (authored lane lemma). Genuinely distinct data-effect chains exercised (arithmetic / bitwise / signed+unsigned compare / shift / W sign-extend), so the §2 template is broadly proven.
- **The recursive (Option X) gate covers all 28** — `soundConstructionTheorems` list in `bin/TrustGate/Main.lean`; the deep baseline (`trust/generated/baseline-construction-theorem-binders.txt`) holds 28 honest flat blocks, **zero** `*RowBinding`/`MainRowProvenance` leaves. **Adding a family = append to the list + regen.** That diff is the per-family progress signal.
- **NEEDS-WORK is DONE** (on #102), not pending: ADD/ADDI resolved the `staticLookup ∨ BinaryAdd` provider disjunction (both arms discharged from the trace, no exclusion premise); the W-ALU required *authoring* `input_r1_packed_a32_row` (the m32=1 binary lane lemma — genuinely proven, key insight: the `(1-1)*a_hi` term needs no discharge, the 32-bit binding comes from the m32-independent `a_lo` conjunct).
- **Remaining = NEW PLAN or unblocking** (the sweep's buildable scope is exhausted): M-extension (13, new ArithMul/ArithDiv extractors), branches (6, #100/#101), loads/stores (11, #76), JAL/JALR (#100), FENCE (defect), LUI/AUIPC (reconsider). All next-PC discharge is a named residual pending #100.

**Critical honesty rule:** a salvaged Layer-A op-bus wrapper (`exists_*_provider_row_matches_*_from_binding`) only de-risks the op-bus-MATCH bucket — it is **NOT** a completed construction. A sound construction additionally derives the data effect, names the residuals as explicit top-level binders, and grows the deep gate baseline by exactly those flat binders. "Salvage exists for family X" ≠ "family X is done." The #97 stack's per-family `construction_<op>` were LAUNDERING (forwarded caller-supplied `*RowBinding`/`MainRowProvenance` records into `*OfExtractedShape`; `trace.constraints`/`balanced` dead; blind gate) and were STRIPPED in PR #99 (`AcceptedTrace.lean` 10814→656 lines).

---

## Per-archetype status

Legend: **DONE** = sound `construction_<op>_sound` committed + gated + `lake build`-proven; **NOT-STARTED** = no sound construction (may have salvage); **BLOCKED-ON-#X** = a residual cannot be derived until prerequisite #X lands. PR column: where the sound construction lives.

### Archetype 1 — R-type ALU (binary lookup route) — DONE (7/7)
Dispatch: `RTYPE.lean`, `ADD_RTYPEW.lean`(ADD). Opcodes: ADD, SUB, AND, OR, XOR, SLT, SLTU.
- [x] **SUB** (#99, SPINE; `construction_sub_sound`), **AND** (#99, SPINE; `construction_and_sound`).
- [x] **OR, XOR** (#99 W1; logic route, `binary_{or,xor}_chunks_eq_bv_*_of_wf`; XOR via the `op=16` non-`<16` path).
- [x] **SLT, SLTU** (#99 W1; compare route, `binary_{lt,ltu}_chunks_eq_bv_{slt,ult}_of_wf`).
- [x] **ADD** (#102 W5; `staticLookup ∨ BinaryAdd` provider disjunction — both arms discharged).

### Archetype 2 — I-type ALU (binary lookup route) — DONE (6/6)
Dispatch: `ITYPE.lean`, `Misc.lean`(ADDI). Opcodes: ADDI, ANDI, ORI, XORI, SLTI, SLTIU.
- [x] **ANDI, ORI, XORI, SLTI, SLTIU** (#99 W2; same logic/compare chains + immediate operand via `ITypePromises.input_imm_eq` + `itype_imm_subset_holds_main`).
- [x] **ADDI** (#102 W5; provider disjunction, immediate DELTA).

### Archetype 3 — W-type 32-bit ALU (m32=1 path) — DONE (3/3)
Dispatch: `ADD_RTYPEW.lean`(ADDW,SUBW), `Misc.lean`(ADDIW). Opcodes: ADDW, SUBW, ADDIW.
- [x] **ADDW, SUBW, ADDIW** (#102 W6). Required authoring the m32=1 binary lane lemma `input_r1_packed_a32_row`/`input_r2_packed_b32_row` (the m32=0 versions existed); 32→64 sign-extend inside `equiv_<OP>_of_static_row`.

### Archetype 4 — Shifts (BinaryExtension lookup route) — DONE (12/12)
Dispatch: `Shift.lean`, `Remaining.lean`(W-shifts). Opcodes (12): SLL, SRL, SRA, SLLI, SRLI, SRAI, SLLW, SRLW, SRAW, SLLIW, SRLIW, SRAIW.
- [x] **SLL/SRL/SRA + SLLI/SRLI/SRAI** (#99 W3; m32=0, `one_sub_zero_mul` lane route, `%64` mask).
- [x] **SLLW/SRLW/SRAW + SLLIW/SRLIW/SRAIW** (#99 W4; m32=1, `ring` lane route, `%32` mask + W sign-extend).
- Note: shifts have the bare-execute conclusion shape (no writeReg-nextPC prelude) + the opaque-`row` helper pattern (avoids the giant-`rowInput` whnf timeout).

### Archetype 5a — M-extension UNSIGNED mul (ArithMul provider) — NOT-STARTED
Dispatch: `Remaining.lean`. Opcodes: MULHU, MULW.
- [ ] NOT-STARTED. No `arithMul…_from_binding` provider-match wrapper assembled (only branch-EXCLUSION lemmas `arithMul_provider_branch_ne_*` exist — exclusion ≠ provider-match); `arithMulOfTable` extractor not built. Needs ArithMul{Table,ChunkRange,CarryRange}Witness derivations. **Separate sub-stream — needs new infra.**

### Archetype 5b — M-extension UNSIGNED div/rem (ArithDiv provider) — NOT-STARTED
Dispatch: `DIVU.lean`(DIVU), `Remaining.lean`(DIVUW, REMU, REMUW). Opcodes: DIVU, DIVUW, REMU, REMUW.
- [ ] NOT-STARTED. Op-bus match needs `_primary`/`_secondary` (two op-bus entries); `arithDivOfTable` extractor + ArithDiv witnesses + remainder_bound to build. Separate sub-stream.

### Archetype 5c — M-extension SIGNED mul/div/rem (DEFECT-GATED) — NOT-STARTED
Dispatch: `Remaining.lean`. Opcodes: MUL, MULH, MULHSU, DIV, DIVW, REM, REMW.
- [ ] NOT-STARTED; correctness PERMANENTLY GATED by `Defects.NoKnownDefect` until a patched ZisK release. Construction of the constructible bucket-(a) fields still in scope; any signed-path field not constructible without the fix is a CRITICAL-REPORTING-RULE finding (name it, do not fake).

### Archetype 6 — Branches — NOT-STARTED (blocked)
Dispatch: `Branch.lean`. Opcodes (6): BEQ, BNE, BLT, BGE, BLTU, BGEU.
- [ ] BEQ / BNE — **DOUBLY BLOCKED-ON-#100 + #101** (next-PC handshake + missing Binary-EQ aggregation lemma `binary_eq_chunks_eq_bv_eq_of_wf`).
- [ ] BLT / BGE / BLTU / BGEU — **BLOCKED-ON-#100** for next-PC (flag reuses the compare chains). The salvaged op-bus machinery does NOT serve the branch next-PC.

### Archetype 7 — Loads — NOT-STARTED (blocked on #76)
Dispatch: `LDSD.lean`(LD), `Misc.lean`(LB,LH,LW), `Remaining.lean`(LBU,LHU,LWU). Opcodes (7): LD, LBU, LHU, LWU, LB, LH, LW.
- [ ] ALL 7 — **BLOCKED-ON-#76** (discharge `memoryTimelineConstructionEvidence`; cross-segment whole-trace Mem assembly). Provider `Valid_Mem` via the pre-existing `memOfTable`. NOT blocked by #100 (Mem uses single-row shadow columns).

### Archetype 8 — Stores — NOT-STARTED (blocked on #76)
Dispatch: `LDSD.lean`(SD), `Remaining.lean`(SB,SH,SW). Opcodes (4): SD, SB, SH, SW.
- [ ] ALL 4 — **BLOCKED-ON-#76**. SD has no preserved bytes; SB/SH/SW carry the documented BUCKET-(c) preserved-high-byte facts — need the HARD store-preserved-byte spike `MemoryBusRowsPrefixStoreSound`.

### Archetype 9 — LUI / AUIPC / JAL / JALR (U/J control flow) — NOT-STARTED
Dispatch: `NoMemOrSimple.lean`(LUI,AUIPC), `Remaining.lean`(JAL,JALR) + route variants auipc_x0 / jal_x0 (2 extra OpEnvelope arms beyond 63). Opcodes: LUI, AUIPC, JAL, JALR (+2 no-rd-write variants).
- [ ] JAL / JALR — jump-target next-PC is the cross-row residual → **BLOCKED-ON-#100**; Store-PC return-addr witness.
- [ ] LUI / AUIPC — sweep scoped them out, but the *data* effect may be constructible (LUI = imm<<12; AUIPC = pc+imm), with next-PC the usual named residual. **Reconsider — possible quick wins.**

### Archetype 10 — FENCE — NOT-STARTED (defect-gated)
Dispatch: `NoMemOrSimple.lean`(FENCE). Opcode: FENCE.
- [ ] FENCE — correctness gated by `NoKnownDefect` (FENCE carve-out), like Archetype 5c.

**Totals:** 7 R-type + 6 I-type + 3 W-type + 12 shifts + 2 unsigned-mul + 4 unsigned-div + 7 signed-M + 6 branches + 7 loads + 4 stores + 4 U/J + 1 FENCE = **63 canonical opcodes** across 10 dispatch families. **DONE: 28** (7 R + 6 I + 3 W + 12 shifts). **Remaining: 35** (13 M-ext + 6 branches + 7 loads + 4 stores + 4 U/J + 1 FENCE).

---

## Cross-cutting status

- **AcceptedTrace / ProgramBinding infrastructure — DONE (on #99).** `AcceptedTrace` is sound (`balanced` = proof-system soundness antecedent, consumed never proven; `ProgramBinding` = the bucket-(b) decode premise). Column bridges in use: `mainOfTable`/`mainTableRowAtOrZero`, `rowAt_mainOfTable`(`_core`), `opBus_row_Main_mainOfTable`. Extractors present: `memOfTable` (pre-existing), `mainOfTable`. **`arithMulOfTable`/`arithDivOfTable` NOT yet built** (Archetype 5 — the M-ext blocker).
- **Layer-A op-bus wrappers — 5 in use** (`_sub`, `_logic`, `_compare`, `_w`, `binaryExtension shift`) + `_add` (the disjunction wrapper for ADD/ADDI). The old `exists_construction_*_from_balance` OUTER wrappers from #97 were the laundering vehicle (sourced pins via `MainRowProvenance`) and were stripped; the sound constructions source residuals as explicit top-level binders.
- **Recursive (Option X) audit gate — DONE (on #99).** The #97 baseline check was BLIND (snapshotted only top-level binders, never recursed into `ProgramBinding`/`*RowBinding`/`MainRowProvenance`). Option X: deep renderer `bin/TrustGate/TypeWalk.lean` enumerates struct fields, telescopes function-valued fields, recurses with path+visited set, emits one baseline row per LEAF field (descending only into `ZiskFv.*` structures); wired as `print-construction-binders-deep` in `bin/TrustGate/Main.lean`, generalized to a LIST of sound constructions. The deep baseline now holds 28 honest flat blocks. **Per-family sweep requirement:** the baseline must grow by EXACTLY the new family's honest binders.
- **Bucket audit + closeout docs — DONE (on #98).** `trust/envelope-burden-audit.md` reclassified Branch exec-row → bucket-(c) artifact and PC/nextPC → bucket-(b)-pending-infra for ALL opcodes. Salvage manifest `trust/p4-salvage-manifest.md` + decision record `trust/p4-construction-closeout.md` on #98. (The full evidence `RESEARCH_PR94_CLOSEOUT.md` is local-only — `docs/ai` is local-excluded — so its references in committed text dangle on GitHub.)
- **Memory portion (#76) — BLOCKED on #103 (Spike #1 NO-GO, 2026-06-16).** Loads (A7) + stores (A8) discharge `memoryTimelineConstructionEvidence`. The two HARD spikes were: (1) cross-segment whole-trace Mem assembly — **ran NO-GO**: the seam is not derivable from the live single-Mem-table ensemble → filed as foundational prerequisite **#103**; (2) store preserved-byte soundness `MemoryBusRowsPrefixStoreSound` — auto-skipped (also needs the timeline). NOTE: #76 is NOT blocked by **#100** (Mem handles INTRA-segment continuity via single-row shadow columns) — but it IS blocked by **#103**, the distinct CROSS-segment ceiling. The intra-segment machinery + `_append` glue are salvage for when #103 lands.

---

## Blockers

- **#100 (cross-row capability / Main PC handshake) — FOUNDATIONAL, OPEN, OUT of P4 sweep scope.** Live `Air.Flat.Component` evaluates each row independently (`build/clean-lean/Clean/Air/FlatComponent.lean:149-150,171-172`), so no constraint can reference row-1; `constraint_18` (PC handshake, extracted only into the dead legacy Circuit model) is unrepresentable in `trace.constraints`. Blocks discharging **EVERY** opcode's next-PC (sequential pc+4 AND branch/jump targets) — surfaces in every sound construction as the explicit residual `h_nextPC_matches`. Two candidate fixes (rotation accessor vs shadow-witness columns); likely its own endgame phase. Distinct from #76.
- **#101 (Binary-EQ 8-byte aggregation lemma) — MODERATE, OPEN.** No `binary_eq_chunks_eq_bv_eq_of_wf` (flag=1 ↔ a==b over 64 bits); templated by the proven `binary_lt_chunks_eq_bv_slt_of_wf`. Needed (with #100) before BEQ/BNE.
- **#76 (discharge h_memory_timeline from the Mem AIR) — OPEN, now itself BLOCKED on #103.** Blocks all loads (A7) + stores (A8). Plan `PLAN_ENDGAME_P4_MEMORY.md` written; Spike #1 (the gating cross-segment seam) ran **NO-GO** (2026-06-16) — the whole-trace timeline is not derivable from the live single-Mem-table ensemble. #76's intra-segment machinery is salvage for when #103 lands.
- **#103 (cross-segment Mem capability) — FOUNDATIONAL, OPEN, NEW (2026-06-16).** The Mem-side analogue of #100's cross-row ceiling: the live `fullRv64imEnsemble` has one Mem table + a `MemBus` channel (`Guarantees := True`) and encodes the segment-continuation permutation accumulator as per-row `assertZero` constraints, not a balanced channel — so the cross-segment seam `seg0.segment_last_* = seg1.previous_segment_*` has no home (map-level seam PROVED false; weaker `SeamColumnEquality` not derivable). Fix (well-founded): make the direct accumulator a real segment-continuation permutation channel + prove its global balance → seam via hash injectivity. **Blocks #76 (hence all loads/stores).**

> **UNIFYING CEILING (2026-06-16):** #100 (cross-ROW, Main PC) and #103 (cross-SEGMENT, Mem) are the SAME limitation — the live single-table / per-row Clean ensemble cannot express a cross-X GLOBAL balance. A single foundational "cross-X ensemble capability" effort could unblock branches + all next-PC (#100) AND loads/stores (#103). #101 (Binary-EQ) is separate/smaller.
- **Exec-bus artifacts** (`h_exec_len`/`h_e0_mult`/`h_e1_mult`/`execRow`) — bucket-(c) foreign `bus_effect`/ExecutionBusEntry bookkeeping (ZisK has only OpBus/ROM/MemBus). A permanent named residual until the tracked P6-style `bus_effect` retirement; not a per-family blocker.
- **Signed-arith / FENCE** — correctness permanently gated by `NoKnownDefect` until the patched ZisK release.
- **Anti-vacuity guard (every sweep family):** `execRow` MUST be a genuine ∀-binder — hard-coding `[]` makes the exec hypotheses contradictory/vacuous (caught + fixed in the SUB spike).

### Open issues (all OPEN)
#61 (umbrella "Close the OpEnvelope construction gap"); #74 (real-trace instantiation, → P5); #76 (memory timeline); #100 (cross-row Main-PC, #61 child); #101 (Binary-EQ aggregation, #61 child). No closeout issue is closed (the stack is unmerged).

### PRs — ALL MERGED / closed (2026-06-16, squash merges)
- **PR #98** — docs(trust): audit reclassification + decision record + salvage manifest. **MERGED** (`2854b81b`).
- **PR #99** — strip the relabel + the SPINE (SUB/AND) + the 21-family READY front + the recursive Option-X gate. **MERGED** (`effef9e6`); superseded #94/#97.
- **PR #102** — NEEDS-WORK families ADD/ADDI + ADDW/SUBW/ADDIW (rebased onto main, retargeted base→main). **MERGED** (`eb19cc8f`).
- **PR #94 / #97** (the laundering stack) — **CLOSED as superseded** (not merged).

Branches `endgame-p4-*` / `p4-*` and the `.worktrees/*` are no longer needed (the salvage is in `main`) — deletion left to Cody. `p4-sub-spike` holds the throwaway SUB spike.

---

## How to read progress going forward

0. **The full nested structure (campaign → P4 → streams → prereqs/XCAP) is the navigation map at `ENDGAME_ROADMAP.md` §0.** This metaplan is the **P4 (L2) index**; the roadmap §0 map situates P4 within the whole DAG. Read it if you've lost the thread.
1. Start at **`STATUS.md`** (repo root) — current state, the 30/63 count, the merges (#98/#99/#102 + #106), and what's next.
2. The umbrella issue is **#61**; prerequisite children **#100** (cross-row), **#101** (Binary-EQ), **#103** (cross-segment Mem); **#76** the memory blocker; **#74** the P5 real-trace instantiation.
3. Plans: `archive/PLAN_ENDGAME_P4_SPINE.md` + `archive/PLAN_ENDGAME_P4_SWEEP.md` (DONE/merged — infra + §2 template + §4 invariants + the 28-family sweep); **active**: `PLAN_ENDGAME_P4_MEMORY.md` (#76, rewritten 2026-06-17), `PLAN_ENDGAME_XCAP.md` (#100+#103 cross-X capability, incl. #101) + `PLAN_ENDGAME_P4_103.md` (#103 landing checklist + dead-end table), `PLAN_ENDGAME_AENEAS.md` (aeneasBridgeTrust); M-ext sub-plan still to be written; `ENDGAME_ROADMAP.md` situates P4 against P5 (trace-level export) and P6 (delete OpEnvelope).
4. **The single per-family progress signal** is the deep audit baseline diff: a sound new family grows `trust/generated/baseline-construction-theorem-binders.txt` by EXACTLY its honest top-level binders (no `*RowBinding`/`MainRowProvenance` leaf). Any net-zero or growing-with-records diff is laundering, not progress.
