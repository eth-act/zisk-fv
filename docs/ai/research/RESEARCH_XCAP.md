# RESEARCH — XCAP (cross-row #100 + cross-segment #103)

> # ⛔ CORRECTION (2026-06-17, PIL-verified) — the #100 "ADDCHANNEL" verdict below is WRONG
> The §1 route verdict ("ADDCHANNEL for #100", "#100 and #103 are the SAME mechanism") was
> reached WITHOUT checking PIL faithfulness, and is REFUTED. ZisK has no per-row `pc`-tagged
> bus: within-segment PC is a per-row polynomial constraint (`main.pil:410`, `pc_handshake`),
> cross-segment PC is a `direct_update` airval bus (`main.pil:501-529`). So **#103's
> cross-SEGMENT carry IS a bus (addChannel faithful) but #100's cross-ROW within-segment PC is
> a CONSTRAINT (addChannel FABRICATED, type-illegal on the continuation bus).** The per-row
> `PcContChannel` built for #100 (X100.0/X100.1/X100.1a) is a faithfulness dead end. The
> genuine #100 path is the per-row `pc_handshake` constraint into the live single-row component
> (the original cross-row obstruction). #103's addChannel seam is unaffected. See
> [`RESEARCH_GAP_C.md`](RESEARCH_GAP_C.md) (top banner) for the full finding.

**Provenance.** 4-reader scope+probe (workflow `wbghidb2k`, 2026-06-17) over
`origin/main` (a5679e5b), `origin/p4-103-landing` (banked #103), `spike-a-xrow` (the dead
#100 PoC). Raw: [`_raw/xcap-scope.json`](_raw/xcap-scope.json). Consumed by
[`../plan/PLAN_ENDGAME_XCAP.md`](../plan/PLAN_ENDGAME_XCAP.md).

## Index
- [§S. The unifying result](#s)
- [§1. #100 route verdict (ADDCHANNEL)](#route)
- [§2. The cross-row gap](#gap)
- [§3. #103 deep-refactor state](#xseg)
- [§4. #101 (independent)](#bineq)
- [§5. Dependency map](#deps)
- [§6. Risks](#risks)

---

<a id="s"></a>
## §S. The unifying result

**#100 and #103 are the SAME mechanism.** Both express a cross-X fact (cross-row PC
transition / cross-segment value carry) that the single-row Clean `Air.Flat.Component`
*cannot state*, by re-expressing it as **channel balance**: a new continuation channel
(`Guarantees := True`) whose rows **`.emit`** (not `.pull`/`.push`) a tagged
prev/next pair + a boot endpoint, added via **`SoundEnsemble.addChannel`** (no soundness
obligation), whose balance becomes a `BalancedChannels` conjunct and feeds the
**channel-agnostic** engine `SeamTagChain.boot_chain_derived_generalN` to force, per tag,
`pull_value = push_value`. `addVm` is **dead for both** (production Main *and* Mem require
finished channels → `reqs_disjoint_finished` fails). The `SeamTagChain` engine (banked
for #103) is reusable **verbatim** for #100.

This is the legitimate kind of discharge: the cross-X fact is **derived from the
proof-system channel-balance trust class**, not relocated to a caller premise or axiom
(0 PROJECT axioms). The cardinal risk is **vacuity** — a continuation channel emitted
per-row balances only on degenerate one-row traces.

---

<a id="route"></a>
## §1. #100 route verdict — **ADDCHANNEL** (probe `wbghidb2k`)

- **`addVm` is dead for production #100**, identically to #103. Production Main
  (`componentWithRomMemAndOpBus`, `Main/Constraints.lean:440`) is a pure consumer:
  `channelsWithRequirements := [MemBusChannel, OpBusChannel]`, both `.addFinishedChannel`'d
  by `fullRv64imEnsemble` (`FullEnsemble.lean:124-125`). `addVm`'s `reqs_disjoint_finished`
  (`Vm.lean:688`) forbids a VM table requiring a finished channel → FALSE on both.
- **Spike A (`spike-a-xrow:Spike/CrossRowVm.lean`) "GO" does NOT transfer.** It derived
  `row1.pc = row0.pc + 4` soundly — but only because it was built on
  `SoundEnsemble.empty` with **no finished OpBus/MemBus**. The vehicle is unusable in
  production; the PC math (and the `set_pc=0,flag=0 ⇒ next_pc=pc+4` specialization) is
  reusable as the row-local pin model.
- **The addChannel route:** a new `PcContChannel` (`Guarantees := True`); Main rows
  `.emit (-1) (prevPc, tag)` and `.emit (gate) (nextPc, tag+1)`; a `bootComp .emit 1
  (bootPc, tag 0)`; `channelsWithGuarantees` stays `[]` (escapes `subset_finished`);
  add via `SoundEnsemble.addChannel`; balance → `boot_chain_derived_generalN` forces
  `row(i+1).prevPc = row(i).nextPc`. **The `.emit`-not-`.pull` trick is the load-bearing
  discovery** (a both-push-and-pull chain can't be a finished channel —
  `OrderedChannel.lean:440-445`).
- **First increment:** the *real* route probe — wire `PcContChannel` into the **actual**
  `fullRv64imEnsemble` (where Main pulls finished OpBus/MemBus), specialize to a
  sequential ALU op (`set_pc=0,flag=0 ⇒ pc+4`), derive `row(i+1).pc = pc(row i)+4` from
  `BalancedChannels` on a **non-vacuous multi-row witness** (mirror #103's
  `SeamNonVacuity`/`goodBootList2`). Cheap GO/NO-GO; expect GO (proven engine, relabeled
  channel).

---

<a id="gap"></a>
## §2. The cross-row gap (#100)

- The fact: `pc(row i+1) = set_pc(i)·(c_0(i)+jmp_off1(i)) + (1-set_pc(i))·(pc(i)+jmp_off2(i))
  + flag(i)·(jmp_off1(i)-jmp_off2(i))` (PIL `main.pil:409-410`, closed form
  `pc_handshake_at`, `Main/CrossRow.lean:68`). **No nextPC column** — "next pc" *is* the
  next row's `pc`. Sequential (`set_pc=0,flag=0`) ⇒ `pc+4`.
- **Why not derivable:** (a) the live Main circuit is `Air.Flat.Component` with `Spec :=
  fun row _ _ => Spec row` — per-row, literally cannot mention `pc(row+1)`
  (`Circuit.lean:127/175`, `Spec.lean:43` docstring); (b) the PC-transition constraint
  (negative row rotation) is rendered only in the **dead legacy Extraction model**, NOT
  in `trace.constraints`.
- **Carried as a residual today:** `pc_handshake_with_next_pc` is the last conjunct of
  `branch_subset_holds`/`jump_subset_holds` (caller hyps of `Equivalence.Beq…/Jal/Jalr`);
  and as the named binder **`h_nextPC_matches`** (`(b)-pending-infra`) in all 30 P4-sound
  constructions, fed to `*Promises.nextPC_matches`.
- **What the capability must produce:** `h_nextPC_matches` derived from balance → unblocks
  sequential `pc+4` for **every** opcode + JAL/JALR + the cross-row half of the 6 branches.
- **Separate sub-bottleneck:** the per-row pin `nextPc = f(pc)` (the `constraint_18` mux,
  needed for branch/jump targets) is itself not in live `trace.constraints` — re-extracting
  it as a Main row-local constraint is **SPINE Prerequisite #2**, distinct from the
  addChannel capability and possibly the real bottleneck for branch/jump *targets*
  (sequential `pc+4` does not need it).

---

<a id="xseg"></a>
## §3. #103 deep-refactor state (cross-segment Mem)

- **Banked & solid:** `boot_chain_derived_generalN` derives the cross-segment value seam
  for any N from balance, wired to the real ensemble via `.addChannel`. 0 PROJECT axioms.
- **Vacuous-as-banked:** route-b `memWithDualMemBus` (`Mem/Constraints.lean:274-275`)
  emits **per-row**, ungated — a k-row segment emits k pulls+pushes; balances only at k=1.
- **The deep refactor** (sequencing B→A→C→D→E→F→G):
  - **B** add a SEGMENT_LAST selector column to `MemRow` (foundational enabler).
  - **A** gate the emission by it (one pull + one push per segment, matching mem.pil
    `direct_update_*`).
  - **C** re-establish the `addChannel` balance for multi-row segments; **re-prove a k≥2
    non-vacuity witness** (acceptance bar; the current `[v0,v1]` witness is degenerate).
  - **D** ripple the new column/row-shape through **146** `componentWithDualMemBus` refs +
    50 `MemRow` refs (confirmed) + the `rowAt/memOfTable/rowInputVar` projections (large,
    mechanical).
  - **E** the airval↔column bridge (`MemTimeline/Construction.lean:156/161/198`,
    `Linkage.lean:113/118/137`).
  - **F** discharge `SegmentLastRowTie` **from the segment Spec** (not as `h_tie`).
  - **G** wire into the #76 continuation `initialAgreement` (= #76 PR-76.5).
- **Recover first:** the `SeamRowTie.lean` work is on **dangling commit `362c6e83`** (NOT
  an ancestor of `p4-103-landing`) — `git branch` it off before it is GC'd. And correct
  `PLAN_ENDGAME_P4_103.md`'s "L5 DONE" overstatement.
- **#103↔#76 linkage:** the seam discharges the cross-segment seed correctness =
  `GeneratedMemReplayFacts.initialAgreement` for continuation segments = #76 PR-76.5. So
  landing the #103 deep refactor IS the cross-segment half of loads/stores.

---

<a id="bineq"></a>
## §4. #101 — Binary-EQ flag (INDEPENDENT of XCAP)

Branch next-PC needs two things: (1) the cross-row PC handshake (#100), and (2) the
branch **flag** `flag = (a==b)` — which #100 does **not** provide. #101 derives the flag:
`binary_eq_chunks_eq_bv_eq_of_wf` aggregates 8 per-byte `wf_EQ` facts into `flag=1 ↔
a==b` over 64 bits, then re-plumbs BEQ/BNE EquivCore. **Mirror the proven
`binary_lt_chunks_eq_bv_slt_of_wf` SLT structure** (EQ is simpler — conjunction of
per-byte equalities, no signed final-byte flip). Buildable now, parallel to XCAP.

---

<a id="deps"></a>
## §5. Dependency map (toward P4 = 63/63)

| Piece | Route | Unblocks |
|---|---|---|
| **#100** cross-row PC | addChannel `PcContChannel` (confirmed) | sequential `pc+4` (EVERY opcode) + JAL/JALR (2) + cross-row half of 6 branches |
| **#101** Binary-EQ | mirror SLT chunk-aggregation (independent) | BEQ/BNE flag (other half of branches) |
| **#103** cross-seg Mem | addChannel seam (banked) + deep refactor | the cross-segment seed for all 11 loads/stores (#76 PR-76.5) |
| SPINE Prereq #2 | re-extract `constraint_18` mux as a Main row constraint | branch/jump **targets** (beyond sequential pc+4) |
| M-ext, AENEAS | — | independent of XCAP |

Branches (6) need **#100 + #101 + SPINE-#2**; JAL/JALR (2) need **#100 + SPINE-#2**;
loads/stores (11) need **#103 deep refactor + #76**.

---

<a id="risks"></a>
## §6. Risks

- **R1 — #100 production blast radius (the real unknown).** Channel-level GO does NOT
  de-risk production. #103's L4.5 was BLOCKED *by build* (in-place Mem swap broke
  dispatch); Main is **higher** blast radius (referenced by all 28 construction families
  via `mainOfTable`/binding). The production wiring, not the channel math, is the wall.
- **R2 — SPINE Prereq #2 (the mux pin).** Branch/jump *targets* need `constraint_18`
  re-extracted as a Main row-local constraint — separate from the addChannel capability,
  possibly the actual bottleneck. Sequential `pc+4` is unaffected.
- **R3 — vacuity.** Every channel-level claim must be witnessed on a realistic multi-row
  (k≥2) balanced trace; #103 history: the first probe was VACUOUS.
- **R4 — dangling `362c6e83`.** Recover before it GCs.
- **R5 — anti-laundering.** The fact must stay a `BalancedChannels` conjunct (derived),
  never a new caller premise/axiom; baselines net-shrink. Phrasing: "0 PROJECT (`ZiskFv.*`)
  axioms; Sail + kernel as documented external trust."
