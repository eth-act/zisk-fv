# RESEARCH_76 — gap map for resolving issue #76 (memory-timeline argument)

**Provenance.** Distilled from an 8-reader Understand sweep (workflow `ww7bpvgyb`,
2026-06-17) over `origin/main` (head `a5679e5b`, P4 = 30), `origin/p4-103-landing`
(head `cac77248`, the banked #103 seam capability), and salvage commit
`ffd2426d`. Raw structured output: [`_raw/76-understand-maps.json`](_raw/76-understand-maps.json).

This file is the **evidence base**. The **plan spine** that consumes it is
[`../plan/PLAN_ENDGAME_P4_MEMORY.md`](../plan/PLAN_ENDGAME_P4_MEMORY.md). Navigate
by the anchors below; drill into the raw JSON only when a section's citation is
insufficient.

## Index
- [§S. The gap in one picture](#s-synthesis) — read this first
- [§1. Obligation surface](#obligation) — what `h_memory_construction` literally is
- [§2. Existing scaffolding](#scaffolding) — how much is already built (and unwired)
- [§3. mem.pil cross-row constraints](#mempil) — the raw material
- [§4. Salvage assessment (ffd2426d)](#salvage) — already on main; do not import
- [§5. #103 cross-segment seam](#seam103) — banked capability + the scoping answer
- [§6. Ordering / linkage / load machinery](#ordering) — the exact premise loads assume
- [§7. Consumption pattern](#consumption) — the 7-load uniform integration
- [§8. Issue + plan corpus + drift](#corpus) — what's stale in the existing docs

---

<a id="s-synthesis"></a>
## §S. The gap in one picture

**Target.** `zisk_riscv_compliant_program_bus` (`ZiskFv/Compliance.lean:95`) carries
binder #5 `h_memory_construction : env.memoryTimelineConstructionEvidence`
(`:98`), which is also a **conjunct of the public conclusion** `exec_eq` (`:78`).
It is threaded into exactly **3 dispatchers** — `ldsd` (`:110`), `misc` (`:112`),
`remaining` (`:113`). `OpEnvelope.memoryTimelineConstructionEvidence`
(`OpEnvelope.lean:2384`, `@[reducible]`) = `LoadMemoryTimelineConstructionEvidence
state bus.e1` for the **7 LOAD arms** (ld/lbu/lhu/lwu/lb/lh/lw_via_static_match);
`True` for the other 56 arms (**all stores included**). #76 = derive the load
arms' evidence + remove/reduce binder #5.

**The obligation** (`OpEnvelope.lean:2346`):
```
LoadMemoryTimelineConstructionEvidence state entry :=
  ∃ initialState rows (_facts : GeneratedMemReplayFacts initialState rows) priorRows laterRows,
    rows = priorRows ++ entry :: laterRows ∧ MemoryPrefixStateAlignment initialState state priorRows
```

**Four ingredients** — `[✓]` done, `[~]` done-but-unwired, `[✗]` gap:
1. `[✓]` **traceSplit** (`rows = priorRows ++ entry :: laterRows`) — derived from
   channel balance: `Linkage.lean` `memoryBusTraceSplit_of_{primary,dual}_mem_provider_read_match`
   + `matches_memory_entry` (`Airs/MemoryBus.lean:68`).
2. `[✓]` **selectedRead** — `Linkage.lean` `selectedRead_of_load_structural_promises`.
3. `[~]` **prefixReadSound** (circuit side) — DERIVED from generated Mem AIR facts
   (PR#65): `MemoryBusRowsPrefixReadSound` (`MemTrace.lean:979`) + `_append` (`:1076`);
   packaged in `Balance.lean:8974` + the `FullWitnessMemoryTimelineEvidence`
   builders (`Balance.lean:9070-9320`). **Re-assumed at the global boundary** — must
   be *wired*, not rebuilt. The builders still take `h_stateBytesAtPrefix` as a
   parameter (they discharge only the circuit half).
4. `[✗]` **MemoryPrefixStateAlignment** (`Construction.lean:28`, `state =
   stateAfterMemoryBusRows initialState priorRows`, whole-Sail-state) + the
   `initialMemory` choice + `initialAgreement`.

**The surviving residual (non-overclaim).** `GeneratedMemReplayFacts.initialAgreement
: ReplayMemoryAgreement initialState initialMemory` (`TraceSpec.lean:58`,
whole-memory: Sail `initialState.mem` = circuit `initialMemory`) is **program/trace
boot binding, NOT derivable from `Valid_Mem`**. #76 **reduces** the premise to this;
it does **not** make the theorem premise-free. Say so in every closeout.

**The cross-segment crux.** A continuation segment's `initialMemory` is modeled
(`Balance.lean:4464` `previousSegmentInitialMemoryOfRows`) as `zeroMemoryOfRows`
seeded by one write of the segment's own `previous_segment_*` airval. Cross-segment
continuity = proving `previous_segment_value[seg k]` = the prior segment's
`segment_last_value`. In the circuit this is the `MEMORY_CONTINUATION_ID`
permutation (`mem.pil:195-241`), modeled as im_direct constraints 27–33 /
`permutation_every_row` (`Airs/Mem.lean:184-224`). **No Lean theorem yet derives the
boundary equality from it.** Three candidate routes (X seam/addChannel deep
refactor, Y native permutation, Z within-segment + residual) — see [§5](#seam103);
the route decision is the subject of the design workflow.

**Cardinal sin = vacuity.** Every claim must be tested on a *realistic multi-row,
multi-segment* trace (store-then-read same address; two-address
addr-sorted/time-reversed). The only positive witness on main
(`trust/consistency/memory_timeline_construction_witness.lean`) is **degenerate**
(one read row, `priorRows=[]`, alignment by `rfl`) — a vacuity *floor*, not evidence.

**Anti-laundering.** Metric must SHRINK (`baseline-hypothesis-count.txt` gate #7,
`baseline-caller-burden.txt` gate #8, `baseline-global-theorem-binders.txt`). Loads/
stores are on `trust/structural-unpacking-exceptions.txt` (counts allowed to grow
for *earlier* adds) — #76 must be net REMOVAL on top. Phrasing: **"0 PROJECT
(`ZiskFv.*`) axioms; Sail-translation + Lean-kernel axioms present as documented
external trust"** — never "0 axioms".

---

<a id="obligation"></a>
## §1. Obligation surface

- `zisk_riscv_compliant_program_bus` — `Compliance.lean:92-114`. Binder #5
  `h_memory_construction` (`:98`); conjunct of `exec_eq` (`:78`); consumed at
  `:110/:112/:113`. **Not** passed to divu/branch/nomem/rtype/itype/shift/add_rtypew.
- `OpEnvelope.memoryTimelineConstructionEvidence` — `OpEnvelope.lean:2383-2404`,
  `@[reducible]` (so V2 `whnfR` unfolds it; cannot hide a hypothesis behind it).
- `LoadMemoryTimelineConstructionEvidence` — `OpEnvelope.lean:2345-2357`. The
  existential above. **Deliberately does not mention `MemoryTimelineEvidence`** so
  callers cannot repackage the old residual boundary.
- `MemoryPrefixStateAlignment` — `MemTimeline/Construction.lean:26-31`. Whole-state.
  The Sail-side time-order half.
- `GeneratedMemReplayFacts` — `AirsClean/Mem/TraceSpec.lean:52-58`. `{ initialMemory ;
  prefixReadSound ; initialAgreement }`.
- `MemoryTimelineEvidence` — `MemTrace.lean:1277-1290`. The byte-localized object
  loads consume (`stateBytesAtPrefix : ReplayMemoryAgreementOnBytes ... entry.ptr`).
- `ReplayMemoryAgreementOnBytes` — `MemTrace.lean:113-118`. `∀ i<8, state.mem[addr+i]?
  = mem[addr+i]?` — what "byte-localized" means.
- Adapter chain (all proved, project-axiom-clean): `loadMemoryTimelineEvidence_of_constructionEvidence`
  (`OpEnvelope.lean:2358`) → `MemoryTimelineEvidence` → `LoadStructuralPromises.withMemoryTimelineEvidence`
  (`EquivCore/Promises/Load.lean:122`) → `LoadPromises.memory_timeline` (`:119`) → `equiv_<OP>`.
- **Consumer idiom** (identical in every load arm): `simp only
  [OpEnvelope.memoryTimelineConstructionEvidence] at h_memory_construction; rcases
  loadMemoryTimelineEvidence_of_constructionEvidence promises h_memory_construction
  with ⟨timeline⟩` (e.g. `Dispatch/LDSD.lean:57-58`). **Pure forwarding** — a
  discharge slots in with no consumer change.

---

<a id="scaffolding"></a>
## §2. Existing scaffolding (proved, mostly UNWIRED)

**Proved & complete (do not rebuild):**
- MemTimeline assembly layer `Construction/Linkage/Ordering.lean` + `MemTrace.lean`
  replay core — axiom/sorry-free; `baseline-axioms.txt` has 0 lines (memory path is
  axiom-free; #76 is *hypothesis discharge*, no TCB cleanup).
- PR#65 circuit-side `prefixReadSound` derivation —
  `acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts`
  (`Balance.lean:8974`) genuinely derives it via
  `memoryBusRowsPrefixReadSound_of_activeMemReplayRowsOfTable`.
- whole-state→byte-local weakening: `stateBytesAtPrefix_of_memoryPrefixStateAlignment`
  (`Construction.lean:33-51`).
- `FullWitnessMemoryTimelineEvidence` + `_of_rawSidecars`/`_of_rawFacts`/
  `_of_proverDataWitnessFacts` + `toMemoryTimelineEvidence` (`Balance.lean:9070-9320`).

**The orphaning (the real story):** `OpEnvelope.lean:2304-2307` is a *doc comment*
— the FullWitness path is **never used in a proof term**. The global theorem
**re-assumes** the whole `GeneratedMemReplayFacts` existentially, including the
PR#65-derivable `prefixReadSound`. So wiring the FullWitness builders WITHOUT also
deriving the Sail-side half would discharge only the circuit half (net progress
smaller than it looks). All three builders still take `h_stateBytesAtPrefix` as a
top-level parameter.

**P3 (merged #84-#87/#90/#91) was a RESHAPE, not a discharge:** it turned the opaque
`Nonempty (MemoryTimelineEvidence)` promise into the named
`memoryTimelineConstructionEvidence` existential, auditable as one line in
`baseline-global-theorem-binders.txt`. It reduced **no** memory trust.

**Disjoint from P4 construction sweep:** `baseline-construction-theorem-binders.txt`
lists 30 `construction_<op>_sound` (ALU/shift/W-ALU/LUI/AUIPC) — **zero loads, zero
memory-timeline**. #76 is untouched by P4=30.

---

<a id="mempil"></a>
## §3. mem.pil cross-row constraints → Lean (the raw material)

Pinned RV64IM Mem AIR: `RC=2, bytes=8, MEM_STEP_BITS=40, addr 29 bits,
base=0x14000000, 128 MB, large_mem + dual_mem active`. Bundled Lean form:
`segment_every_row` (`Airs/Mem.lean:247-291`, constraints 0–23 over `SegmentColumns`
+ `Valid_Mem`). All Lean forms on main, 0 project axioms / no sorry.

| Concept | PIL | Lean |
|---|---|---|
| Increment packing (THE ordering constraint) | `mem.pil:375` `l_inc + 2²²·h_inc + 1 === addr_changes·(Δaddr−Δstep)+Δstep` | clause 17; `previous_step_le_step_of_same_addr_segment_every_row` (`Airs/Mem.lean:788`) |
| addr_changes boolean / same-addr identity | `:132` / `:347,403` | clause 20; `addr_eq_previous_of_same_addr_*` |
| Step-increment within address | `:367,371,375` | `delta_step` (`:238`), monotone via `field_increment_val_eq_incrementNat` |
| First-access read-zero | `:426` `addr_changes·(1−wr)·value[i]===0` | clauses 22,24; `read_addr_change_value_{0,1}_zero_of_spec` |
| Value-carry on same-addr read | `:423` `read_same_addr·(value[i]−prev_value)===0` | clauses 21,23; `value_{0,1}_eq_previous_of_read_same_addr_*` |
| Segment-last pins | `:215/220/226` `SEGMENT_LAST·(col−segment_last_col)===0` | clauses 10-13; `segment_last_*_eq_of_next_boundary_*` |
| First-segment first-row addr-change | `:377` `is_first·SEGMENT_L1·(1−addr_changes)===0` | clause 18 |
| Distance/range (no field-wrap) | `:265-291` (16-bit chunks) | `previous_segment_addr_lt_two_pow_33_of_segment_every_row` (`:1255`) |
| **Continuation permutation** | `:195-253` `direct_update_assumes([…segment_id, previous_segment_*])` / `direct_update_proves([…segment_id+1, segment_last_*], sel:(1−is_last))` | im_direct constraints 27-33 / `permutation_every_row` (`Airs/Mem.lean:184-224, :1319-1422`) |
| segment_id | `:97` declared; `:107` `is_first·segment_id===0` only; **NO range_check** | `SegmentColumns.segment_id` |

**Sufficiency status:**
- (i) within-address addr-sorted = step-sorted: **essentially complete at adjacent-row
  level** (`Airs/Mem.lean:788` + 40-bit step range rule out wrap). Missing: the global
  fold packaging per-row facts into a sorted full-trace ordering.
- (ii) value-chain (read = last write / 0 first): per-row lemmas all exist. Missing:
  the inductive fold = `prefixReadSound` — currently *carried* not *constructed* from
  `segment_every_row`.
- (iii) cross-segment carry: pins + boundary back-refs exist; **the permutation
  soundness link is undischarged** (no theorem derives `previous_segment_value` = prior
  segment's last value from the grand-product). `segment_id`'s missing range_check
  means +1 ordering rests *solely* on this permutation — a continuity proof that
  assumes segment_id ordering without it would be **unsound**.

**Gotchas:** `previous_row_step` uses ℕ subtraction at `row-1` (`Airs/Mem.lean:233`) —
row 0 must sit on a boundary (`segment_l1 0 = 1`). The dual_mem path permits
read/read rows with **equal** timestamps (`mem.pil:65`) — ordering must use `≤`, and
`TraceSpec.lean:38-44` explicitly does **not** require `rows.Nodup`. A strict-order
assumption is unprovable.

---

<a id="salvage"></a>
## §4. Salvage (ffd2426d) — already on main; importing would REGRESS

- **Verdict:** ffd2426d is behind main; PR#65 + P3 already imported/extended every
  reusable asset. The replay core (`MemTrace.lean`), `SegmentColumns`/constraint
  bundles (`Airs/Mem.lean`), bridges (`MemAlignBridge.lean` byte-identical) are all on
  main as supersets. The salvage's time-order half was only *sketched*; main's new
  `MemTimeline/{Construction,Linkage,Ordering}.lean` are the matured form.
- **Scrap (confirmed, avoid):** `AcceptedFullExecutionMemory*` (+~11k lines,
  `OpEnvelope.lean:7629+` on ffd2426d only) and `AcceptedMemTrace` (bare-`Prop`
  placeholder fields `storeReplaySound/eventOrderingSound/…` = hidden-non-obligation,
  textbook laundering). The issue's "+13k lines to avoid" = exactly this.
- **Only salvage-unique items** (low value): chronology-*assuming* projection lemmas
  (`MemoryBusRows{EventOrdering,SegmentCarry,…}Sound`) — they punt the hard part
  (deriving chronology), which main's `Ordering.lean` now does properly. Re-deriving
  them would not reduce trust.

---

<a id="seam103"></a>
## §5. #103 cross-segment seam (banked on p4-103-landing) + the scoping answer

**Banked capability (solid):** `boot_chain_derived_generalN`
(`SeamTagChain.lean:1155`) — for any N, channel balance forces the per-segment value
seam `prev i = last j` (matched by tag) + `t(N-1)=N-1`. Kernel-only (0 PROJECT
axioms). Mechanism: `.addChannel SeamContChannel.toRaw` (`FullEnsemble.lean:145`,
NO Clean fork, NO addVm) puts the seam in `BalancedChannels` (assumed trust class,
same as MemBus); `Mem.bootComp` (`:114`) is the tag-0 verifier endpoint (analogue of
`mem.pil:253`). Raw-tuple equality (no hash-injectivity / Schwartz-Zippel).

**The fatal limitation:** route-b `memWithDualMemBus` (`Mem/Constraints.lean:270-275`)
emits the seam **per-row, ungated by SEGMENT_LAST**. A k-row segment emits k pulls +
k gated pushes → balance holds **only for one-row-per-segment** traces. The
non-vacuity witness (`SeamNonVacuity.lean` `mkFullWitness`) uses a `[v0,v1]` table
(one row per segment) + `h0:v0.is_last_segment=0`. **Vacuous on real multi-row
segments.** Do NOT merge p4-103-landing as-is.

**Deep refactor to make it real (Route X):** SEGMENT_LAST-gate the push +
SEGMENT_FIRST-gate the pull (one per segment, matching `mem.pil:215/229/232-241`) →
new MemRow selector column → re-establish balance → ripple
`ProvableStruct/size/rowAt/memOfTable/mkFullWitness` + ~145 `Balance.lean`
projections → airval↔column bridge → discharge `SegmentLastRowTie` from the segment
Spec (not as `h_tie`). **`SeamRowTie.lean` / the tie theorem do NOT exist on the
branch head** — commit `362c6e83` carrying them is **dangling** (not an ancestor of
`origin/p4-103-landing`); the plan doc's "L5 DONE" overstates.

**★ The scoping answer (decisive for #76):** cross-segment continuity is **NOT** a
deep across-all-rows replay for the byte-localized claim. `MemoryTimelineEvidence`
needs only `stateBytesAtPrefix` (8 bytes at `entry.ptr`) + `prefixReadSound` over a
**single flat row list** with one `initialMemory`. The construction builds
`AcceptedMemoryReplayEvidence` from **one segment's rows**; a continuation segment
seeds `initialMemory = previousSegmentInitialMemoryOfRows` (= zeros + one write of the
segment's own `previous_segment_*` airval). `prefixReadSound` is proved **within that
single segment** (PR#65). **The only place cross-segment is needed is to discharge
`GeneratedMemReplayFacts.initialAgreement`** — i.e. that the continuation segment's
Sail `initialState` agrees with the `previous_segment_*`-seeded `initialMemory`. The
seam value equality supplies exactly that. So cross-segment is a **bounded
per-segment-boundary initial-value lemma**, and a **byte-localized** continuation
lemma (agreement at the 8 bytes of `entry.ptr`) is *strictly simpler* than full
whole-state continuity. (`mem.pil:46-55` confirms `previous_segment_*` "contain the
value at the end of the previous segment… validated through bus".)

---

<a id="ordering"></a>
## §6. Ordering / linkage / load machinery — the exact premise loads assume

- **Per-address ordering: PROVED but INTRA-SEGMENT & UNWIRED.** `Ordering.lean`
  `same_address_read_chain_facts_of_segment_every_row` (~`:80`) — every lemma gated on
  `cols.segment_l1 row = 0` (non-boundary, within one segment). No cross-segment carry
  here. **P4 assets; counting them as progress = laundering.** Not consumed by
  `Construction.lean`'s builders.
- **Bus-linkage: PROVED.** `Linkage.lean` locates `e1` in the chronological prefix via
  `matches_memory_entry` (`Airs/MemoryBus.lean:68`, fieldwise → record equality) →
  `∃ priorRows laterRows, rows = priorRows ++ e1 :: laterRows`. The trace-split half is
  fully derivable; **not** the gap.
- **The literal premise the 7 loads assume** = `MemoryTraceAgreement state
  (eventOfEntry e1)` (`MemTrace.lean:55`): `state.mem[e1.ptr.toNat + i]? = .some
  (e1.byteAt i)` for `i=0..7`, supplied as `promises.memory_timeline.memoryTraceAgreement`,
  consumed at `Ld.lean:300/337, Lb.lean:171, Lh.lean:173, Lw.lean:186, Lbu.lean:234,
  Lhu.lean:253, Lwu.lean:256`. **This** is the "bus value = time-correct memory value"
  hypothesis #76 must derive.
- **The load DATA path never touches `state.mem`.** `LoadDerivation.lean` /
  `SextLoadBridge.lean` / `MemAlignBridge.lean` relate `byteAt e1 ↔ byteAt e2 ↔ rd`
  purely on bus bytes (grep for `state.mem` returns nothing). **#76 is the timeline
  premise, NOT load-data** — that's fully derived & project-axiom-clean already.
- **The residual reduces to (a) `MemoryPrefixStateAlignment` (Sail-side time-order) +
  (b) boot `initialAgreement`.** prefixReadSound (derived), traceSplit (derived),
  selectedRead (derived), byte-local weakening (derived) are all in place.

---

<a id="consumption"></a>
## §7. Consumption pattern — the 7-load uniform integration

- **`construction_<op>_sound` recipe** (`ConstructionLui/Auipc` = provider-free
  exemplars; `ConstructionIType` `construction_andi_sound` = bus-provider analogue
  closest to loads): hypotheses `(trace : AcceptedTrace)(binding : ProgramBinding
  trace)(i)(op_input)(operands)` + FLAT residual binders; body derives Main per-row
  Spec from `trace.spec`, obtains provider match from `trace.balanced`, assembles a
  `*Promises` record, `exact equiv_<OP>`. Register in `bin/TrustGate/Main.lean:245`.
- **No load/store construction file exists.** #76 adds `Construction{Ld,Lbu,Lhu,Lwu,Lb,Lh,Lw}`
  (+ `{Sb,Sh,Sw}` for stores) following the ITYPE template **with the MEMORY-bus
  provider** (the envelope arms already enumerate the exact provider facts:
  `h_mem_row/h_main_b_match/h_mem_sel/h_mem_wr/…`).
- **The 7 loads are UNIFORM at the timeline layer** — all take `LoadStructuralPromises`
  over `bus.e1` and consume the **same** `LoadMemoryTimelineConstructionEvidence` via
  the same adapter. The novel work is **ONE shared whole-trace artifact consumed 7×**;
  the rd-value witness `w` differs (copyb/MemAlign for LD/LBU/LHU/LWU; BinaryExtension
  for LB/LH/LW) but #76 leaves `w` untouched. Integration count = 7, not split.
- **Dispatch already built:** each load arm does `rcases … → withMemoryTimelineEvidence
  → equiv_<OP>`. #76 only swaps the caller-supplied `h_memory_construction` for a
  derivation; the timeline→promises'→equiv chain is untouched.
- **Stores are a SEPARATE obligation (Spike #2).** `True` in the premise; their
  residual is preserved-high-byte `h_m*` binders (SB:`h_m1..h_m7`, SH:`h_m2..h_m7`,
  SW:`h_m4..h_m7`, SD none) needing a NEW `MemoryBusRowsPrefixStoreSound` (absent
  everywhere). Does not consume `MemoryTimelineEvidence`. Sequence AFTER loads.

---

<a id="corpus"></a>
## §8. Issue + plan corpus + drift list

- **Issue #76** (OPEN): "Discharge `h_memory_timeline` from the Mem AIR constraints."
  Acceptance: global theorem no longer takes `h_memory_timeline` (or takes only
  structural row facts already supplied by envelope construction); baselines
  net-reduce; 0 new axioms; closure print unchanged; the timeline + two-address
  vacuity witnesses still pass; ideally a new positive witness; `nix run .#test` green.
- **`PLAN_ENDGAME_P4_MEMORY.md`** (37.7K, 2026-06-16) body: spikes + PR breakdown
  (PR-S1/S2/M1-M4). Its 2026-06-17 header records the #103 capability + the 3 deep
  prerequisites. **Partially obsolete** post the route analysis here — needs the
  rewrite this research feeds.
- **Drift to correct in the new plan:**
  1. **3 dispatch arms** (ldsd/misc/remaining), not 4. divu uses `h_known_bugs`.
  2. Binder is **`memoryTimelineConstructionEvidence`**, not `h_memory_timeline`. The
     legacy `memoryTimelineEvidence` survives only as internal adapter glue.
  3. main is **`a5679e5b` / 30-of-63**; docs say `eb19cc8f` / 28 (stale by #106).
  4. **p4-103-landing head `cac77248` STOPS at L1/L4.6**; `SeamRowTie.lean` / the L5
     tie is the **dangling** commit `362c6e83`, NOT on the branch. Plan's "L5 DONE"
     overstates.
  5. Salvage import is obsolete — reuse main.
  6. Spike #1 "NO-GO" is superseded (seam IS derivable via addChannel); the residual
     is the 3 deep consumption prerequisites, not the seam capability.
- **Cross-refs:** #100 (cross-ROW Main PC handshake) is DISTINCT — #76 is **not**
  blocked by it (Mem encodes cross-row continuity via single-row shadow columns).
  #61 is the P5 trace-export umbrella #76 feeds. #103 is the foundational prerequisite.
