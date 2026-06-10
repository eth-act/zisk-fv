# Plan: Discharge `LoadPromises.mem_read`

Supersedes `PLAN_MEMORY_TRUST_GAP.md` and `PLAN_MEMORY_TRUST_GAP_CLOSURE.md`
(both live only on the `memory-trust-gap` branch). This plan restates the goal
against current `main` (post PR #62/#63) and salvages the durable pieces of
`.worktrees/memory-trust-gap` while scrapping its wrapper stack.

## Assessment of the `memory-trust-gap` branch

Direct content diff vs current `origin/main`: 80 files, +21,860 / −1,024.

**Durable (salvage):**

| Piece | Size | What it is |
|---|---|---|
| `ZiskFv/ZiskCircuit/MemTrace.lean` | +1,085 | Byte-addressed replay core: `MemEvent`, `replayStoreEvent`, `replayEvents`, `TraceReplaySound`, prefix-cursor projection (`readEventReplayAgreement_of_trace_sound`), `MemoryBusRowsPrefixReadSound`, `byte_facts_of_event_agreement`. Real induction proofs, `OpEnvelope`-free. |
| `ZiskFv/Airs/Mem.lean` additions | +970 | Mem AIR machinery: `SegmentColumns`, `previous_row_step`, `delta_step`/`delta_addr`, `segment_every_row` — the generated constraints 0–23 bundled for ordering/continuity proofs. |
| `tools/pil-extract` Mem changes | ~126 lines | Narrow extractor extension exposing the Mem segment/global constraints the above consumes. |
| `ZiskFv/AirsClean/Mem/TraceSpec.lean` (targets only) | part of +650 | `GeneratedMemRows`, `GeneratedMemRowOrderFacts` (nodup + chronological), `GeneratedMemReplayFacts` (initialMemory + prefixReadSound + initialAgreement) — correct statements of the proof obligations. |
| `FullEnsemble/Balance.lean` projections | part of +2,133 | `mem*ReplayEntriesOfRow`, active-selector gating, dual-row projection, `exists_mem_table_of_fullRv64im_witness` — table-side projection lemmas from the full-ensemble witness. |
| `MemModel.lean` re-theoremed | +120 | `mem_load_correct_of_provider_row` consuming `MemoryTraceAgreement` instead of 8 raw byte facts; byte-address row matching (`ptr = addr * 8` fix, dropping the legacy `mem.addr = e.ptr` pin). |

**Scrap (do not port):**

- The `AcceptedFullExecutionMemory*` family in `Compliance/OpEnvelope.lean`
  (+11,369) and `Compliance.lean` (+1,657): dozens of structures named by their
  provenance chain (`...ActiveReplayRowSplitTraceEnvelopeStateSelectionSourceAtEnvelope`)
  plus pairwise repackaging functions. Every one of them re-carries the same
  unproven leaf fields. Zero proof content.
- `AcceptedMemTrace`'s vestigial `storeReplaySound / eventOrderingSound /
  segmentCarrySound / dualEventsSound : Prop` placeholder fields.
- The branch's trust-ledger/docs churn (diverged baselines, old plan files).
- Compatibility constructors translating between equivalent evidence packages.

**Bottom line.** The branch proved the replay *core* and built the Mem AIR
*vocabulary*, but the four hard leaves are still assumed as structure fields:
(1) Mem-row order facts, (2) prefix-read soundness, (3) initial-memory
agreement, (4) selected-load prefix-state equality. The 13k-line wrapper stack
only renamed and re-routed them. (1) and (2) are provable from the Mem AIR;
(3) and (4) are the irreducible Sail-timeline boundary until a whole-execution
induction exists.

## Goal and trust decomposition

Discharge the **promise hypothesis** `LoadPromises.mem_read : LoadByteAgreement
state e1` (trust class "Memory load byte agreement" in `trust/trusted-base.md`).

Today `mem_read` is a per-load byte oracle: the constructor of any load
`OpEnvelope` arm asserts, with no provenance, that the circuit's load entry
bytes equal Sail memory. The **promise discharge** splits it into:

- **Proved (circuit side):** every read event in the accepted Mem trace
  returns the last value written at that address — derived from the extracted
  Mem AIR continuity/ordering constraints (same-address value carry, write
  update, segment carry, step ordering, dual rows). This is
  `MemoryBusRowsPrefixReadSound` for the concrete accepted table.
- **Residual (one narrow visible boundary):** Sail memory at the selected load
  equals the replay of the prior accepted events from an initial memory that
  agrees with the initial Sail state — i.e. leaves (3)+(4). Stated **once,
  globally**, as a visible hypothesis on `zisk_riscv_compliant_program_bus` in
  the established `h_bridge : env.aeneasBridgeTrust` idiom. No new axiom; the
  global project-axiom closure stays at 0.

This is a genuine shrink: the trusted content drops from "arbitrary bytes per
load" to "the Mem trace is the execution's memory timeline", with all circuit
semantics proved. Full closure of the residual boundary is a future
whole-execution-induction milestone, explicitly out of scope here.

## Architecture rules (guardrails against re-derailing)

1. **One global memory-evidence hypothesis.** A single
   `MemoryTimelineEvidence`-shaped object (working name; final name fixed in
   Phase C) appears once on the global theorem. No per-opcode memory source
   objects on `OpEnvelope`; load arms *consume* the global object, they do not
   carry memory evidence in constructor fields.
2. **No provenance-chain names.** Any new structure whose name concatenates
   more than two evidence stages is a smell; stop and restate.
3. **Hard budget:** `Compliance/OpEnvelope.lean` may grow by at most ~300
   lines across the whole plan. If a step seems to need more, the design is
   wrong — stop and re-plan.
4. Replay core stays `OpEnvelope`-free and `Compliance`-free.
5. No new axioms. The residual boundary is a theorem hypothesis. Any deviation
   requires a prior trust-class PR per `trust/trusted-base.md` rules.
6. Canonical `equiv_<OP>` signatures do not change shape; the discharge
   happens at `LoadPromises` (field removal) and the dispatch/Compliance layer
   (derivation). **Anti-laundering metric** must hold or shrink on
   `trust/generated/baseline-hypothesis-count.txt`; the wrapper
   **caller-burden ledger** diff must be net-negative (the `mem_read` lines
   leave).

## Work plan

### Phase 0 — Setup

- [x] Create branch + worktree `mem-read-discharge` from current
      `origin/main`, manually (`git worktree add`), not via agent isolation.
- [x] Copy this plan into the worktree; point its `STATUS.md` here.
- [x] Remove completed/superseded tracked planning and work-description docs
      (`PLAN_EXPLICIT_TRUST_BOUNDARY_REPAIR.md`, `PLAN_OP_ENVELOPE_GAP.md`,
      `docs/extraction/op-envelope-gap-plan.md`) and prune `PROJECTS.md` to the
      active stream.
- [x] `lake exe cache get` before proof/build work.
- [x] `nix run .#populate`; confirm `lake build ZiskFv.Compliance` and
      `trust/scripts/check-all.sh` green before any change.

### Phase A — Port the durable core (additive only, PR 1)

- [x] Port `MemTrace.lean`, trimmed: replay semantics, `TraceReplaySound`,
      prefix-cursor projection, `MemoryBusRows{ReadWrite,PrefixRead}Sound`,
      `eventOfEntry`/`storeEventOfEntry`, `byte_facts_of_event_agreement`.
      Drop the `Accepted*` packing variants and all `: Prop` placeholder
      fields.
- [x] Port the `Airs/Mem.lean` segment/ordering machinery and the
      `tools/pil-extract` Mem extraction changes; re-run extraction (warm
      pilout — no 17 GiB rebuild) and commit the extractor change.
- [x] Port `Mem/TraceSpec.lean` reduced to the three `Generated*` obligation
      statements plus their direct consumers; no packing chains.
- [x] Port the Balance.lean replay-row projection definitions and
      active/dual-selector lemmas actually referenced by Phase B.
- [x] Verify: `lake build`, V1 gate. No boundary or baseline changes expected.

### Phase B — Prove the Mem-table side (PR 2, the hard provable part)

Target theorem: for the concrete Mem table selected by the full-ensemble
witness, the projected replay-row list satisfies `GeneratedMemRowOrderFacts`
and read events satisfy `MemoryBusRowsPrefixReadSound` — **derived from
`Valid_Mem` constraints, with no assumed soundness fields**.

- [x] Same-address value carry from continuity constraints (constraints 0–23
      bundle).
- [x] Write-update soundness (written lanes replace, untouched lanes carry).
- [x] Segment boundary carry-in/out.
- [x] Dual-row (`dual_mem = 1`) event emission ordering, primary-then-dual.
- [x] Selector gating: inactive rows emit no events.
- [ ] Nodup/order facts for cursor uniqueness.
      Partial: row-local chronological order is proved from the dual-step
      range check, and row-local `Nodup` is proved under distinct primary/dual
      timestamps. Full table `Nodup` remains open because `mem.pil` allows
      read-read dual rows with `step_dual = step`.
- [ ] **Gate A check:** if a needed constraint is not in the extracted Lean,
      extend `tools/pil-extract` narrowly for exactly that constraint — never
      add an assumed field instead.
- [ ] **Constructibility check:** every strengthened `Valid_Mem`-adjacent
      statement cites the PIL constraint it mirrors.

Known technical risk (R1): the Mem AIR orders rows by (addr, step), not
execution order. Read soundness only needs same-address predecessors, so prove
it per address group first; the bridge from addr-sorted table order to the
step-chronological event list is a separate permutation lemma. If that bridge
stalls, its statement joins the residual timeline boundary explicitly — do not
bury it in a structure field.

### Phase C — Boundary swap and discharge (PR 3)

- [ ] Define the single residual object (final name decided here; candidate
      `MemoryTimelineEvidence state`): existence of the accepted Mem-event
      trace + initial Sail agreement + selected-prefix state equality for read
      cursors — exactly leaves (3)+(4), nothing provable inside it.
- [ ] Add the one visible hypothesis to `zisk_riscv_compliant_program_bus`
      next to `h_bridge`.
- [ ] Remove `mem_read` from `LoadPromises`; in the load dispatch arms derive
      `LoadByteAgreement` = Phase B theorem + replay core + timeline
      hypothesis (`mem_load_correct_of_provider_row` consuming
      `MemoryTraceAgreement`).
- [ ] Port the `MemModel.lean` re-theoreming and the byte-address row-match
      fix (`ptr = addr * 8`); scan for legacy pins:
      `rg -n "mem_legacy_addr|mem\.addr .* = .*\.ptr" ZiskFv`.
      Partial: byte-addressed primary/dual Mem-row match predicates and Clean
      adapters are ported, and `mem_load_correct_of_provider_row` now consumes
      `MemoryTraceAgreement`; legacy pins remain to scan/migrate.
- [ ] Update the 7 load EquivCore/Wrapper files; stores untouched beyond
      shared types.
- [ ] Update `trust/trusted-base.md`: retire "Memory load byte agreement",
      add the narrower "Sail memory timeline" boundary section with its
      retirement path (whole-execution induction).
- [ ] `trust/scripts/regenerate.sh` + regenerate caller-burden; confirm the
      wrapper caller-burden diff is net-negative and hypothesis counts hold or
      shrink.
- [ ] `trust/consistency/` probe updates: the old byte-oracle witness file
      adapts to the new boundary; a false-probe must still fail to typecheck.

### Phase D — Cleanup

- [ ] Full verification: `lake build`, `check-all.sh`,
      `check-all-semantic.sh`, closure print, `nix run .#test`.
- [ ] Open PRs (1–3 may collapse into 2 if A stays small; never into 1).
- [ ] After landing: delete branch/worktree `memory-trust-gap` (ask first —
      destructive), remove its plan files from `docs/ai/PROJECTS.md` history
      notes.

## Decision gates

- **Gate A (extraction sufficiency):** checked inside Phase B per constraint;
  extraction is believed largely sufficient since the branch already extended
  the extractor.
- **Gate B (timeline):** fixed by design — the timeline is the declared
  residual boundary; no attempt to prove it in this plan.
- **Gate C (reviewability):** each PR stays a focused slice; if Phase B's diff
  outgrows review, split per constraint family.

## Anti-laundering self-check (required before declaring done)

Per `trust/README.md#anti-laundering-terms`: (a) the anti-laundering metric
shrank — hypothesis-count baseline holds/shrinks and the caller-burden ledger
diff is net-negative; (b) no new trust-ledger axiom at all; (c) the new
timeline structure and any new top-level `def` reviewed for hidden-promise
risk and marked `@[reducible]` when in doubt; (d) PR titles/bodies use the
canonical glossary terms (promise hypothesis, promise discharge, trust ledger,
caller-burden ledger, constructibility).

## Success criteria

- `LoadPromises` has no `mem_read` field; `LoadByteAgreement` is derived.
- Circuit-side replay soundness is a theorem from extracted Mem AIR
  constraints with no assumed soundness fields.
- Residual memory trust is exactly one named, visible global hypothesis,
  documented in `trust/trusted-base.md` with a retirement path.
- Global project-axiom closure remains 0.
- `Compliance/OpEnvelope.lean` net growth ≤ ~300 lines.
