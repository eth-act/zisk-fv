# PLAN — Close #221: root_soundness instantiation with a real multi-row memory prefix

> **For the executing agent — read this first.** This plan is **Stream S5 of
> `PLAN_PROJECT_CLOSEOUT.md`** (the wind-down metaplan; completeness, no punts). **Its trigger is
> now MET: S1–S4 have landed; `origin/main` is `d4780eee` (#242/S4 closed).** The plan was
> originally authored 2026-07-10 against `fbe7abcb`, then reconciled 2026-07-23 against
> `d4780eee` — the "expected deltas" it was written to anticipate are now RESOLVED FACTS,
> recorded in the two blocks below and threaded through the phases. Before starting, read
> `trust/README.md#anti-laundering-terms` and the anti-laundering section of the repo `CLAUDE.md`;
> use canonical vocabulary throughout. Symbol names below are verified present on `d4780eee`;
> **line numbers must still be re-resolved at execution time** (they shifted from `fbe7abcb` and
> will shift again as main moves).

> **Certificate surface — RESOLVED against `d4780eee` (the biggest change from the original
> plan).** `AcceptedZiskTrace` (`ZiskFv/Compliance/AcceptedZiskTrace.lean:93`) is now down to:
> **params** `programLength` / `program` / `witness`; the **structural core** `constraints_hold`
> (`witness.Constraints`), `channels_balanced` (`witness.BalancedChannels`), `transitions_hold`
> (`witness.TransitionConstraints`), `cyclic_successor_transitions_hold`
> (`witness.CyclicSuccessorTransitionConstraints` — **NEW since authoring: the #243 D3 field**),
> `main_height`; and **exactly two** Mem certificates — `mem_replay_table` (guarded table
> selection: `∈ allTables ∧ component = Mem.componentWithDualMemBus ∧ 0 < length`) and
> `mem_replay_source_covers` (source correlation). **DELETED — now derived, DO NOT populate:**
> `main_step_index_fixed`, `segment_l1_fixed`, `mem_replay_constraints`, the row/segment range
> facts, and the five legacy sidecar certificate fields. Range and generated-constraint facts come
> free from the derived theorems `AcceptedZiskTrace.memReplayRowRanges` and
> `AcceptedZiskTrace.memReplayGeneratedConstraintFacts` (both off `constraints_hold`).
> **Anti-laundering caveat this shrink does NOT touch:** the concrete 2-row Mem table must still
> satisfy the *full* Mem component `Spec` on every row, because that is exactly what
> `constraints_hold` asserts for that table. The segment (`segment_every_row` 0–23), permutation
> (`permutation_every_row` 24–33), range, and logUp `gsum`/`im*` obligations are unchanged in
> substance — only the *separate AcceptedZiskTrace plumbing* for them is gone. The Phase-1 spike
> make-or-break is therefore identical to the original; the shrink lands only in Phase-2 assembly.

> **Defect surface (S4) — RESOLVED: #221's opcodes are clean.** `RowOutsideDefectRegion`
> (`ZiskFv/Compliance/TraceLevelExport/Dispatcher.lean:403`) carries the MemAlign narrow-load forge
> exclusion (`¬ Defects.MemAlignNarrowLoadLaneForge`) **only on the narrow-load arms**
> `.lbu/.lhu/.lwu/.lb/.lh/.lw`. The arms this plan uses do NOT: `.sd` and `.ld` discharge just
> `SequentialPcDomain c.<op>_input.PC`, and `.jal` discharges `MainJalRangeDomain ziskTrace i
> c.imm`. The aligned-doubleword choice (below) sidesteps S4 entirely — `.ld` is explicitly not a
> narrow-load arm. Positive confirmation the opcode choice survives S4; no new obligation.

## Context

Issue #221 (soundness, mvp; part of the #74 ladder, blocks #74) asks for the
non-degenerate-memory OPEN criterion of #74: a checked-in `root_soundness` instantiation on a
trace whose Mem provider table carries a **genuine multi-row memory timeline** — a store row then
a load row — so the load-arm memory obligation is discharged at a concrete, non-degenerate
instance instead of the empty-prefix witness in
`trust/consistency/global_theorem_instantiation_ld.lean` (old `OpEnvelope` path, `priorRows = []`).

All dependencies have landed on `origin/main`: #76 (timeline reduction), #115/#236 (concrete
`BootSegmentMemorySeed` + direct-Mem read-soundness closeout), #185 (single seed premise),
#225/#235 (register MemBus provider), #219/#220/#250 (multi-row witness machinery, the
`AddAddiSpin` pattern). #222 (trace-acquisition tooling) is NOT a blocker — hand-authored
literals with a documented regen recipe are the accepted precedent (#244/#248/#250).

**Owner rulings (2026-07-10):**
1. Sequencing: execute **after all fanout-closeout streams**. Streams 3/4 (#249, #243) derive and
   delete some `AcceptedZiskTrace` certificate fields this plan otherwise populates; #245 reshapes
   the witness surface. This plan is therefore written against the stable seams, with Phase 0
   re-orientation.
2. PR shape: **spike PR + main PR** (two stacked landings, reviewer pass on each).

## What "non-degenerate" must mean here (acceptance restated)

- The Mem table in the accepted witness is non-empty (`MutableMemPresent` holds — no vacuous
  `readSoundInputs` discharge) and carries ≥ 2 rows: a write row then a read row, same address.
- The stored value is **non-zero** (differs from `memInit` default bytes), so the load's byte
  agreement is genuinely carried by the store row, not by boot memory. Same non-vacuity
  discipline as `PLAN_ENDGAME_P4_MEMORY.md` §5 (recover via git history if purged).
- Seed fields `boot`/`step`/`placement`/`readSoundInputs` are all real (no
  `absurd h …not_mutableMemPresent` anywhere in the new witness).
- No new axioms, no `sorry`; V1 + V2 gates green; file header documents the program + regen recipe.

## Target design (concrete defaults — re-verify in Phase 0)

**Program (AMENDED by coordinator ruling 2026-07-23 — 7 instructions + spin successor row,
following the #250 `AddAddiSpin` shape; see the register-seed ruling below):**

```
pc 0:  ADDI x1, x0, 0xA0   -- x1 = 160
pc 4:  SLLI x1, x1, 24     -- x1 = 0xA0000000
pc 8:  ADDI x1, x1, 8      -- x1 = 0xA0000008
pc 12: ADDI x2, x0, 42     -- x2 = 42 (the non-zero stored value)
pc 16: SD x2, 0(x1)        -- store x2 to [x1]
pc 20: LD x3, 0(x1)        -- load [x1] into x3
pc 24: JAL x0, 0           -- self-loop spin (faithful successor row, per #248/#250 precedent)
```

- **Register-seed ruling (coordinator, 2026-07-23; supersedes the original boot-seed default,
  which Phase-1 execution falsified):** RegisterBoundary boot pulls are definitionally
  zero-valued — `bootMessageExpr`/`bootMessage`
  (`ZiskFv/AirsClean/RegisterBoundary.lean:59-86` @ `d4780eee`) pin `value_0 = value_1 = 0`
  per `mem.pil:507-508`, and the telescope forces the first register pull to equal the boot
  message (`aRegPre_eq_boot`, `RegisterMemBusBalance.lean:604`). This is FAITHFUL (ZisK boots
  registers to zero), so the fix is the in-program ADDI/SLLI preamble above — never a new
  nonzero-seed capability. All registers boot to 0 on BOTH the ZisK and Sail sides; the preamble
  computes `x1 = 0xA0000008` (byte address; Mem word addr `0x14000001`) and `x2 = 42`; `x3 = 0`
  until the LD. Avoid LUI for the address: RV64 LUI sign-extends, so `LUI 0xA0000` yields
  `0xFFFFFFFFA0000000`, outside the RAM window. Equivalent covered ALU ops may substitute if a
  constraint rejects this exact preamble — report the constraint first.
  The base address **must** be in the Mem AIR's RAM window: the segment distance
  constraints (`previous_segment_addr − 335544320 = distance_base_0 + 65536·distance_base_1`,
  `402653183 − segment_last_addr = distance_end…`, 16-bit chunk range facts) pin word addresses
  to `[0x14000000, 0x17FFFFFF]` — a small literal address is unsatisfiable. Use
  `previous_segment_addr = 0x14000000`, row addr `0x14000001` so row-0 `increment` stays in
  range (Δaddr = 1 ⇒ increment = 0).
- SD/LD are the **aligned doubleword** ops on purpose: they take the direct-Mem path
  (`busSt .e2` write row / `busLd .e1` read row), no MemAlign family involvement (through-MemAlign
  is #242's scope), and `.sd`'s `MemoryOpPlacement` arm has no RMW preserved-bytes obligation.
- Timestamps (AMENDED 2026-07-23 — SD/LD are now instruction indices 4 and 5, so the original
  store ts = 3 / load ts = 6 literals are SUPERSEDED; recompute the concrete values from the
  SD/LD Main rows' `step` columns and update the Phase-1 table's `step`/`previous_step`/
  `increment` and step-dependent logUp `im*` literals by the same scratch-script route).
  COORDINATOR DERIVATION (2026-07-23, review of the first amendment attempt — which wrongly used
  the raw indices 4/5): the Main emission timestamps are `slot + 4·main_step` with a=1, b=2, c=3
  (`ZiskFv/AirsClean/Main/Bridge.lean:165-192` @ `d4780eee`, `aMemMessage`/`bMemMessage`/
  `cMemMessage`), and `main_step` = instruction index (pinned to fixed column 1, cf.
  `AddAddiSpinWitness.lean:105,277`); this reproduces the superseded 3/6 at indices 0/1. Expected
  Mem rows therefore: SD (c-slot write, index 4) `step = 19`; LD (b-slot read, index 5)
  `step = 22`, `previous_step = 19`, `increment = 3` (unchanged from the original spike);
  `segment_last_step = 22`. Values must still be CONFIRMED by evaluating the emission
  definitions against the concrete rows, not assumed from this formula. CONFIRMED by worker0
  source evaluation 2026-07-23. COORDINATOR RULING (2026-07-23, on worker0's stop-finding that
  the in-AIR `im*`/`gsum` logUp literals are timestamp-blind at `std_alpha = 0`): NOT a
  Defect-watch signature-3 escalation. The model's step binding is tuple-level:
  `BalancedInteractions` (`build/clean-lean/Clean/Air/Balance.lean:17-26` @ `d4780eee`) filters
  interactions by exact message-array equality and cancels multiplicities per distinct tuple, so
  the Mem pull `[mem_op, ptr, timestamp, width, v0, v1]` must equal Main's push tuple exactly,
  timestamp included — the "carried by `channels_balanced`" claim above is confirmed, with no
  pairing freedom for signature 3 to exploit. The degenerate-challenge blindness of the in-AIR
  accumulator columns is expected and carries no binding; their per-random-challenge soundness
  is the ledgered lookup/permutation protocol-soundness trust class (`trust/trusted-base.md`),
  not a new gap and not a ZisK defect: the old
  `MainStepIndexFixedFacts` / `main_step_index_fixed` certificate that pinned timestamps was
  **deleted by S1**; the step values are now set directly on the concrete Main rows' `step`
  columns and on the Mem table `step` column, and must agree between Main's mem-op emission and
  the Mem row — that agreement is carried by `channels_balanced`, not a separate step
  certificate. Mem table row order = (addr, step) order =
  execution order, so the seed's order certificate is the `MemoryBusRowsReplaySafePermutation`
  **refl** constructor (`ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean:207` @
  `d4780eee` — re-resolve). Do NOT use the all-pairs
  `…of_perm_pairwise_noActiveWriteOverlap` bridge — same-address write/read pairs cannot satisfy
  pairwise no-active-write-overlap.

**Mem table (2 rows, `Mem.componentWithDualMemBus`, `sel_dual = 0` throughout to avoid the dual
lane and its selector-gated range check):**

| row | addr | step | wr | sel | value | addr_changes | read_same_addr | previous_step | increment |
|-----|------|------|----|-----|-------|--------------|----------------|---------------|-----------|
| 0 | 0x14000001 | 3 | 1 | 1 | 42 | 1 | 0 | 0 (from segment) | 0 |
| 1 | 0x14000001 | 6 | 0 | 1 | 42 | 0 | 1 | 3 | 3 |

(The `step`/`previous_step`/`increment` literals above are the superseded index-0/1 values; the
2026-07-23 amendment recomputes them at SD/LD indices 4/5 — the table structure is unchanged.)

The value carry-over constraint `read_same_addr · (value_i − previous value_i) = 0`
(`ZiskFv/Airs/Mem.lean`, `segment_every_row`) is the in-circuit store→load tie — the substantive
content of the instantiation. Segment sidecar: single segment, `is_first_segment =
is_last_segment = 1`, `segment_id = 0`, `segment_last_*` = row-1 values. Row-0 quirk:
`(is_first_segment · segment_l1 0) · (1 − addr_changes 0) = 0` forces `addr_changes 0 = 1`.

**Sail trace (amended):** pc 0/4/8/12/16/20/24; `mem`: `{}` until the SD writes (8 bytes of 42 at
0xA0000008), then unchanged; all regs boot 0, x1/x2 built by the preamble, x3 = 42 after the LD. `memInit = {}` must also equal the accepted replay evidence's
`initialMemory` (`BootSegmentReadSoundInputs.initialMemory_eq`) — check in Phase 0 how
`acceptedMemoryReplayEvidence_of_fullWitnessMemReplayBridge` computes `initialMemory` for a
first-segment table whose first row is a write, and adjust `memInit` to match if it is not `{}`.

## Execution phases

### Phase 0 — re-orientation + setup (run when fanout closeout is done)

- [x] Confirm fanout end state (RESOLVED — verify still true at execution): #220 #225 #226 #242
      #243 #245 #249 all closed; `origin/main` = `d4780eee` or later. Re-diff the then-current
      `AcceptedZiskTrace` field list against the **Certificate surface** block in the header; the
      deltas the plan was written to anticipate are now facts:
      - `AcceptedZiskTrace` = params + 5-field structural core (incl. the NEW
        `cyclic_successor_transitions_hold`) + `mem_replay_table` + `mem_replay_source_covers`
        only. `main_step_index_fixed`, `segment_l1_fixed`, `mem_replay_constraints`, and all
        row/segment range + legacy sidecar certificate fields are GONE (derived) — no work items
        for them; the derived theorems `memReplayRowRanges` / `memReplayGeneratedConstraintFacts`
        supply those facts off `constraints_hold`.
      - #245's `programLength` (ROM length) vs `numInstructions` (executed steps) split is live;
        adopt the rebased #250 `AddAddiSpin{Witness,RootSoundness}` shape verbatim as the template.
      - Re-resolve every line number in this plan (they shifted from `fbe7abcb`); the symbol names
        are all confirmed present on `d4780eee`.
- [x] Create worktree `.worktrees/issue-221-mem-prefix`, branch `issue-221-mem-prefix`, **manually
      from `origin/main`** (do not rely on agent worktree isolation — it can base off stale
      refs). `git submodule update --init zisk`; `nix run .#populate`; `lake exe cache get`
      (mandatory first command, do not skip); full `lake build ZiskFv` (needed for V2 and warm
      LSP). At most one standing watchexec lake-build watcher; subagents must not start their own.
- [x] Write the worktree's `STATUS.md`; keep this plan's checklist current at every checkpoint.

### Phase 1 — spike PR: the concrete Mem provider table (the make-or-break)

Goal: retire the only genuinely novel risk — a concrete 2-row Mem table satisfying the full
generated constraint surface — in a small, self-contained, reviewable PR.

- [x] Multi-row Mem table builder `memRowsTable` (generalize `memSingleRowTable`,
      `ZiskFv/Compliance/Instantiation/ConcreteRowReductions.lean:832` — proven but consumed by
      nothing yet) + `rowInput` / `interactionsWith_memBus` / `constraints_of_proverAssumptions`
      lemmas, mirroring the existing single-row ones.
- [x] The concrete store+load rows (table above) with per-row Spec / `ProverAssumptions`
      discharged.
- [x] Concrete segment + permutation sidecar columns satisfying the Mem component's `Spec` on
      every row (`segment_every_row` constraints 0–23, `permutation_every_row` 24–33; definitions
      in `ZiskFv/Airs/Mem.lean`, structures in
      `ZiskFv/AirsClean/FullEnsemble/Balance/TableProjections.lean`) plus the range facts.
      **RESOLVED (post-S1–S4):** these are no longer separate `AcceptedZiskTrace` certificate
      fields — you discharge them once, as part of `witness.Constraints` (= `constraints_hold`)
      for the Mem table, and the derived `AcceptedZiskTrace.memReplay{RowRanges,
      GeneratedConstraintFacts}` theorems then read the range/generated-constraint facts back off
      `constraints_hold` for free. The *content* is unchanged — a 2-row table still has to satisfy
      the full generated surface — so this remains the spike's make-or-break. The logUp columns
      (`gsum`, `im_0`, `im_1`, `im_direct_0..5`)
      are solvable row-by-row once challenge values (`std_alpha`, `std_gamma`) are chosen with
      non-zero denominators: each constraint has shape `im · D + 1 = 0` ⇒ `im = −D⁻¹`. Compute the
      Goldilocks inverse literals with a throwaway scratch script (outside the TCB, pasted as
      literals — #222's philosophy), check in Lean by `decide`/`norm_num`. If a single equation
      resists `decide`, `native_decide` is acceptable only inside `trust/consistency/`
      (precedent: `load_byte_agreement_witness.lean`).
- [x] MemBus provider emission lemmas for the two rows (`memBusInteraction` with
      `mem_op = wr + 1`, `ptr = addr·8`, `width = 8`, mult `sel`), in the exact shape the Phase-2
      balance proof will consume.
- [x] Optional gate hook: a `trust/consistency/` constructibility witness (`#print axioms` guard)
      so the spike lands verified before the main PR
      (`trust/consistency/memory_prefix_sd_ld_mem_table.lean`, wired into V2).
- [ ] Exit: focused `lake build` of the new modules + V1 green; PR opened, reviewer pass, merge.
      **If the sidecar constraints are NOT satisfiable at a 2-row table** (constraint misread,
      unexpected fixed-column coupling), STOP and report — that is a finding about the extracted
      constraint model, not a reason to weaken `Valid_Mem` (anti-laundering refusal #4,
      constructibility).

Checkpoint (2026-07-23, coordinator-verified): Phase 1 is built and fully gated (focused builds,
full `lake build ZiskFv`, V1, V2 incl. the new constructibility witness, `nix run .#test`) and
open UNMERGED as PR #290 (`issue-221-mem-prefix` @ `0a4b2f74`) — the 2-row table satisfies the
full generated Mem surface, so the make-or-break passed. Phase-2 construction then exposed the
register-seed blocker resolved by the 2026-07-23 ruling above; the spike's step-dependent
literals must be recomputed at SD/LD indices 4/5 and PR #290 amended in place before its
reviewer pass. Two narrow statement-preserving repairs to `origin/main` files ride in the PR
(MemBusRowBridges `set_option` placement + proof normalization; BootSegmentMemorySeed
width-conditional range-fact form) — coordinator-reviewed, no obligation change.

### Phase 2 — main PR: the SD/LD/JAL witness + root_soundness application (closes #221)

New files following the #250 naming: `ZiskFv/Compliance/SdLdSpinWitness.lean`,
`ZiskFv/Compliance/SdLdSpinRootSoundness.lean`,
`trust/consistency/root_soundness_instantiation_sd_ld_spin.lean` (small gate hook), plus the
`trust/scripts/check-all-semantic.sh` entry (mirror #250's wiring).

- [x] **Main rows** (8, AMENDED 2026-07-23: ADDI, SLLI, ADDI, ADDI, SD, LD, JAL, JAL-successor)
      — DONE (worker commits `3635944a` rows/histories, `8c622109` program tables, `ff80e59f`
      prover assumptions, `1637f975` table constraints + 8 PC handshakes; coordinator-approved):
      ROM program rows + `RomFlagBits` for SD
      (`a_src_reg`, `b_src_reg`, `store_ind` — CORRECTED 2026-07-23 from the original `store_mem`
      transcription error on worker0 escalation: binding `RowDataArithMem.Decode_sd` requires
      `store_ind = 1` and pinned riscv2zisk `store_op_typed` agrees) and LD (`a_src_reg`,
      `b_src_ind`, `ind_width = 8`,
      `store_reg`) + free columns incl. register prev-step pins; `ProverAssumptions`
      (`MainRomExecKind.Coherent`, `MainRomSourceGuard`, `MainRomAddressGuard`) per row;
      `pcHandshakeBetween` transitions. Pattern: `AddAddiSpinWitness.lean:30-201`.
      COORDINATOR RULING on encoding sources (2026-07-23, on worker0 escalation): the BINDING
      template for each ROM row's op constant, flag bits, and immediate-field placement is the
      shape consumed by that opcode's dispatcher/EquivCore arm — `root_soundness` must apply at
      every index, so rows must instantiate exactly those shapes with the concrete
      (rs1, rd, imm) literals. Concretely: ADDI = the `AddAddiSpinWitness` ADDI shape with
      nonzero `b_offset_imm0` literals; SLLI = the existing P4 shift-construction shape
      (#98/#99/#102 sweep) at imm 24; SD/LD = the flag bits above + op/field placement from the
      `.sd`/`.ld` arms (`ConstructionStore.lean`/`ConstructionLoad.lean` + their EquivCore
      shapes). The pinned `zisk` submodule transpiler (riscv2zisk) is APPROVED as a read-only
      cross-check for these 7 instructions; any discrepancy vs the shape instantiation is a
      STOP-and-report (Defect-watch signature 2 — ROM rows enabling wrong semantics). Raw 32-bit
      instruction words are NOT to be introduced: decoder pins are standalone (#160) and
      `root_soundness` does not consume raw words; assemble one only if an already-consumed fact
      requires it. No new binders/assumptions to make a row acceptable — if a shape cannot take
      the concrete immediates, report before adapting.
- [x] **RegisterBoundary rows** — DONE (`39e4beb9` closes all three telescopes + proves the SD
      ts-19 / LD ts-22 messages equal the Phase-1 Mem provider tuples; full 31-register table,
      x1/x2/x3 live, x4–x31 idle; coordinator-approved) for x1/x2/x3 (zero-valued boot pulls per the 2026-07-23 ruling,
      reload push with final values, timestamp telescope across the preamble writes — x1 is
      written three times, x2 once, before the SD) + idle rows — the #250 N-row telescoping
      combinator.
- [x] **EnsembleWitness** via the canonical 14-slot list with the Mem slot = the Phase-1 table
      (first-ever non-empty Mem slot in an accepted trace); `Constraints`,
      `TransitionConstraints`, uniform widths. Pattern: `AddAddiSpinWitness.lean:213-330`.
      DONE (`19dd10f3` assembly, `63f52212` all-14-table constraints at uniform `sdLdMemData`,
      `33895423` transitions + cyclic successor; coordinator-approved). CORRECTION 2026-07-24
      (worker stop-and-report, approved): channel enumeration showed Mem is live on bus 103, so
      slot 7 is a live 8-row SpecifiedRangesSlice provider (`7c368e7a`, multiplicities 0×4 /
      65534×2 / 1023×2 matching the two Mem rows' pulls) — six live slots, not five; Binary
      providers for the 4 external ALU rows ride in `85ae3918`/`72a9ad05`/`2c39c0a4`.
- [x] **BalancedChannels**: COMPLETE 2026-07-27 (`54be7a27`, independently reviewed) —
      SpecifiedRangesSlice, MemAlignRange,
      MemAlignRom balanced (`7c368e7a`); exact OpBus enumeration/balance kernel-checked
      (`8631ffef`; SD/LD confirmed internal copyb-class, the 4 external ALU rows cancel their
      Binary providers). MemBus is the live front: SD/LD provider pairs + x1/x2/x3 telescopes
      are separately balanced kernels with selector-zero traffic isolated as a balanced
      residual; first aggregate close via brute finite enumeration blew the heartbeat budget
      and is being replaced by the structured permutation into those five pieces. Aggregate
      five-channel theorem NOT yet claimed.
      **COORDINATOR RULING 2026-07-26 (on worker0's second MemBus stop-report, root cause
      verified by coordinator reading the uncommitted draft):** the blocker is proof
      engineering, NOT a defect signal and NOT a scope question. `Air.Flat.Interaction` has
      no `DecidableEq` — its `RawChannel` carries `Prop`-valued fields, stated outright at
      `EnsembleWitnessBuilder.lean:29-33`. Two constructs in the draft each need exactly that
      instance and are therefore dead: (a) proving the nonzero-filter list equation by
      `decide` (it is a *computation* over an explicit cons-list — reduce it, since the
      predicate on `mult` is decidable via `DecidableEq FGL`); (b) `List.perm_iff_count`
      under `classical` (the instance exists but is noncomputable, so `simp` can never
      evaluate the counts). Approved technique: build the permutation structurally, exactly
      as `AddAddiSpinWitness.lean:1054-1087` (`List.perm_append_comm` / `List.Perm.append` /
      `List.Perm.refl` / `List.Perm.trans`, closed by `balancedInteractions_of_perm`), using
      `List.perm_middle` to extract the non-adjacent SD/LD partners from the chronological
      list — linear in list length, not an enumeration. Approved fallback stands:
      `balancedInteractions_of_present`, which works precisely because `present : List
      (Array FGL)` and `Array FGL` *does* have `DecidableEq` — the undecidable object is
      `Interaction`, never the message. Standing rule for this stream: never `decide` at
      `Interaction` type; trust Lake over warm LSP on this file.
      **CORRECTION 2026-07-26 (worker stop-and-report on carrying out the above; verified by
      coordinator at source):** the "five kernels + selector-zero residual" decomposition —
      inherited from the Phase-2 predecessor and restated in coordinator dispatches #172/#175/
      #186 without being checked — is **incomplete**. `boundaryInteractions row =
      [emittedPulledValue (bootMessage row), MemBusChannel.pushedValue (reloadMessage row)]`
      (`RegisterMemBusBalance.lean:371-374`) is a −1 pull and a +1 push, so the 28 idle
      registers (x4..x31; x1/x2/x3 are live here) contribute **56 nonzero-mult interactions**,
      not zero residual. Root of the error: the docstring at `RegisterMemBusBalance.lean:376`
      calls each idle row a "self-balancing boot/reload **zero pair**", where "zero" means the
      pair *sums* to zero — not that the mults are zero. Corrected decomposition is **six
      kernels**: x1/x2/x3 telescopes, SD provider pair, LD provider pair, and an
      idle-boundary paired kernel (any genuinely zero-mult residual may now be empty).
      Note `idleBoundaryInteractions` (`RegisterMemBusBalance.lean:377`) is **not reusable**
      here — it hardcodes the AddAddi layout `(List.range 30)` / `i + 2` (x2..x31 idle, x1
      alone live). Build an SD/LD-specific 28/`i + 4` message list on the shared generic
      `pairedInteraction(s)` + `pairedInteractions_balanced`
      (`RegisterMemBusBalance.lean:70/74/112/116`), following
      `AddAddiSpinWitness.lean:1094-1119` and folding in by permutation as at `:1467-1489`.
      NOT a defect-watch hit: our own witness-assembly bookkeeping, cancelling both
      semantically and per-message; adding the omitted traffic strengthens the accounting.
      **CORRECTION 2026-07-27 (coordinator + independent reviewer):** the first corrected
      chronological list still omitted seven live Main interactions: `mainAMemInteraction` for
      SLLI, ADDI-x1+8, SD, and LD; `mainBMemInteraction` for SD; and
      `mainCRegPreInteraction` for SLLI and ADDI-x1+8. The source-register pulls have
      multiplicity `-1`; the destination predecessor pushes have multiplicity `+1`. Each must
      follow the real six-slot Main table order. The six kernels were already exact and must
      NOT be shortened: x1/x2/x3 lengths 16/6/4 + idle 56 + SD/LD pairs 4 = 86, matching
      Boundary 62 + Main 22 + primary Mem 2. This is another hardcoded-list bookkeeping
      omission, not a ZisK defect or a change to the approved decomposition.
      Original spec: OpBus (SD/LD are internal
      copyb-class ops — expect no external-op
      provider row; verify) and MemBus via `balancedInteractions_of_present`
      (`ZiskFv/Compliance/EnsembleWitnessBuilder.lean:34`): register lanes telescope as in #250;
      the new content is Main's SD `cMemMessage` (as=2, mult +1) and LD `bMemMessage` (as=2,
      mult −1) cancelling against the Mem rows' provider emissions from Phase 1.
      Final evidence: all five ensemble channels kernel-check. MemBus accounts for exactly
      62 Boundary + 22 live Main + 2 primary Mem interactions; the inactive lanes and dual Mem
      emissions remain in the proved zero residual. The nonzero reorder is an explicit structural
      `List.Perm` proof with no `DecidableEq (Interaction FGL)`, counting, or `perm_iff_count`.
- [x] **AcceptedZiskTrace assembly** — COMPLETE 2026-07-27 (`14687a17`, independently
      reviewed): populate the current field list exactly (Certificate
      surface block), nothing more:
      - `constraints_hold : witness.Constraints`, `channels_balanced : witness.BalancedChannels`
        (from the Phase-1 table + Main/Register rows and the balance step below);
      - `transitions_hold : witness.TransitionConstraints` — Main's PC handshake is the real
        content; the MemAlign predecessor part is vacuous (no MemAlign rows in an aligned trace);
      - `cyclic_successor_transitions_hold : witness.CyclicSuccessorTransitionConstraints`
        (**NEW field — did not exist at authoring**) — likewise trivial with no MemAlign effective
        rows, but a proof term is still required; mirror however the rebased #250 witness discharges
        it;
      - `main_height` — Main covers each of the `numInstructions` steps;
      - `mem_replay_table` (guarded table-selection subtype = the Phase-1 table) and
        `mem_replay_source_covers` (component-name case-analysis pattern, `AddAddiSpinWitness.lean`).
      **Do NOT** populate any range/segment/constraint-fact certificate or `main_step_index_fixed` /
      `segment_l1_fixed` — they no longer exist; the derived theorems supply those facts.
      Final evidence: the guarded source is the real two-row slot-6 Mem table; source coverage
      exhausts the verifier plus all 14 witness slots; Main height proves all `Fin 7` execution
      indices against the eight-row table (the eighth row is the JAL successor). Focused build and
      axiom audit are green with only standard axioms.
- [x] **SailTrace + bundles** — COMPLETE 2026-07-27 through `f8c04ef0`
      (fresh focused build and root-layer independent review green) (AMENDED 2026-07-23; Sail states and all seven
      `ProgramDecode_*` bundles complete at `386274dc`/`3434f074`, focused build and
      independent review green; all seven concrete `Inputs_*` bundles committed at
      `0adc0444`, focused build and independent review green): `Claim_*` for all seven instructions
      (ADDI ×3, SLLI, SD, LD, JAL); `ProgramDecode_*` (h_prog line
      disambiguation over the 7-entry ROM); `Inputs_*` per instruction (register reads
      via `read_xreg`, pc bridges, Sail `write_mem`/`read_mem` success on the concrete states);
      `RowOutsideDefectRegion` per arm — **RESOLVED (S4):** the ALU preamble arms and `.sd`/`.ld` need only
      `SequentialPcDomain c.<op>_input.PC`, `.jal` needs `MainJalRangeDomain ziskTrace i c.imm`; no
      `¬ MemAlignNarrowLoadLaneForge` conjunct applies (aligned doubleword is not a narrow-load
      arm). Pattern: `AddAddiSpinRootSoundness.lean` throughout.
- [x] **BootSegmentMemorySeed** — COMPLETE 2026-07-27 (`39ee8090`, focused build
      and independent structural/trust review green) (the heart;
      `ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean:2286-2317`):
      - **CORRECTION 2026-07-27:** the accepted first-segment replay initial memory is
        `zeroMemoryOfRows`, concretely eight zero bytes at the touched doubleword, not `{}`.
        The Sail prestates and `initialMemory_eq` must use that explicit map.
        `rowsOf`: `0 ↦ [(busSt …).e2]`,
        `1 ↦ [(busLd …).e1]`, `_ ↦ []`;
      - `boot` := rfl-ish; `step` := `replayMemoryAfterBusRows` computation on the concrete
        states;
      - `placement` (`MemoryOpPlacement`, same file `:2241-2276`): reduce `busSt`/`busLd`
        (`ConstructionStore.lean:130` / `ConstructionLoad.lean:118`) on the concrete trace via
        the `mainRowAt` lemmas; the `.sd` arm needs only the row equation — no RMW bytes;
      - `memPresent_of_executionRows_nonempty` := the real Mem-table witness;
      - `readSoundInputs` := `BootSegmentReadSoundInputs` (same file `:252-262`):
        `initialMemory_eq` + order certificate via the **refl** constructor (accepted Mem rows =
        execution-order rows, by the Phase-1 table's construction).
- [x] **Apply `root_soundness`** — COMPLETE 2026-07-27 (`017e3c59` plus integration/performance
      correction `f8c04ef0`; fresh focused module build, semantic hook, and independent review green)
      (`ZiskFv/Soundness.lean:54-68` @ `d4780eee`, 8 args) at all 7 indices;
      per-step `StepSound` corollaries; gate hook file with `#print axioms`. The root and step
      theorems inherit the existing Sail extern axioms plus Lean's standard axioms; the accepted
      trace and channel-balance endpoints use only the standard axioms. The correction imports
      the module from `ZiskFv.lean` and replaces the pathological broad boot-seed simplification
      with an exact structural proof of the two generated replay rows.
- [x] Verify the committed stack: fresh focused root build (8780 jobs), semantic hook,
      full `lake build` (9074 jobs), V1 (`trust/scripts/check-all.sh`, 17/17), V2
      (`trust/scripts/check-all-semantic.sh`, 18/18), and `nix run .#test` (8/8) all pass;
      independent reviewer pass is approved. No trust-ledger text changes are needed because the
      hook adds no new trust class.
- [ ] Land Phase 1 PR #290 and stacked Phase 2 PR #291 after owner review/explicit merge approval;
      then close #221 with a landed-work comment documenting the program + regen recipe, and
      record the satisfied non-degenerate-memory OPEN criterion on #74.

## Stable seams this plan relies on (symbols re-verified present on origin/main @ d4780eee; re-resolve line numbers)

- `root_soundness` 8-arg signature (`ZiskFv/Soundness.lean:54-68` @ `d4780eee`), unchanged by S4;
  `StepSound` conclusion. The 8 binders: `numInstructions`, `ziskTrace : AcceptedZiskTrace`,
  `sailTrace`, `ziskStep`, `programDecodes`, `inputsAgree`, `bootSeed`, `hAvoidKnownBugs`.
- `BootSegmentMemorySeed` + `MemoryOpPlacement` + `BootSegmentReadSoundInputs` + refl-order route
  (`ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean:252-340, 2241-2317`).
- `busLd` / `busSt` (`ZiskFv/Compliance/ConstructionLoad.lean:118` /
  `ConstructionStore.lean:130`).
- `memEvidence_of_bootSeed` dispatch (`BootSegmentMemorySeed.lean:5642`); `.sd` needs placement
  only, `.ld` routes through `loadEvidence_of_seed`.
- The #250 witness pattern (`ZiskFv/Compliance/AddAddiSpin{Witness,RootSoundness}.lean`) and
  `memSingleRowTable` (`ConcreteRowReductions.lean:832`).
- Spike lemmas `rowTraceCoherence_of_uniformReplayMem` / `exec_order_fold_fin` /
  `exists_flatMap_range_split_of_singleton` (`ZiskFv/ZiskCircuit/MemTimeline/Spike.lean:431/464/492`).

## Standing constraints

Anti-laundering per AGENTS.md and `trust/README.md#anti-laundering-terms` — this work is
*constructibility* evidence: populating certificate fields concretely, never adding axioms or
weakening `Valid_<AIR>`; 0 project axioms; canonical vocabulary in PR titles/bodies/commits; one
live branch; STATUS.md + this checklist current at every checkpoint; no wall-time estimates;
reviewer pass before every merge; do not merge PRs without explicit review approval from the
owner in-thread.
