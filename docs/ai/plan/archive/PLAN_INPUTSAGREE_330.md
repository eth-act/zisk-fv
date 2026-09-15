# Close #330 (discharge `InputsAgree`) via Clean's channel-guarantee transfer

## #357 register-column derivation — merged through PR #359

- [x] Remove all four register-lane facts from every `InputsCore_<op>` structure.
- [x] Derive `RegAgree` through the combined step induction.
- [x] Derive every register-write entry range from accepted trace constraints.
- [x] Remove every introduced proof hole and `native_decide` use.
- [x] Restore all concrete root witnesses without `sorryAx`.
- [x] Record the single `regBoot` premise in the trust boundary.
- [x] Pass `lake build`, all 20 fast trust checks, and all 20 semantic trust checks.
- [x] Resolve all 13 review threads, including machine-checked MemAlign provenance.

PR #359 merged as `08db164596bfdedb3be284f7b53960d60b3bbdd8` and closed #357.
The initial `regBoot` premise replaces 116 per-row register-lane facts.

## #330 closeout

Issue #330 targeted operand-column agreement with the Sail register file.
PR #359 removed the four named register-lane field families from every operation structure.
PR #343 also completed the later PC-agreement extension.
Issue #330 closed on 2026-08-20.

## Context

`root_soundness` assumes `inputsAgree : ∀ i, InputsAgree ziskTrace sailTrace i (ziskStep i)`
(`ZiskFv/Soundness.lean`). Measured across the 63 `Inputs_<op>` structures, that premise carries
**179 field occurrences** of cross-machine agreement — `h_a_lo_t`/`h_a_hi_t` (34 each),
`h_b_lo_t`/`h_b_hi_t` (27/21), and `h_pc_bridge` (all 63) — each directly assuming a ZisK column
equals the Sail register file or PC at that step. It is the largest remaining assumed premise on the
soundness axis. Standing project principle: reduce assumptions wherever we can.

**This plan was amended mid-design.** The first approach was to hand-roll an induction — a
`BootSegmentRegisterSeed` mirroring the landed `BootSegmentMemorySeed` — carrying a register-agreement
invariant, which would have required a `SailTrace` successor relation and a `Fin n` induction at the
root. Investigation showed that Clean already proves the general theorem and **we use none of it**.
The amended plan builds on Clean instead of re-implementing it more weakly.

## The finding this plan rests on

Clean's channel layer already contains the argument, proven, no axiom:

- `RawChannel.Consistent` / `consistent_of_normal` (`build/clean-lean/Clean/Air/Balance.lean:169-217`)
  — balancedness + `Requirements` on all interactions ⟹ `Guarantees` on all interactions.
- `guarantees_of_requirements_of_requirements_of_guarantees` (`Balance.lean:276`) — the VM-transition
  cycle theorem. Supply the per-row local obligation `Guarantees(pull_i) → Requirements(push_i)` plus
  one unconditional anchor push, and it yields every pull's guarantee. **The induction over the trace
  is already done, generically.**
- Typed-channel semantics (`Clean/Circuit/Channel.lean:34-39`): one predicate per channel;
  `Guarantees` applies at `mult = -1`, `Requirements` at `mult ≠ -1`.

What we actually use:

- `grep -rn "channelsWithGuarantees" ZiskFv/` → **zero hits**. No component registers as a guarantor.
- `grep -rn "guarantees_of_requirements|RawChannel.Consistent|OrderedChannel" ZiskFv/` → **zero hits**.
- `ZiskFv/Channels/MemoryBus.lean:105` → `Guarantees _msg _data := True`. 8 of our 9 channels are `True`.

So our channels are pure bookkeeping: balance is proven but carries no semantic payload, which is
precisely why register-read soundness must be assumed rather than derived.

Two facts make the route viable, and one gives us the pattern:

- **Precedent.** `ZiskFv/Channels/SpecifiedRanges.lean:32-47` already carries a non-trivial
  `Guarantees` plus a `memDistanceMessage_guarantees_iff` bridge lemma. This is the shape to copy.
- **Balance is free.** `AcceptedZiskTrace.channels_balanced : witness.BalancedChannels` is a *field*
  (`ZiskFv/Compliance/AcceptedZiskTrace.lean:100`), so the cycle theorem's main hypothesis holds for
  every accepted trace by construction.
- **The anchor is a literal.** `global_init_mem` (`mem.pil:507-508`, call site `main.pil:535-537`)
  pushes `(mem_op=3, addr, ts=0, value=0)` — a PIL constant, not a prover-chosen witness value.
  That is exactly the unconditional push the cycle theorem needs.

**Sizing correction this implies.** The earlier estimate ("root gains a `SailTrace` successor relation
plus a hand-rolled induction, and a per-op writeback obligation across 63 arms") is likely too large.
On this route the per-row obligation `Guarantees(pull) → Requirements(push)` has the shape
`stepStrong_<op>` already has, and the root change reduces to a boot-agreement premise.

## Route decision (owner, 2026-08-07)

Investigation found that the tree **already implements counterpart-matching by hand**:
`ZiskFv/AirsClean/FullEnsemble/Balance/MemBusRowBridges.lean` (~3,000 lines) derives providers by
message equality plus component classification, and
`ActiveMainRegisterBoundaryProviderRowMatchSpec` (line 2760) has exactly the shape of
`exists_push_of_pull`'s conclusion. So `Guarantees := True` is coherent with that design rather than an
oversight, and an alternative route existed: extend that machinery to the `mem_op=3` partition
(its only current use is *negative* — `BootSegmentMemorySeed.lean:942` rules the RegisterBoundary out
as the counterpart for `as=2` rows, so the register chain is named but never walked forward).

**Owner chose the `Guarantees` rewire.** Phase 0 then established that route is **blocked by a Clean
limitation**, not by our code:

- `ChannelInteraction.Requirements` (`Clean/Circuit/Channel.lean:181`) fires at every `mult ≠ -1`,
  including `0`, and ignores `assumeGuarantees`. So every *inactive* selector-gated push would owe a
  guarantee about unconstrained witness values.
- A typed `Channel` cannot gate on multiplicity (`Channel.Guarantees` takes only `(message, data)`).
- A message-content guard cannot substitute: `aRegPreMessageExpr` hardcodes `mem_op := 3`
  (`Main/Constraints.lean:397-403`) while carrying `a_src_reg` as its multiplicity.
- Same limit one level up: `VmTables.tables_channel` (`Clean/Air/Vm.lean:52-55`) demands exactly one
  `pulled`/`pushed` pair at `∓1` per table; Main exposes six selector-gated MemBus interactions.

Extending Clean to cover conditional interactions is **scope beyond #330**, filed as **#337** with the
`gated_consistent` proof as its evidence. Per the owner's standing instruction — use Clean idiomatically
where decisions must be made, without increasing scope beyond #330 — #330 therefore proceeds at the
layer that works today: **`exists_push_of_pull` on the balanced MemBus interactions**, which is Clean's
own API and is exactly what the existing counterpart machinery is built on. `RegisterBoundary` (literal
`∓1` emissions) is the one component that already fits the idiom and can adopt `pull`/`push` directly.

## Design

Give `MemBusChannel` a real `Guarantees`; discharge `Requirements` at push sites; consume the
`Guarantees` at pull sites; let Clean's cycle theorem carry it across the trace.

The guarantee must be **guarded**, because Clean charges `Requirements` at every `mult ≠ -1` —
including `mult = 0`. Our emissions are selector-gated (`Main/Constraints.lean:436-450`,
e.g. `MemBusChannel.emit row.rom.a_src_reg (aRegPreMessageExpr row)`), so inactive rows emit at
multiplicity 0 and would otherwise owe a guarantee about a garbage message.

**A message-content guard does not work** (established 2026-08-07, before writing Lean). The obvious
guard `msg.mem_op ≠ 0` works on the *pull* side — `aMemMessageExpr.mem_op` is
`aMemOpExpr = MEMORY_LOAD_OP * a_src_mem + MEMORY_REG_OP * a_src_reg`, which is 0 when inactive — but
fails on the *push* side, which is where `Requirements` are actually owed:
`aRegPreMessageExpr` hardcodes `mem_op := 3` (`Main/Constraints.lean:397-403`) while carrying
`a_src_reg` as its multiplicity. An inactive register-preload push therefore still presents
`mem_op = 3`. The message carries no inactivity marker on the push side.

**So the guard must be on multiplicity, which a typed `Channel` cannot express**: `Channel.Guarantees`
takes only `(message, data)` (`Clean/Circuit/Channel.lean:12`), and `toRaw` derives both polarities
from it. The route is a `RawChannel` with a multiplicity-aware `Requirements`:

```
Guarantees   mult msg data := mult = -1 → P msg data
Requirements mult msg data := mult ≠ -1 → mult ≠ 0 → P msg data
```

This is *not* `Normal` (its `grts_of_reqs` is stated for all `mult ≠ -1`, so a `mult = 0` push cannot
transfer), so `consistent_of_normal` does not apply. But `exists_push_of_pull` (`Balance.lean:112`)
returns a counterpart with **`b.mult ≠ -1 ∧ b.mult ≠ 0`** — exactly the extra hypothesis the gated
form needs. So a bespoke `Consistent`-style lemma should go through by mirroring
`consistent_of_normal`'s proof (`Balance.lean:202-217`). Proving that lemma is spike item S0.1.

## Phases

### Phase 0 — spike (make-or-break; nothing else starts until it returns)

Run both questions against the existing artifact
`ZiskFv.Compliance.RegisterMemBusBalance.addX1X1X1_registerMemBus_balanced`, which already proves
`BalancedInteractions` of the `mem_op=3` partition from the real emission definitions.

- **S0.1 — the gated-consistency lemma (framework-level, no ensemble needed).** Prove, for the
  multiplicity-gated `RawChannel` above: balance + all `Requirements` ⟹ all `Guarantees`, by mirroring
  `consistent_of_normal` and feeding `exists_push_of_pull`'s `b.mult ≠ 0` into the gated
  `Requirements`. If this goes through, selector-gated emissions are solved at the framework level and
  no message-content guard is needed anywhere. If it does not, the whole route is blocked.
- **S0.2 — apply it to the register partition.** Instantiate S0.1 on
  `addX1X1X1_registerMemBus_balanced` and check the four telescoping equalities
  (`aRegPre = boot`, `aMem = bRegPre`, `bMem = cRegPre`, `cMem = reload`; `trust/trusted-base.md:516`)
  are reachable as `Guarantees` at the pulls.
- **S0.3 — report for the Sail-bridge decision (owner deferred this pending the spike).** State
  exactly what the chain delivers ZisK-internally, so the boot-agreement-premise vs derived-boot
  question can be settled on evidence.

Deliverable: throwaway branch containing either a Lean proof that the cycle theorem applies to that
witness's register partition, or a precise statement of what blocks it. **Record the go/no-go on #330.**
On NO-GO, fall back to the hand-rolled `BootSegmentRegisterSeed` — as a documented fallback, never a
silent one.

### Phase 1 — owner sign-off

Two protected-interface changes need explicit permission per `AGENTS.md`: moving
`MemBusChannel.Guarantees` off `True`, and changing `root_soundness`'s binder list. Present the Phase-0
result with both.

### Phase 2 — isolate the register partition (`mem_op = 3`)

New sibling module `ZiskFv/AirsClean/FullEnsemble/Balance/RegisterChainBridges.lean`. The existing
machinery walks an active Main pull to its provider
(`exists_mem_provider_row_msg_eq_of_active_main_table_interaction`, `MemBusRowBridges.lean:335`,
derived from `witness.BalancedChannels`) and classifies it into five branches
(`activeMainNonMutableMemProviderRowMatchSpec_branch_cases`, line 2841). Today the register branch is
only ever used *negatively* (`BootSegmentMemorySeed.lean:942` rules it out for `as = 2` rows).

Phase 2 supplies the **dual exclusions**: at `mem_op = 3`, no memory-side provider is possible, since
none can emit `mem_op = 3` —

| provider | `mem_op` | needs |
|---|---|---|
| `MemAlignReadByte` | literal `1` | nothing |
| `MemAlignByte` | `1 + is_write` | booleanity of `is_write` |
| `MemAlign` | `wr + 1` | booleanity of `wr` |
| `Mem` | `wr + 1` | booleanity of `wr` |

That leaves exactly the two register-side branches (Main-self `regPre`, `RegisterBoundary`).

### Phase 3 — walk the chain forward

From the two surviving branches, derive the telescoping equalities the balance artifact already names
(`aRegPre = boot`, `aMem = bRegPre`, `bMem = cRegPre`, `cMem = reload`;
`trust/trusted-base.md:516`), anchored at `RegisterBoundary.bootMessage`'s literal `(ts 0, value 0)`.
Reuse `registerAccessChain` / `registerTelescopingInteractions`
(`ZiskFv/Compliance/RegisterMemBusBalance.lean:144-200`) rather than restating the chain.
`RegisterBoundary` adopts `MemBusChannel.pull`/`push` here — the one component that fits Clean's idiom
without #337.

**Status (2026-08-12).** Split into two landings, both under #342.

* **Ordering — done.** PR #345 (squash `88ff6704`) models `main.pil:333-335` as the bus-102
  `RegisterStepRangeChannel` and derives the descent from balance.
  `ZiskFv/Compliance/RegisterWalk.lean` (PR #346, squash `e84e4e79`) then quantifies the walk over
  an accepted trace: `registerRead_supplied_by_boundary_or_strictly_later_row` says a register read is
  supplied either by the `RegisterBoundary` or by a Main row whose own access is strictly later, and
  `regSupplies_chain_timestamps_nodup_of_trace` therefore excludes cycles. The relation is
  slot-indexed on both sides (`RegSlot`), so mixed-slot cycles go too, and it is exhibited
  non-vacuously on the `add x1,x1,x1` witness row. No new premises: the branch split comes from
  `channels_balanced`, the supplying slot's activity from its counterpart multiplicity plus Main's
  selector booleanity, and the no-wrap bound from `mainFixedCapacity = 2^22` — **not** from an
  assumption about segment length. The chain result is stated over `IsActiveWitnessMainRow`, every
  Main row of the witness rather than only the executed prefix, so it consumes what the
  classification produces. Gates on the merged head: build 9161, V1 20/20, V2 20/20.

* **Source exclusivity — done (PR #347), and it did not need #172.** `BalancedInteractions` is
  message-exact, so a row setting two operand-source flags emits its current access at an opcode
  nothing else in the ensemble can carry, and the balance there is a nonzero multiple of a positive
  count. `main_not_a_src_mem_and_a_src_reg` and `main_aMem_pull_of_a_src_reg` give the `-1`-pull
  shape `exists_push_of_pull` consumes; `main_not_store_mem_and_store_ind_and_store_reg` is the
  `mem_op = 7` case; `slot_timestamp_ne` separates the three slots by timestamp residue, and the
  `mem_op = 5` instance built on it gives `main_b_src_mem_and_ind_zero_of_b_src_reg` and
  `main_store_mem_and_ind_zero_of_store_reg`. **All three slots are exclusive**, so every Main
  register access is a genuine `-1` pull at `mem_op = 3`. **Termination is proved** —
  `exists_boundarySuppliedSite`, by induction on `2^40 − readTimestamp`. Main-table uniqueness was
  not needed: the ensemble-level counterpart lemma already took an arbitrary witness table.

* **Termination — DONE (PR #347, `28b9304b`). #342 is closed.** The residual `main.pil:447` gap is
  now **#348**, which blocks this issue. Superseded note follows for the record.

* **The landing point — done (PR #350, on `348-boundary-anchor`).** "Ends at the boundary" left open
  *which* boundary message. It is the **reload**: `RegisterBoundary` emits boot at `-1` and the
  counterpart shape carries `mult ≠ -1`. So `reloadTimestamp` equals a real read timestamp and is
  positive (`boundary_reload_ne_boot`) — **per register**, not globally; rows for never-read
  registers keep `reloadTimestamp = 0` and do self-pair, and carry nothing.
  `boundarySuppliedAt_reload_message` returns the **whole** `MemBusMessage` equality, so
  `boundarySuppliedAt_reload_values` gives the read's values, not just its timestamp. #348 stays
  open for the unmodelled `main.pil:447` upper bound, which nothing consumes.

* **Value telescope — Phase 4.** Ordering is not agreement; carrying the value along the chain is
  below.

  **Direction, which the original plan never fixed.** The forward walk ends at the *reload*. The
  value telescope must therefore run **backwards**: from a row's register-pre push, find the *pull*
  it answers — an earlier read, or `bootMessage`'s literal `(ts 0, value 0)` — and follow that down
  a **decreasing** timestamp measure. It is the mirror of `exists_boundaryWalk_of_fuel`, not a reuse
  of it.

### Phase 4 — consume

Apply the cycle theorem on an `AcceptedZiskTrace` (balance from `channels_balanced`, anchor from
`RegisterBoundary.bootMessage`) to derive per-step register agreement, and use it to *build* the
`h_a_*_t` / `h_b_*_t` fields rather than assume them.

**RESTRUCTURED 2026-08-13 — vertical slice. Read this before doing any Phase 4 work.**

#### Why the old step list was wrong

The previous plan ordered Phase 4 by proof machinery: classify the counterpart → walk backwards →
carry the value → widen the induction → build the fields. Every one of those steps can be finished,
gated and merged **while the assumed-field count does not move.** The deliverable sat at the end, so
nothing before the end was ever forced to touch it.

That is exactly what happened. Between 2026-08-12 and 2026-08-13, eight PRs merged (#338, #339,
#345, #346, #347, #349, #350, #352) and the count went **504 → 504**. Measured, not estimated:

```
$ grep -rho 'h_[ab]_\(lo\|hi\)_t' --include='*.lean' ZiskFv/Compliance/TraceLevelExport/ | sort | uniq -c
     80 h_a_hi_t     80 h_a_lo_t     51 h_b_hi_t     82 h_b_lo_t
$ grep -rc 'h_[ab]_\(lo\|hi\)_t' --include='*.lean' ZiskFv/ | awk -F: '{s+=$2} END {print s}'
504
```

Worse, the ordering hid the error most worth catching early. This plan recorded "both halves of
Phase 4 are built" **twice**, and it was false: `exists_bootAnchored` binds `tbl / r / t` freshly, so
it says a boot-anchored slot exists *somewhere* and carries no value. A slice would have reached for
it on day one and found that out. Instead it surfaced only when the theorem was finally used.

#### The new structure: one field, one opcode, end to end

**Drive `h_a_lo_t` on ADD to zero, against the `addFaithful` witness, before generalizing anything.**
`addFaithfulPaddedRawRootSoundness` is the right target: it already instantiates `root_soundness`,
it runs one instruction, and its ADD row reads `x1`.

Every layer must exist simultaneously, in the smallest form that works:

| slice step | what it must produce | status |
|---|---|---|
| S1 | the value carried along the boot walk, for **this** row's a-slot | **DONE** (`55621f6d`) |
| S2 | `RegAgree` at step `0` only, stated and satisfied by the witness | **DONE** (`37f9ddf6`, `dcf306fe`, `0edc0e9c`) |
| S3 | `h_a_lo_t` **derived** for the ADD arm rather than taken as a field | not started — **gated on coverage, below** |
| S4 | that one field removed from `InputsCore_add`; count goes 504 → 503 | not started |

**The gate for the slice is the count, not a green build.** If `grep -rc` does not drop, the slice
did not land, whatever else was proved. **Measured 2026-08-13 after S1 + S2 + the S3 groundwork:
still 504.**

**Trap the gate springs on its own author.** The grep is over all of `ZiskFv/`, prose included. Two
docstrings written during S1/S2 quoted `h_a_lo_t` and pushed the count to **506** — the gate read as
if the slice had gone *backwards* by two fields. Fixed by rewording the prose (`36a9c9c4`), not by
touching the grep or the baseline; adjusting either would be the allowlist edit the trust rules
forbid. Anything written from here on should name these fields in words.

Work is on `330-phase4-bootwalk-path` in `/home/cody/zisk-fv/.worktrees/clean-migration-330`,
rebased onto `origin/main` `f58ccef4` so `chainedSailStates_regs_of_ne_pc` (#343 / PR #352) is
available. The stack under it is `330-phase4-value-telescope` = open PR #351.

#### What S1 landed

`bootWalk_head_value` inducts over `exists_bootWalk`'s path, so the value reaches the head rather
than sitting at the anchor: **either the head's operand column is `0`, or it is the value written by
an active c-slot the walk lands on.** The induction turns on the slot asymmetry —
`readMessage_value_eq_regPre_of_ne_c` says an a- or b-link passes the value through unchanged
(`aMemMessage` and `aRegPreMessage` carry the same columns), and it is deliberately false for `.c`,
where `cMemMessage` carries the store value and `cRegPreMessage` carries `store_reg_prev_value`.
`a_columns_of_bootWalk` states it on the columns `Inputs_<op>` talks about, and both branches name
real witness rows.

#### What S2 landed

`ZiskFv/Compliance/TraceLevelExport/RegisterFileAgreement.lean`:

* `ziskRegFile` — the ZisK register file, defined by folding **`stepChannelOutput`'s own memory
  rows**, i.e. the same entries `StepSound` hands Sail. The alternative (recursing over the Main
  table's `store_reg` flag) would need a per-opcode decode fact tying `store_reg` to each arm's
  literal `as` before the step could even be stated.
* `stepChannelOutput_memRows_shape` — all 63 arms collapse to three memory-bus shapes with literal
  multiplicities and address spaces.
* `post_regs_eq_of_stepChannelOutput` — the whole register effect of one step, one equation, every
  arm. Five `bus_effect` post-state lemmas feed it (empty, single-entry, ALU, store `as = 2` write,
  load `as = 2` read), each in its `x0` and non-`x0` branch.
* `regAgree_succ` — writeback preservation, from the above plus `chainedSailStates_regs_of_ne_pc`.

**Trap found and recorded in the source:** `reg_of_fin` is **not injective**. Its last `match` arm
is a catch-all returning `x31` and the explicit arms stop at `30`, so indices `0` and `31` collide.
`decide` caught it. `RegAgree` is stated off zero anyway, because `bus_effect` never writes a
register whose index wraps to `0`.

**Not circular, and this needs saying once:** `regAgree_succ` consumes `StepSound j`, and once the
register fields are derived from `RegAgree` instead of assumed, `StepSound j` consumes `RegAgree j`.
`RegAgree (j + 1)` needs `StepSound` only at steps `≤ j`, so it is one well-founded interleaved
induction on the step index — the skeleton Phase 7 already installed. `RegAgree` must be carried
*inside* `stepSound_of_programDecodes`, never derived afterwards from `∀ i, StepSound i`.

#### HEADLINE, RESOLVED (2026-08-16): the repair landed and the coverage argument is complete

The block below is **cleared**. `RegisterBoundary` now carries a fixed enumerated register column
(`registerBoundaryFixedColumns`, capacity 31, `reg` at row `index` fixed to `index + 1`), so
`materialized_index_unique` holds by construction and the boot anchor is unique per register. The
repair touched 34 files at 20 sites, `rawWidth` went 4 -> 3, and every checked-in witness gained
`_length` and `_enumerated` lemmas. It **reduces** prover freedom, so it cost no trust: no new
axiom, no new trust marker, V1 and V2 both green.

All four coverage steps are now proved — see the list below, with steps 3 and 4 marked DONE. Both
are **false without this repair**, which is the clearest evidence the gap was real and not
bookkeeping.

The assumed-field count is **still 504**. None of this moves the deliverable on its own; what
changed is that the fact S3 was missing now exists. S3's composition and S4's removal remain.

#### The original finding (2026-08-13), kept as the record

Not on remaining proof effort. Deriving the 116 register fields needs the register telescope's
coverage argument; coverage needs the boot-anchored slot to be unique per register; and **that is
false in the model as it stands**, because `RegisterBoundaryRow.reg` is a free witness column and
`RegisterBoundary.circuit` has `Spec := True`. Two boundary rows may carry the same `reg`. The full
measurement and the PIL citation are in the STOP-FINDING below.

So no amount of further work inside Phase 4's stated scope reaches S4. The blocking item is a
model-fidelity repair to a live AIR — give `RegisterBoundary` a fixed enumerated register column,
mirroring `main.pil:535-537` — which is a *reduction* in prover freedom and therefore costs no
trust, but touches 34 files and all 20 boundary-table construction sites including every checked-in
witness. That is a separate piece of work and needs owner sign-off on scope.

**Everything below S3 remains correct and remains the right route** once the repair lands. Nothing
in S1 or S2 depends on the gap.

#### S3 is gated on a coverage argument, and this is the finding of the slice

S1 gives "the operand column holds the value written by *a* c-slot the walk lands on". S3 needs
"…by the **last** write before this step", because that is what `ziskRegFile` records. The gap
between the two is the standard offline-memory-checking argument, and **it cannot be avoided by
restating `RegAgree`** — every reformulation tried (walk-ordered induction, timestamp-ordered
induction, per-access agreement) reduces to the same missing fact: no write to `r` occurs strictly
between the walk's link and the reading row.

Four steps close it, in order:

1. **Main-table uniqueness — DONE** (`df6a87f4`, `ZiskFv/Compliance/MainTableUniqueness.lean`).
   `main_table_unique`: exactly one witness table carries the Main component. The discriminator is
   `rawWidth`, and `ensemble_rawWidths` pins the whole profile —
   `[0, 4, 10, 16, 30, 1, 6, 17, 1, 1, 43, 44, 29, 39, 10, 41]` — so `41` occurs once, a Main table
   sits at index `15`, and any two are equal. `GeneralFormalCircuit.size_eq` plus `circuit_norm`
   reduces each width; all sixteen in one `simp only` exhausts 8M heartbeats at `isDefEq`, so they
   are separate declarations. **The widths are not pairwise distinct** (`MemAlignReadByte` and
   `BinaryAdd` are both `10`, three slices are `1`), so the argument is specific to Main.
   The assumable fallback — an `AcceptedZiskTrace` field shaped like `mem_replay_source_covers` —
   was **not** taken: Phase 4 exists to remove assumptions.
2. **Pull-uniqueness — DONE** (`1eaa27d1`). `readMessage_inj`: two active register slots carrying
   the same `mem_op = 3` read message are the same slot of the same row. An access timestamp is
   `offset + 4 * index` with `offset ∈ {1, 2, 3}` naming the slot and `index` the row, both far
   below the wrap point, so `slot_timestamp_val` moves it to `ℕ` and `omega` finishes.
   `mainRowAt_main_step` supplies `main_step = index` for *any* in-range row, not only the executed
   prefix — the walk's providers may be padding rows.
3. **Push-injectivity — DONE** (`14514ee8`, `ZiskFv/Compliance/RegisterPushCounting.lean`).
   `regPreMessage_inj`: two distinct active register slots cannot share a register-pre message.
   `memBus_memOp3_mult_trichotomy` discharges the side condition — anything outside `{0, 1}` at a
   `mem_op = 3` message is, by the classification, a Main current access or the boot pull, and
   `mem_op = 3` forces the Main slot's selector hence its `-1`. The build-up:
   `pushCount_eq_pullCount_of_balanced` is landed: at every memory-bus message whose interactions
   ride at `0`/`±1`, the push count equals the pull count. The existing balance lemma could not
   express this — `no_balanced_message_with_constant_nonzero_mult` assumes *one* constant
   multiplicity, and here the two sides carry opposite ones.
   **Positions, not values, and this is the trap:** `Interaction` is
   `⟨channel, mult, msg, _, _⟩`, so two Main rows pushing the same register-pre message produce
   **equal interaction values at different list positions**. Nothing about the values separates
   them, so every step of this argument must stay at `List.countP` level; a set-valued reading
   collapses the very case it is about.
   The push side is now complete in both halves. `two_le_countP_flatMap` separates **rows** —
   `interactionsWith` flat-maps tables and each table flat-maps rows, so emissions by two different
   rows land in different summands. `two_le_row_memBus_pushCount` separates **slots within one
   row**: Main's memory-bus emission list is six entries, the a/b/c register-pre pushes at positions
   `0`, `2`, `4` and the a/b/c current pulls at `1`, `3`, `5` (`Main/Circuit.lean:1025`). That
   second half is not optional — two slots of one row *can* carry equal register-pre messages,
   because their predecessor columns are free.
   `two_le_witness_pushCount` assembles both halves at witness level, so **the push side is done**.
   The pull side's general form is landed too: `countP_le_one_flatMap`. Note the two sides are
   proved by **opposite** arguments — the push side counts *up* (two witnesses ⇒ two positions), the
   pull side counts *down* (no message pulled twice) — so the bookkeeping does not share a lemma.
   `row_memBus_pullCount_le_one` supplies the first of `countP_le_one_flatMap`'s two hypotheses
   at the register instance (it closes with `countP_le_one_of_unique_index`; an eight-way
   `by_cases` on which current access matches does **not** close, tried and reverted).
   The second hypothesis — no two distinct rows both pull a given message — routes through
   `readMessage_inj`, but not directly: that lemma wants `IsActiveWitnessMainRow`, so first recover
   `a_src_reg = 1` from `mem_op = 3` with `regSlot_selector_of_mem_op_three`.
   **Newly found, and not in this plan before:** the witness-level pull count also has a
   `RegisterBoundary` contribution. A register-pre message whose timestamp is `0` is answered by
   the **boot** pull rather than by a Main access. Table uniqueness for it is proved
   (`registerBoundary_table_unique`, `c11b8125`) — `rawWidth 4` occurs once, so
   `table_index_of_rawWidth` covers Main and the boundary off one argument.
   `pushCount_eq_pullCount_of_balanced` then closes push-injectivity at `2 ≤ 1`. The boundary side
   closes **because of the fidelity repair** — `registerBoundaryTable_pullCount_le_one` is false
   against a free `reg` column.
4. **The merge — DONE** (`418bcabf` generic, `d95d926b` instantiated). `bootWalk_merge`: two boot
   walks that end at the same anchored slot merge, so the head of the shorter lies on the longer.
   The generic content is `mem_of_chains_getLast_eq`: reversed, both chains start at the anchor and
   each step is then **functional**, so one reversed chain is a prefix of the other. Injectivity of
   the link comes from `regPreMessage_inj_step` and determinism from `readMessage_inj`.
   Two seams were needed to connect them. `mem_of_chains_getLast_eq` wants injectivity
   *unconditionally* while `regPreMessage_inj` needs both endpoints active, so activeness is
   carried **inside** the link relation (`answersRegPre_inj_active`), and a boot walk is shown to
   be a chain for the restricted relation (`isChain_active_of_isChain`). `bootAnchoredStep_unique`
   supplies the common endpoint: `bootMessage` is determined by `reg`, every other field being a
   literal — again false without the repair.

#### STOP-FINDING: `RegisterBoundary` is weaker than its PIL source, and coverage needs the gap shut

Measured, not inferred. `ZiskFv/AirsClean/RegisterBoundary.lean`:

* `RegisterBoundaryRow` has `reg` as a **free witness column**;
* `circuit` has `Spec := fun _ _ _ => True` and asserts **no algebraic relation at all** — its
  `main` is two `MemBusChannel.emit`s and nothing else;
* so the model permits a witness with **two boundary rows carrying the same `reg`**.

The PIL does not permit that. `main.pil:535-537` emits the boot pulls from a **compile-time loop**:

```
for (int ireg = 0; ireg < REGS_IN_MAIN; ++ireg) {
    global_init_mem(sel: 1, addr: ireg + REGS_IN_MAIN_FROM, value: zeros);
}
```

`addr` is a literal per iteration and `sel` is `1` unconditionally, so ZisK has exactly
`REGS_IN_MAIN` boot pulls at fixed addresses, with no witness column for the register index.

**Why this blocks coverage.** Two boundary rows for the same register give two boot pulls at
`(3, r, 0, 0)`, so two Main rows may be boot-anchored for `r`, so `r`'s accesses may split into two
disjoint chains. The merge argument (coverage step 4) rests on the boot-anchored slot being
**unique**, and it is not, in the model as it stands. This is a *model-fidelity* gap, not a ZisK
defect: the real circuit is stronger than what we model.

**Route, and what it costs.** Strengthening `RegisterBoundary` to mirror the PIL — a fixed
enumerated register column instead of a free witness one — is the honest fix, and it is a
*reduction* in what a prover may do rather than a new assumption, so it does not trade trust away.
Source citation `main.pil:535-537` and `mem.pil:505-508`; constructibility is immediate, since the
real prover emits exactly those rows. But it is a change to a live AIR that #225's balance proofs,
the checked-in witnesses and the ensemble all consume, so it is not a local edit and it was not in
this plan's scope. **Get owner sign-off before touching it.**

**EXTRACTION EVIDENCE (2026-08-15).** The earlier citation was PIL source only. Checked at the
layer the proof actually consumes: `build/extraction/Extraction/Main.lean` carries exactly **62**
`mem_op = 3` memory-bus direct terms, at **literal addresses 1 through 31, each appearing twice** —
the boot pull and the reload push for `x1` .. `x31`. So the register index is a compile-time
constant in the generated artifact too, not only in the source. `std_direct.pil`'s
`direct_initial_checks` explains why: it rejects any expression of degree > 0 in a direct update, so
the address *cannot* be witness data.

**Repair started, checkpointed on branch `330-registerboundary-fidelity` (`1486b5c1`, TREE RED).**
`ZiskFv/AirsClean/RegisterBoundary.lean` is done and compiles: `reg` moves to component-owned fixed
data, `rawWidth` 4 → 3, `capacity` 31, `values 0 i = i + 1`. `Table.fixed_domain` then bounds the row
count at 31 for free.

**What the ripple actually is, measured.** `Table.table` materializes rows with `mapIdx`
(`FlatComponent.lean:218`), so effective rows are index-dependent. The boundary lemmas are written
in row-*value* style — pass a row, get its interactions — and must become *index* style, the way
Main uses `mainTableRowAtOrZero`. That is ~126 references in
`Instantiation/ConcreteRowReductions.lean` and ~20 in `RegisterMemBusBalance.lean`, plus each
witness supplying the new length bound. Two theorems are now false as stated, correctly so, and must
take the index: `registerBoundarySingleRowTable_rowInput` and
`registerBoundaryRowsTableOf_memBus_row` both claim the recovered row is the one the caller passed;
`reg` is now the fixed value at that index instead.

**Feasibility, checked rather than guessed (2026-08-13).** The repair is workable, and the two
things that would have made it painful are both already in our favour:

* There is a **shared builder**, `registerBoundaryRowsTableOf`
  (`Instantiation/ConcreteRowReductions.lean:1733`), so the `fixed_domain` obligation is discharged
  in one place rather than at each of the 20 sites. Today it closes vacuously because
  `fixedColumns = none`; with a fixed column it becomes a real obligation.
* The witnesses **already enumerate registers in index order**. `AddFaithfulPaddedWitness.lean:122`
  builds `addFaithfulBoundaryRowX1 :: (List.range 30).map (fun i => boundaryRowIdle (i + 2))`, so
  `reg = index + 1` holds on the nose and the fixed column would be `reg index = index + 1`
  (`REGS_IN_MAIN_FROM = 1`). Check the other witnesses build the same shape before starting.

**Corrected after opening the mechanism (same day).** "Add a fixed column" understates it. Clean's
`IndexedFixedColumns` works the way `mainFixedColumns` does (`Main/Circuit.lean:816`): the row type
keeps the field, but the **raw row encoding omits it** — `mainRawRow` leaves out `SEGMENT_L1` and
`main_step` — and the fixed schema supplies it. So the repair is a **row-encoding change**, not a
field addition:

* `registerBoundaryRowArray` currently is `(toElements row).toArray`; it would have to omit `reg`;
* `RegisterBoundary.component` gains a `fixedColumns` with `capacity` / `layout` / `values`;
* `registerBoundaryRowsTableOf`'s `raw_uniform_width` and `fixed_domain` both become real
  obligations instead of the vacuous ones they are now;
* every proof that evaluates a boundary row's environment — the #225 balance work included — has to
  keep working through the new encoding.

That is a several-hour refactor with real uncertainty, not a contained edit. It is still the right
repair and it still costs no trust; it is simply its own piece of work.

**And note the repair alone does not reach S4**: coverage step 4 (the chain merge) is still
unstarted, and S3's composition and S4's field removal follow it.
4. **The merge.** `pred` (the slot whose read answers a given register-pre push) is a partial
   injection by (3), it is deterministic by (2), and every walk terminates at the unique
   boot-anchored slot. So of two walks the one with the smaller start timestamp is a suffix of the
   other; with the descent this gives "every earlier access to `r` lies on the walk", which is the
   coverage fact S3 needs.

Only after (4) does S3's composition (`a_0 i = ziskRegFile i r`, then `RegAgree i`) go through, and
only after S3 can S4 move the count.

Only after S4 does generalization start, and it generalizes along two independent axes that should
be separate PRs: the other three lanes (`h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`) on ADD, then the
remaining 62 opcodes.

#### What the slice reuses

Nothing landed is thrown away. `exists_bootWalk` (`54ab4b9d`), the bus-102 descent (#342), the
boundary anchor (#350), `chainedSailTrace` (#352), and `RegisterWriteback.lean` are all inputs to S1
and S2. The restructure changes the *order of consumption*, not the substrate.

#### The structural fact that makes this hard

From `RegisterWriteback.lean`'s header, measured there: `bus_effect` returns `Prop × EStateM.Result`,
its `.1` accumulates exactly the register-read conditions — and `state_effect_via_channels` is
`(bus_effect …).2`. **`StepSound` discards `.1` entirely.** That is *why* these fields are assumed,
and why no amount of work on `StepSound` alone can produce them. The slice must build the ZisK side
independently and meet Sail through `RegAgree`.

#### History of this section's blocker, kept because the reasoning still binds

**The "both halves exist" claim below was wrong — it is preserved so the mistake is not repeated.**
PR #351 landed `exists_bootAnchored` / `bootAnchored_values_zero` and the backward walk (gates
9166 / 20 / 20), and the Sail half predates all of it —
`ZiskFv/Compliance/TraceLevelExport/RegisterWriteback.lean`, `regs_write_of_busEffect_ok_three` and
`regs_preserved_of_busEffect_ok_three`. What was **not** true is that the ZisK half was usable:
`exists_bootAnchored` carries no value. `exists_bootWalk` (`54ab4b9d`, branch
`330-phase4-bootwalk-path`) is the fix and is S1's input.

`SailTrace n` is `Fin n → PreSail.SequentialState` (`Compliance/SailTrace.lean:20`) — a *family* of
states with **no relation between indices**. So `RegAgree j → RegAgree (j+1)` has nothing to induct
over: `regs_write_of_busEffect_ok_three` constrains `post`, the post-state of `bus_effect` at step
`j`, while `sailTrace (j+1)` is an unrelated state.

The PC arm met exactly this and *assumed* the link: `SegmentPcChain` extends `SailRetireChain`, a
per-step `retire` law, and `SailRetireChain.lean:789` says so outright — "**This direction is why
Phase 7 is not, by itself, a logical-strength reduction, and the docstrings must not claim one.**"

The register analogue would be a `SegmentRegChain.succ`: a per-step cross-machine assumption that
`sailTrace (i+1)`'s registers are the post-state's. That is `n` per-step assumptions traded for 116
per-row ones — **the same logical strength in a different shape**, which is the swap the
anti-laundering rule forbids. It would look like a discharge and be none.

**#343 landed at the root (PR #352) and this is now unblocked** — `chainedSailStates_regs_of_ne_pc`
says the general registers at step `j + 1` are the post-state's, because retire touches `PC` and
nothing else. Do **not** open a `SegmentRegChain` premise to get around anything.

**S2 must make one design call the old plan never made: where `RegAgree` lives.**
`stepSound_of_programDecodes` deliberately kept its `sailTrace` binder, so inside it the trace is an
arbitrary family and `chainedSailStates_regs_of_ne_pc` does not apply. Either:

* move the `RegAgree` induction up into `root_soundness`, where the trace is known chained; or
* migrate `stepSound_of_programDecodes` to take `init` too — which forces the five multi-step
  witnesses to derive their states by running Sail (13 chain steps; see Phase 8 for the route).

Take the first. It is cheaper and does not disturb the five witnesses. **The slice at
`numInstructions = 1` does not distinguish them** — `addFaithful` has no step `j + 1` — so S2 states
`RegAgree` in the form the general case needs and satisfies it at step `0`, and the choice above is
only forced when the slice generalizes past one instruction. Record it then; do not pretend the
slice settled it.

The earlier claim in this plan that "the 504-occurrence strip across 35 files is bookkeeping"
describes only what happens *after* the induction is in place, and should never have been written as
if the strip were the easy part.

**Decisions I will make without stopping** (standing instruction, 2026-08-13; expert review runs
before anything lands). Two bars, and only two: do not actually increase trust — no new trust marker,
and no swapping one caller-supplied assumption for another while calling it discharged — and do not
regress progress. `RegAgree 0` as a new named boot premise clears the first bar **only if** the 116
per-row fields genuinely go away; the bargain gets stated plainly in the PR either way. Changing
`root_soundness`'s statement is in scope for the same reason.

**Design refined after Phase 7 (2026-08-11).** Two things changed the shape of this phase.

1. **The induction skeleton already exists.** `stepSound_of_programDecodes` is now a strong
   induction on the step index (Phase 7), carrying per-row PC agreement. Phase 4 widens that
   invariant to `PcAgree j ∧ RegAgree j`, where `RegAgree j` says the ZisK register file at step
   `j` equals Sail's `xreg`. No new induction has to be built.

2. **Where `h_a_lo_t` actually lives, measured.** `bus_effect` returns a
   `Prop × EStateM.Result`. Its **`.1`** accumulates, for every `mult = -1, as = 1` memory entry,
   exactly `read_xreg reg_idx state = .ok val state` — i.e. *the operand column equals the Sail
   register*. `state_effect_via_channels` is `(bus_effect …).2`, so `StepSound` compares only the
   post-state and **discards `.1` entirely**. That is the structural reason the register fields are
   assumed rather than checked: nothing in the export ever looks at the read conditions.

   So Phase 4 cannot recover them from `StepSound`. It must supply the two halves separately:

   * **ZisK side (Phase 3).** The operand column at step `j` equals the ZisK register file cell for
     `rs1`/`rs2`, from the register MemBus telescope anchored at `RegisterBoundary.bootMessage`.
   * **Cross-machine side (this phase).** `RegAgree` by induction: `RegAgree 0` is a new boot
     premise, in the same class as `SegmentPcChain.boot` and `BootSegmentMemorySeed`; the step is
     writeback preservation — `StepSound j`'s post-state updates Sail's `regs` from the c-side
     memory-bus entry (`write_xreg`, `mult = 1, as = 1`), and the ZisK register file is updated by
     the same `cMemMessage` push, so agreement carries.

   The writeback step reuses the Phase 7 machinery directly: `stepChannelOutput`,
   `stepChannelOutput_busEffect_ok` and the `bus_effect` reduction are already proved and are
   opcode-uniform. What is new is a `regs`-projection lemma in the shape of
   `nextPC_of_busEffect_ok` — read the c-entry's write back off the post-state — plus the
   `reg_of_fin r ≠ Register.nextPC` commutation that `BusEmission.write_reg_state_comm` already
   proves.

**Honest accounting to state in advance.** `RegAgree 0` is a new named premise. Phase 4 is a real
reduction only if the 116 per-row fields go away and only one boot equation replaces them — the
same bargain as the PC arm, but this time the per-row facts are genuinely *derived* through the
MemBus telescope rather than re-expressible as the premise. Whether the converse is provable (as it
was for Phases 5/6 and 7) must be checked and reported, not assumed either way.

### Phase 5 — the PC arm — **DONE**

Taken via the `Component.transition` fallback, not the execution-bus route. `SegmentPcSeed`
(`ZiskFv/Compliance/TraceLevelExport/SegmentPcSeed.lean`) has two fields, `boot` and `succ`.
`pcBridge_of_pcSeed` derives every row's PC agreement: row `0` is `boot`; every later row is `succ`
composed with the circuit's own PC recurrence
(`mainOfTable_pc_eq_nextPcMux_of_transitions_hold`, free from
`AcceptedZiskTrace.transitions_hold`). Two side conditions are derived rather than assumed:
`segment_l1 ≠ 1` off row `0` (from the fixed `SEGMENT_L1` schema) and the fixed-column capacity
bound (from the table's own `fixed_domain`).

### Phase 6 — collapse — **DONE**

`Inputs_<op>` was split into `InputsCore_<op>` + a child that `extends` it and carries
`h_pc_bridge` alone. That beat both alternatives (63 hand-written reduced structures; threading a
seed parameter through ~150 declarations and 413 application sites) and left all 119 read sites,
the `RowData_<op>` bundles, the four `StepStrong*` files and `EnvOf` untouched.

`root_soundness` and `stepSound_of_programDecodes` now take `InputsAgreeCore` + `pcSeed`.
`Audit.lean`'s frozen snapshot, `trust/trusted-base.md` and all seven accepted-trace witnesses were
updated in the same commit. Full `lake build` green (9154 jobs); V1 19/19.

### The guardrail this trips, stated plainly

The Guardrails section below says: *"The assumption count must strictly drop. Replacing a ∀-premise
with an equally strong new premise is laundering."*

The count drops (n PC equations → 2). **The strength does not.** `pcSeed_of_inputsAgree` proves the
converse, so over an `AcceptedZiskTrace` the old bundle and `InputsAgreeCore` + `pcSeed` are
inter-derivable. Earlier wording on this branch (commit `fdccff32`, the `SegmentPcSeed.lean` module
docstring) claimed "a genuine reduction rather than a repackaging"; that was wrong and is corrected
in `ad57f637` and in the ledger.

This is the same bargain `BootSegmentMemorySeed` (#185/#115) struck for memory — which the ledger
already records as "net-zero-to-marginally-stronger", not a reduction. It is legitimate *because it
is labelled honestly*: the ledger entry says "do not read this as a trust reduction". It is
laundering only if reported as a discharge.

**So Phase 5/6 do not close #330.** The PC arm is restructured and auditable, not discharged.

### Phase 7 — the PC-arm restructure — **DONE, MERGED (PR #338, squash `6b279fe3`)**

`root_soundness` takes `pcChain : SegmentPcChain` (`boot` + `retire`) and
`rowsAligned : StepRowsAligned` in place of `pcSeed : SegmentPcSeed`.
`stepSound_of_programDecodes` became a **strong induction on the step index**: row `0`'s PC
agreement is `boot`; every later row is derived from the *previous row's own* `StepSound` by
`pcBridge_succ_of_stepSound`.

New module `ZiskFv/Compliance/TraceLevelExport/SailRetireChain.lean`:

* `nextPC_of_busEffect_ok` — if the channel effect succeeds, its post-state's `nextPC` **is** the
  producer entry's `pc`. Needs only the execution bus's shape. This is what collapsed the expected
  63-arm proof into one lemma.
* `busEffect_ok_nil/_one/_three` + `stepChannelOutput_busEffect_ok` — the channel effect never
  faults. `MemBusMessage.toEntry` takes multiplicity and address space as explicit arguments and
  every bus passes numerals, so `bus_effect`'s "impossible under assumptions" exits are
  unreachable. **Proved, not assumed** — which is why `retire` needs no existential.
* `sailInstructionOf` / `sailStepResult` / `stepChannelOutput` / `stepProducerRow` — the 63 arms
  of `StepSound`, named. `stepSound_iff` and `stepChannelOutput_execRows` then close by
  `cases zs <;> rfl`. The plan's step 1 predicted a large 63-arm `sailPostState` construction; the
  arms turned out to be pure data extraction and the two bridging theorems are one line each.

**Guardrail check, stated plainly.** The plan's guardrail says the assumption count must strictly
drop and that replacing a ∀-premise with an equally strong one is laundering.
`sailRetireChain_of_inputsAgree` proves the converse — the old per-row bundle plus `rowsAligned`
yields `retire` — so **Phase 7 is not a logical-strength reduction either**, the same finding as
Phase 5/6. It is recorded as such in `trust/trusted-base.md`, the PR, and the module docstring.

What it does buy:

* `boot` is now the only premise relating a committed ZisK column to a Sail register. `retire`
  names no `mainOfTable` / `nextPcMux` / `pc`; `rowsAligned` names no Sail state. Each side is
  dischargeable by reasoning on one machine only.
* **`rowsAligned` is a condition the old `succ` was hiding.** `JalrLoweringRows` permits a two-row
  unaligned lowering with `finish = start + 1`, and `StepSound`'s JALR arm is indexed by `finish`,
  so such a step writes `pc (j + 2)` into Sail's `nextPC` while step `j + 1`'s bridge is stated at
  `pc (j + 1)`. Assuming `succ` let a trace satisfy the PC equation while its Sail step had in fact
  retired elsewhere. It binds only at steps with a successor, so a trailing unaligned JALR (the
  `jalrSpin` shape) discharges it vacuously.

Also landed: `inputsAgree_of_pcSeed` generalized to `inputsAgree_of_pcBridge` (takes the row's PC
agreement, not a whole-segment seed); new `pcNamed_of_inputsAgree` projects each arm's
`regs.get? PC = some v`. All 7 witnesses + the V2 degenerate probe updated; none evaluates a Sail
execution by hand.

### Phase 8 — the genuine PC discharge (#343) — **DONE at the root, branch `343-chained-sailtrace`**

`retire` is no longer a premise of `root_soundness`. This is the first assumption to actually leave
the endpoint in this workstream; Phases 5, 6 and 7 were restructurings.

**What landed.**

* `ChainedSailTrace.lean` — `retirePC`, `sailStepPost`, `chainedSailStates`, `chainedSailTrace`.
  `chainedSailTrace_retireChain` proves `SailRetireChain` with **no hypothesis**.
  `retirePC`'s `nextPC`-absent branch *erases* `PC`, so both sides of the retire law are `none`
  there and the law needs no side condition about the 63 `execute` arms.
* `root_soundness` takes `init : PreSail.SequentialState …` instead of `sailTrace`, and builds the
  trace itself. The `pcChain : SegmentPcChain …` binder is replaced by `pcBoot` alone.
* Frozen artefacts updated together with the declaration: `ZiskFv/Audit.lean`'s `#guard_msgs`
  snapshot, `trust/generated/baseline-strong-export-binders.txt`, and the PC-arm section of
  `trust/trusted-base.md`.

**Why it is a reduction and not another restructure.** `sailRetireChain_of_inputsAgree` derives
`retire` from the old per-row bundle — that converse is what made Phase 7 inter-derivable with what
it replaced. It needs `retire` to be something a caller supplies. At the root there is nothing to
supply, so there is nothing to derive. #343's own guardrail is also met: a caller can no longer pick
the Sail states, because `inputsAgree` is now demanded at `chainedSailTrace ziskStep init`.

**The scope claim in this section was wrong, and the correction is the reusable lesson.** It said
`SailTrace` is "referenced by all 63 arms, every `Inputs_<op>`, and all 7 witnesses", so the change
needed sign-off before starting. Two of those three are false:

* `InputsAgreeCore` and `StepSoundWithoutDecode` are **parametric** in `sailTrace` and only ever use
  `sailTrace i`. The 63 arms need no edit. There are 11 `sailTrace` binder sites in total, 8 of them
  in `Dispatcher.lean`.
* Only **2** of the 7 witnesses instantiate `root_soundness`; the other 5 target
  `stepSound_of_programDecodes`, which deliberately keeps its signature. Those 2 are at `n = 1` and
  `n = 0`, so neither has a chain step to evaluate.

The estimate came from reading the issue body instead of the tree. Grep before scoping.

**What is left.** Migrating the five multi-step witnesses off hand-written traces means deriving
each state by running Sail — 13 chain steps in total. That is real work and is not done. It is not
needed for the root reduction, only for those five to exercise the generated trace. The route, if
picked up: the `Dispatch/` equivalences already give
`execute_instruction … = state_effect_via_channels …`, so the post-state is computable from the
witness's own bus rows via `nextPC_of_busEffect_ok` and `RegisterWriteback`'s projections — no
brute-force reduction of Sail's `execute` is required.

### Clean upgrade — **DONE, MERGED (PR #339, squash `8794dcca`)**

`flake.nix`'s `clean-src` names fork `bf5e40ed` (`port-zero-mult-gating`, Lean 4.28.0), all 24
components are migrated to the post-#398 `ElaboratedCircuit` class, and the combined tree —
Phase 7 + Phase 4 groundwork + the migration — builds green at 9158 jobs with V1 19/19.
`scripts/chansnap.py` is committed as the safety gate.

**#337 is fixed upstream.** `Channel.toRaw.Requirements` now reads `mult ≠ -1 → mult ≠ 0 →
Guarantees`. That is exactly the multiplicity gating Phase 0 found missing, so the `Guarantees`
rewire is unblocked and the bespoke `gated` `RawChannel` from `Spike330.lean` is no longer needed.

**Channel snapshot: 70 → 69, two deltas, both checked by hand (not just by the script).**

* **−3, shadowed duplicates.** `Binary.staticLookupCircuit`,
  `BinaryExtension.staticLookupCircuit`, `.shiftStaticLookupCircuit` each restated an
  `exposedChannels` its base already had, byte-identically. Merged form declares it once.
* **+2, `channelsWithGuarantees := []`** on `MemAlignByte.circuit` and
  `MemAlignReadByte.circuit`, which pull from MemBus. Verified sound and, more importantly,
  **kernel-checked**: `ChannelsLawful ops []` (`Clean/Circuit/Operations.lean:1134`) requires
  `∀ i ∈ interactions ops, i.channel ∈ [] ∨ i.Guarantees env`, and the left disjunct is false,
  so it holds *only because* `MemBusChannel.Guarantees := True`
  (`ZiskFv/Channels/MemoryBus.lean:105`). Both circuits carry
  `channelsWithRequirements := [MemBusChannel.toRaw]`, so `Operations.lean:302`'s
  `channels ⊆ guarantees ++ requirements` is satisfied.

### Phase 3 tripwire, found by that verification — read before starting

Giving `MemBusChannel` a real `Guarantees` is Phase 3's whole design. The moment it stops being
`True`:

1. `MemAlignByte.circuit` and `MemAlignReadByte.circuit`'s `channelsWithGuarantees := []` **stop
   compiling**. This is a feature, not an obstacle — Lean checks it, so the weakening cannot pass
   silently. Both must be revisited and given the real list.
2. Once they carry `[MemBusChannel.toRaw]`, `SoundEnsemble.addTable`'s
   `channelsWithGuarantees ⊆ finished` obligation binds, and `fullRv64imEnsemble`'s existing table
   order does not satisfy it. The ensemble needs reordering, or the guarantee needs to be carried
   only by the components that actually guarantee.

Budget Phase 3 with both in scope. Neither is optional and neither is visible until the
`Guarantees` change is made.

### Phase 3 is blocked by extraction fidelity, not by Clean (measured 2026-08-11)

The Clean migration removed the blocker this plan named and revealed the real one. **Do not start
Phase 3 as written — the descent it needs is not in our model.**

**What the telescope needs.** To terminate at `RegisterBoundary.bootMessage`'s literal `ts = 0`, the
register access chain must strictly descend. Balance alone is not enough: it says pulls and pushes
pair up as a multiset, so the pairing may decompose into the boundary path *plus disjoint cycles*, and
a cycle carries prover-chosen values that nothing ties to the boot value.

**Why cycles are constructible in our model.** The pull side is pinned — `a_mem_step` is
`1 + main_step * 4`, and `MainStepIndexFixedFacts.main_step_eq_index` (a field of
`AcceptedZiskTrace`) pins `main_step = i`. The push side is not: `a_reg_prev_mem_step` is a free
witness column (`Main/Circuit.lean:230`, `Main/Row.lean:115`) whose only use is as the `timestamp` of
`aRegPreMessageExpr` (`Main/Constraints.lean:398`). **No constraint in our Main component touches
it.**

**What the real circuit has that we do not.** `main.pil:333-335`:

```
range_check(expression: a_mem_step - a_reg_prev_mem_step - 1, min: 0, max: MAX_RANGE);
range_check(expression: b_mem_step - b_reg_prev_mem_step - 1, min: 0, max: MAX_RANGE);
range_check(expression: store_mem_step - store_reg_prev_mem_step - 1, min: 0, max: MAX_RANGE);
```

(`MAX_RANGE = (1 << 24) - 1`; the columns are additionally declared `bits(REG_STEP_BITS)` at
`main.pil:261-263`.) That is exactly the strict descent, and with it a decreasing cycle is
impossible. The plan's earlier citation of `main.pil:277-279` was the `reg_pre_load` *call site*,
which only names the column; `reg_pre_load` itself (`mem.pil:492-494`) emits no range check —
unlike `precompiled_reg_load` (`mem.pil:496-500`), which does.

**Measured status in the tree.** The extractor captures the wiring
(`build/extraction/Extraction/LookupWiring.lean:924, 951` carry
`"(a_mem_step - a_reg_prev_mem_step) - 1"` and the b-side twin), and
`SpecifiedRangesSlice.component` **is** composed into `fullRv64imEnsemble`
(`FullEnsemble.lean:128`). But Main emits **only** `OpBusChannel` (1 interaction) and
`MemBusChannel` (6); `grep SpecifiedRanges ZiskFv/AirsClean/Main/` returns nothing. The existing
slice is bus 103, the **16-bit** table Mem uses for its distance chunks; Main's checks are 24-bit
(`MAX_RANGE`), a different range id. So the descent is **not derivable from
`AcceptedZiskTrace.constraints_hold`**.

This is the #169/#19 range-fidelity axis that this plan's own guardrail said would have to be
"said out loud, not slipped in to make a proof close". Taking the descent as a premise instead
would be laundering: it is not a small side condition, it is the entire content of register-read
soundness.

**Route, and its cost.** The pattern to copy already exists and is non-trivial:
`ZiskFv/Channels/SpecifiedRanges.lean` gives `SpecifiedRangesSliceChannel` a real `Guarantees`
(`rangeId = 103 ∧ rangeTable16.Spec value`) plus a `memDistanceMessage_guarantees_iff` bridge, and
`Mem/Constraints.lean:409-414` emits four interactions into it. Phase 3 needs the same for the
register-step range:

1. read the actual bus id and bound for `range_check(…, min: 0, max: MAX_RANGE)` out of the pinned
   pilout;
2. add the matching slice channel + component, with a `Guarantees` giving the 24-bit bound;
3. have Main emit the three interactions (a / b / store);
4. compose the slice into `fullRv64imEnsemble` and fix the `addTable` ordering;
5. only then walk the telescope, using descent + `main_step_eq_index` to rule out cycles.

Steps 1–4 are extraction/composition work on the #169/#19 axis, not proof work. Step 5 is the
original Phase 3.

**A concrete witness that the gap is load-bearing.** The project's own standard is that a premise
needs a witness showing it is non-vacuous; symmetrically, a claimed gap needs a witness showing it
is real. Here is one, read off the emission definitions.

A Main row's register-pre **push** and its memory **pull** carry the *same* value lanes:
`aRegPreMessageExpr` is `{ mem_op := 3, ptr := a_offset_imm0, timestamp := a_reg_prev_mem_step,
value_0 := a_0, value_1 := a_1 }` and `aMemMessageExpr` is `{ …, timestamp := 1 + main_step * 4,
value_0 := a_0, value_1 := a_1 }` (`Main/Constraints.lean:360-364, 396-401`). The pull's timestamp
is pinned; the push's is free.

Take two rows `A`, `B` accessing the same register. Set `a_reg_prev_mem_step_A := ts_B` and
`a_reg_prev_mem_step_B := ts_A`, and give both rows the same arbitrary value `v`. Then `A`'s pull
matches `B`'s push and `B`'s pull matches `A`'s push — a closed 2-cycle carrying `v`, touching
neither the boot pull nor the reload push. The boundary still balances with itself: our
`RegisterBoundary` omits `main.pil:447`'s range check on `last_segment_reg_mem_step`, so the reload
push's timestamp is free too and can be set to `0` to pair with `bootMessage`'s literal
`(ts 0, value 0)`. Every interaction is matched, `BalancedChannels` holds, and both rows read a
value that was never written.

**What this does and does not say.** It does **not** say `root_soundness` is unsound. Those reads
are exactly what `InputsAgree`'s `h_a_*_t` / `h_b_*_t` fields *assume*, so the theorem as stated is
unaffected — the assumption covers the gap. What it says is that those 116 fields **cannot be
discharged** from the current model at any amount of proof effort, because the model admits traces
where they are false. It is also not a ZisK defect: the real circuit rules the cycle out with
`main.pil:333-335` (and `main.pil:447` on the boundary side). It is an extraction-fidelity gap, and
it is the reason Phase 3 needs the bus-102 slice rather than a cleverer proof.

**Feasibility, measured (2026-08-11).** The route is buildable — every piece of the pattern
already exists:

* the bus id is **102** for all three checks, read off the extraction:
  `hint_Main_40_1` carries `piop := "Range Check"`, `busId := Expr.constant "102"`,
  `multiplicity := witness 1 35`, and the slot
  `"(a_mem_step - a_reg_prev_mem_step) - 1"`; `constraint_Main_41` carries the b-side
  (`witness 1 31`, selector `witness 1 36`) and store-side (`witness 1 32`, selector
  `witness 1 37`) twins. All three sit in the **stage-2 challenge-mixing** constraints, which is
  precisely the part the F-only extracted slice does not carry — Clean's `Channel` / `Air.Balance`
  layer is their modelled counterpart.
* `rangeTable24` already exists (`ZiskFv/AirsClean/RangeTables.lean`,
  `rangeStaticTable (2 ^ 24) … "range-24"`), matching `MAX_RANGE = (1 << 24) - 1`.
* `ZiskFv/AirsClean/SpecifiedRangesSlice.lean` is a ~70-line template — circuit, `Spec`,
  `ProverAssumptions`, `component`, and `component_interactionsWith_rangeChannel` — that the
  bus-102 slice mirrors with `rangeTable16 → rangeTable24` and `103 → 102`.

**The increment is atomic; it cannot be landed in halves.** V1 check 18 (module reachability)
fails on a module that is not reachable from `ZiskFv.lean` — confirmed empirically, not assumed. So
the slice, Main's three emissions, and the `fullRv64imEnsemble` composition must land together.

**Started 2026-08-11; the first third is banked on `330-phase3-bus102-wip` (NOT GREEN, do not
merge).** `RegisterStepRangeChannel` (bus 102, real `Guarantees`, `rangeTable24`) and
`ZiskFv/AirsClean/RegisterStepRangeSlice.lean` are written and build in isolation (8067 jobs); the
branch deliberately fails V1 check 18 because the wiring is not there yet. `a_src_reg` / `b_src_reg`
/ `store_reg` are already columns 35/36/37, so Main's emissions need no new columns.

**Progress, 2026-08-11 — two thirds banked on `330-phase3-bus102-wip` (NOT GREEN, do not merge).**

Building on their own:

* `RegisterStepRangeChannel` (bus 102, real `Guarantees msg _ := msg.rangeId = 102 ∧
  rangeTable24.Spec msg.value`) and `ZiskFv/AirsClean/RegisterStepRangeSlice.lean`, the bounded
  static provider, mirroring the bus-103 pair.
* Main's three emissions: `aRegStepDistanceExpr` / `bRegStepDistanceExpr` / `cRegStepDistanceExpr`
  plus `RegisterStepRangeChannel.emit (-<sel>)` on the outermost layer, a third `expose` block, and
  the three-way `exposedChannels_eq` split (`lake build ZiskFv.AirsClean.Main.Constraints` green,
  8058 jobs). **No new columns needed** — `a_src_reg` / `b_src_reg` / `store_reg` are already
  stage-1 columns 35/36/37.
* `RegisterStepRangeSlice.component` added to `fullRv64imSoundEnsemble` with
  `addFinishedChannel RegisterStepRangeChannel.toRaw`, mirroring bus 103.

**RETRACTED: "Main must stop being the first table."** An earlier revision of this section claimed
the ensemble had to be reordered because Main would need `RegisterStepRangeChannel.toRaw` in
`channelsWithGuarantees`. The compiler contradicts it. Main's new obligations land on the
*Requirements* side, in the #337-gated form

```
¬(sel = 1) → ¬(sel = 0) → RegisterStepRangeChannel.Guarantees { rangeId := 102, value := … }
```

one per slot. Those hypotheses contradict booleanity of the selector, so they are vacuous — Main
proves no range fact and nothing so far demands a reorder. Whether `channelsLawful` or
`SoundEnsemble.addTable` still forces one is **unknown**: the build stops before reaching them.
Do not assume either way; let the compiler answer it.

**The next concrete task, and the one real gap.** `mainWithRomMemAndOpBus_soundness`
(`Main/Circuit.lean:657`) and its completeness twin must discharge those three conjuncts, each
needing `<sel> = 0 ∨ <sel> = 1`. That follows from the ROM lookup — the table's rows are
`mainRomRowOf` images whose flags are `boolF`-valued (`Main/Circuit.lean:193, 311`), and soundness
already has `(romStaticTable length program).Spec (eval env (romMessageExpr row))`
(`Main/Circuit.lean:530`) — but **no rom-flag booleanity lemma exists in the tree** (`grep` returns
nothing), so it must be proved by unpacking `packFlags`. That is the piece to write next.

**Note the interaction with the tripwire above.** Step 2 gives *this* channel a real `Guarantees`,
which is separate from giving `MemBusChannel` one. The `MemAlignByte` / `MemAlignReadByte`
`channelsWithGuarantees := []` tripwire fires only on the `MemBusChannel` change, so if the descent
route is taken first, that tripwire stays dormant.

### Flake follow-ups, owner-sequenced — NOT done

`flake.nix` names `bf5e40ed` but `flake.lock` still pins `8edf71f8`, because `nix run .#populate`
would overwrite the **shared** `/home/cody/zisk-fv/build/clean-lean` under every other worktree.
Four files describe `8edf71f8` and are consistent with the lock, not with `flake.nix`. They move in
the **same** change as the lock: `flake.lock`, `nix/README.md:26`, `trust/trusted-base.md:1053`
(the ledger's record of the pinned Clean input), and `docs/clean-fork-divergences.md` (entry **D0**
landed upstream and should be deleted per that file's own rule; D1–D3's `main @ 8edf71f8`
provenance lines become `bf5e40ed`).

## Guardrails

- **The assumption count must strictly drop.** Replacing a ∀-premise with an equally strong new premise
  is laundering. Each phase records before/after premise counts in its PR.
- **Every new premise ships with a witness in the same PR.** The #320 lesson: `A → B` passes every gate
  whether or not `A` is inhabited.
- **No new trust markers.** No `axiom`/`opaque`/`sorry`/`native_decide`; `#print axioms` stays
  kernel-only on every touched endpoint.
- **The guarantee must not be overstrong.** A `Guarantees` stronger than what the circuit actually
  provides is an overstrong validator — the anti-laundering hazard runs in that direction. Every clause
  needs a PIL citation.
- **Do not quietly re-add dropped constraints.** Our `RegisterBoundary` omits `main.pil:447`'s range
  check, which is sound (under-constrained ⇒ we accept a superset ⇒ the soundness claim is stronger).
  If the argument turns out to need it, that is the #169/#19 range-fidelity axis and gets said out
  loud, not slipped in to make a proof close.

## Landed (2026-08-12)

Both stack PRs are merged to main; main is `8794dcca`.

| PR | squash | closes | build | V1 | V2 |
|---|---|---|---|---|---|
| #338 Phases 0/2/5/6/7 | `6b279fe3` | #340, #341 | 9156 | 19/19 | exit 0 |
| #339 Clean post-#398 + `bf5e40ed` | `8794dcca` | #337 | 9158 | 20/20 | exit 0 |

Each row was measured on that PR's own head (`b9b50aba`, `30983048`). The two V1 totals differ
because #339 adds check 20, the channel-declaration snapshot; quoting one PR's total for the other
is the error the reviewer caught, so the numbers are recorded per head here. After #338 squashed,
#339 needed `git rebase --onto origin/main 0fc035b6` — a plain rebase onto main hits an add/add
conflict, because the branch replays commits whose content the squash already put on main. Main's
tree is byte-identical to the gated `30983048`.

Open follow-ups: **#342** (bus-102 range slice — gates Phase 3 and Phase 4), **#343** (Phase 8,
`SailTrace` as a chained execution), **#344** (JALR two-row coverage gap).

## Verification

- Inner loop: `lake build <target>` plus LSP diagnostics on touched files.
- Per phase: `lake build`, then `trust/scripts/check-all.sh` (V1) and
  `trust/scripts/check-all-semantic.sh` (V2, needs oleans).
- Before each landing: `nix run .#test` (eight stages).
- Regression floor: all seven existing accepted-trace witnesses must still instantiate, including
  `addFaithfulPaddedRawRootSoundness` and `memoryRawRootSoundness`.

## Key files

| Role | Path |
|---|---|
| Channel to change | `ZiskFv/Channels/MemoryBus.lean` |
| Pattern to copy | `ZiskFv/Channels/SpecifiedRanges.lean` |
| Push sites | `ZiskFv/AirsClean/Main/Constraints.lean:440-520`, `ZiskFv/AirsClean/RegisterBoundary.lean` |
| Spike target | `ZiskFv/Compliance/RegisterMemBusBalance.lean` |
| Consumption | `ZiskFv/Compliance/TraceLevelExport/RowData*.lean`, `.../Dispatcher.lean:192` |
| Root endpoint | `ZiskFv/Soundness.lean` |
| Clean reference | `build/clean-lean/Clean/Air/Balance.lean`, `Clean/Air/OrderedChannel.lean`, `Clean/Circuit/Channel.lean` |
| Fallback route | `ZiskFv/Compliance/TraceLevelExport/BootSegmentMemorySeed.lean` (shape to mirror) |
