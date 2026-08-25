# Projects

## Active

### Project Closeout

Plan: `docs/ai/plan/PLAN_PROJECT_CLOSEOUT.md` — the wind-down metaplan (owner ruling 2026-07-13:
completeness, no punts); **its "WHERE WE ARE" dashboard is the source of truth**. S1–S4 done and
merged (#249/#243/#226/#242 + detour #268 closed; main `d4780eee`). S4 closed #242 with MemAlign
read-soundness proven and two real ZisK v0.17.0 defects named/excluded (narrow-load value-lane
forge = our unreported find, + skippable-prove #1142); a Docker repro of the narrow-load bug is in
progress in `~/zisk`. **S5 (#221→#74) landed 2026-07-27** (PRs #290/#291; both issues closed).
**S6 #281 landed as PR #292** (`a60b2bd5`; issue closed) after adversarial review corrected its
trust and provider-route wording. **S7 #280 and S8 #279 both LANDED 2026-07-28** — merged as PR #293 (`fac67c2f`) and PR #294
rebased onto it (`2da97416`); both issues auto-closed. S8 deleted all 16 `Inputs_div` fields and
added defect 6 (signed-DIV quotient sign, reproduced by codygunton/zisk#12). **The merge broke
`main` and was repaired the same day** by PR #297 (`01f5a5ba`) and PR #298 (`e19f012e`): neither
#293 nor #294 imported its root-soundness witness from `ZiskFv.lean`, so `lake build` never
compiled them and the semantic gate had been passing on leftover explicit builds — CI on `main`
failed on both probes. Repairing it exposed four real breakages (each PR's witness written against
the other's pre-merge shapes) plus a 637-line signed-DIV regression that did not typecheck while
`trust/defects.md` cited it as evidence. `main` is now `e19f012e`, green, with a V1 build-graph
reachability gate (check 18/18, allowlist-free) and the counterexample's axioms pinned at V2 check
9/19. S7b **#295 is complete**: PR #299 merged as `5b1f4fca` after adversarial review and the full
eight-stage repository gate; **S8b #296 is complete** through PR #310 at `740f4429`: the weld
fan-out is merged and its fail-closed gate pins 11 map carriers against nine generated AIR headers.
**S9 #61 is DONE 2026-08-07** — the six-PR Phase 9 stack (#313–#318) is merged, the raw-program
endpoint *is* the headline `root_soundness` (binder list frozen in-build by `ZiskFv/Audit.lean`,
PR #336), and the non-vacuity gap it left at the entrypoint (#320) was closed by PR #335
(`9b65f7b7`): a real executed step lifted through `programDecode_of_rawProgramDecode` from an
inhabited `ProgramRowsBinding`. **#61 and #320 both CLOSED.** Residuals split out: #172 (Sail-side
`raw word → ext_decode` grounding, now unblocked), #184 (premise audit), #334 (remaining spin-trace
witnesses carry hand-authored `ind_width` placeholders — not usable for `ProgramRowsBinding`).
Added 2026-07-28: **S11 (#303 + #304)** — round-trip verification, after the weld fan-out showed
every mirror gap was found by hand rather than by a gate. Check `g(f(t)) ≡ t` in the pilout algebra
so coverage is derived from data, not from a declaration list. **PART I DONE 2026-08-06** — the gate
is green on `main` at `176/176 comparable, 0 failing`: #303/#304 merged (PRs #312/#327), the 9 Main
segment-boundary gaps closed by a `MainExposed` carrier + welds (PR #331, which also added the
consumed-check), and residuals + a real MemAlign L1 `fixedColumns` fix landed as PR #333 (#329/#332
CLOSED; its anti-laundering pin-check survived three review rounds). Forward and out of PART I scope:
**#328** (cross-segment continuation, ladder C4) and **#330** (discharge `InputsAgree`; no longer
blocked by #184). **PART II — completeness** (#108/#182/#183/#154) stays **parked**. The #173
dependency graph was re-audited 2026-08-07 against native `blockedBy` metadata: #61/#320 closed,
both `#61 blockedBy #184` and `#330 blockedBy #184` dropped (a docs-only audit is not a prerequisite
for proof content), `#75 blockedBy #174` added, and axis labels applied to #328/#330/#334 (all three
had rendered as unlabeled). Result: 19 nodes, 6 edges; nothing on the soundness axis is blocked on
proof content.

#360 now owns the successor stream — see **Inputsagreecore 360** below.
This plan carries two standing sections every agent and review must honor: **Defect watch** (unexposed
table/inter-channel ZisK bugs expected on external word; recognition not hunting) and the
**post-mvp coverage ladder** (owner ruling 2026-07-22: C1 full link coverage, C2 un-composed AIRs,
C3 Zicclsm, C4 #103 cross-segment — covered eventually, outside the mvp finish line).

### Inputsagreecore 360

PR #359 merged as `08db1645` and closed #357.
It passed both 20-check trust gates and resolved all 13 review threads.

Plan: `docs/ai/plan/PLAN_INPUTSAGREECORE_360.md` — #360 owns the full removal of
`InputsAgreeCore` from `root_soundness`. Closed #330 remains the completed register subproject.
The new parent also contains #76, #172, #184, and #353. Worktree
`/home/cody/zisk-fv/.worktrees/inputsagree-330-spike`, branch
`330-spike`. **PR #338 MERGED 2026-08-12** (squash `6b279fe3`, closes #340 + #341) with **PR #339
MERGED** on top (squash `8794dcca`, closes #337); main is now `8794dcca`. #338 carries Phases
0/2/3-partial/5/6/7: `root_soundness` takes
`InputsAgreeCore` + `pcChain : SegmentPcChain` (`boot` + a Sail-internal `retire` law) +
`rowsAligned : StepRowsAligned`, and `stepSound_of_programDecodes` is a strong induction on the
step index instead of a per-`i` map (`lake build` 9156 green, V1 19/19, V2 exit 0, no new axioms,
three gate artifacts updated deliberately). **At that checkpoint, #330 was not resolved.** Both
`pcSeed_of_inputsAgree` (Phase 5/6) and `sailRetireChain_of_inputsAgree` (Phase 7) prove the
converses, so given `rowsAligned` the old per-row bundle and `boot` + `retire` are
inter-derivable — honest restructurings in the `BootSegmentMemorySeed` class, not discharges. What
they buy: `boot` is now the only premise relating a committed ZisK column to a Sail register, and
`rowsAligned` exposes a placement condition the assumed `succ` was hiding (an unaligned two-row
JALR writes `pc (j+2)` into Sail's `nextPC` while step `j+1`'s bridge is stated at `pc (j+1)`).
The Clean migration is **DONE** (PR #339, all 24 components, `flake.nix` repointed to `bf5e40ed`;
`lake build` 9158 green, V1 20/20 — #339 adds check 20, the channel-declaration snapshot — V2 exit
0) and it fixed #337 upstream. It also pins a Clean revision where `Channel.toRaw.Requirements`
gains a `mult ≠ 0` guard, i.e. **an obligation this project proves became weaker**; merged on owner
instruction, argued (in `trust/trusted-base.md`) to lose nothing derivable because Clean consumes
`Requirements` only via `exists_push_of_pull`, which already concludes `mult ≠ 0`. That argument is
human-made, not machine-checked, and must be re-read at the next `clean-src` bump. The migration did
**not** unblock Phase 3. **Phase 3 is blocked by extraction fidelity, not by
Clean**: the register telescope needs the strict descent at `main.pil:333-335` (bus 102, 24-bit) to
rule out disjoint cycles in the balanced register partition, and Main emits no `SpecifiedRanges`
interaction, so `a_reg_prev_mem_step` is a free witness column nothing constrains. A concrete
two-cycle witness (recorded in the plan) shows the gap is load-bearing: the 116 `h_a_*_t`/`h_b_*_t`
fields **cannot be discharged** from the current model at any proof effort. This does not make
`root_soundness` unsound — those fields are exactly what it assumes — and it is not a ZisK defect;
the real circuit rules the cycle out. Closing it means building a bus-102 range slice (**#342**,
#169/#19 axis, atomic because V1 check 18 rejects an unwired module); Phase 4 (the 116 fields) is
blocked on it. **#342's first half MERGED as PR #345** (squash `88ff6704`): the bus-102 slice, the
descent derived from balance rather than assumed, all seven accepted-trace witnesses closing the
channel, and the tree's last three `sorry`s discharged. **The second half MERGED as PR #346** (squash `e84e4e79`): the walk is now
quantified over an accepted trace — a register read is supplied either by the `RegisterBoundary` or
by a Main row whose own access is **strictly later**, with the branch split from
`channels_balanced`, the supplying slot's activity from its counterpart multiplicity plus selector
booleanity, and the no-wrap bound from the Main table's fixed-column capacity rather than a
segment-length premise. Cycles are therefore excluded (including mixed-slot ones), and the relation
is exhibited non-vacuously on the `add x1,x1,x1` witness row. Gates on the merged head: build 9161,
V1 20/20, V2 20/20 (V2 gained check 19, register-walk acyclicity).
**#342 stays OPEN — termination is not proved.**
Acyclicity bounds the walk from below, not above; iterating the supply step needs the supplying
row's own access to be a `mem_op = 3` pull, i.e. `a_src_mem + a_src_reg = 1` (Clean's
`exists_push_of_pull` fires only at `-1`). I first routed that to the committed-program decode
bridge (#172); **that was wrong**, and **PR #347** proves it from `BalancedChannels` alone.
`BalancedInteractions` is message-exact, so a row setting both flags emits at `mem_op = 4` where no
other emission in the ensemble can offset it (register-pre pushes and `RegisterBoundary` carry `3`,
`MemAlignReadByte` carries `1`, `Mem`/`MemAlign`/`MemAlignByte` carry `wr + 1` or `1 + is_write`
with the flag `Spec`-bounded, and Main's three currents are all pulls pinned to `-2`); the balance
is then `-2 * count` with `count ≥ 1 < GL_prime`. #347 lands
`main_not_a_src_mem_and_a_src_reg`, `main_aMem_pull_of_a_src_reg`,
`main_not_store_mem_and_store_ind_and_store_reg` (the same argument at `mem_op = 7`) and
`slot_timestamp_ne` (the three slots access at `1,2,3 + 4*main_step` with `main_step` the row index
capped at `2^22`, so no wraparound crosses residue classes). Gates on `27db4dca`: build 9163,
V1 20/20, V2 20/20. The `mem_op = 5` instance is
also built (`ZiskFv/Compliance/MemBusSlotSeparation.lean`): there the multiplicity is not constant
across slots, and `cMem_message_ne_bMem_message` separates them by timestamp residue. So
**all three slots are exclusive** and every Main register access is a genuine `-1` pull at
`mem_op = 3`. **Termination is proved** (`exists_boundarySuppliedSite`): from any witness
site the walk reaches a site supplied by `RegisterBoundary`. Main-table uniqueness turned out **not**
to be needed — the ensemble-level counterpart lemma already quantified over an arbitrary
`mainTable ∈ witness.allTables`; only the trace wrapper had specialized it. The measure is
`2^40 − readTimestamp`, well-founded from the Main table's fixed-column capacity. **The `RegisterBoundary` fidelity repair is DONE (2026-08-15, branch `330-registerboundary-fidelity`).**
`reg` moved from a free witness cell into the component's fixed schema — `rawWidth` 4 → 3, capacity
31, `values 0 i = i + 1` — so the register index is component-owned data and `Table.fixed_domain`
bounds the row count at 31 for free. Evidence at the layer the proof consumes:
The PIL source is the citation: `main.pil:536` runs `global_init_mem(sel: 1, addr: ireg +
REGS_IN_MAIN_FROM, value: zeros)` in a compile-time loop with `REGS_IN_MAIN_FROM = 1`,
`REGS_IN_MAIN_TO = 31`, and `mem.pil:507-508` expands it to
`direct_global_update_assumes(MEMORY_ID, [MEMORY_REG_OP, addr, 0, 8, ...value], sel: 1)`. The
address is a literal per unrolled iteration; there is no witness column for it. **RETRACTED:** an
earlier entry here claimed `Extraction/Main.lean` carries "exactly 62 `mem_op = 3` direct terms at
literal addresses 1..31, each twice". That count could not be reproduced from the tree. What is
verified is 96 `im_direct` lanes with a repeating three-lane pattern matching the register loop's
three emissions; the lane-to-source map is open, tracked by **#354**.
Gates: build 9170, V1 20/20, V2 semantic all passed. Deliverables `materialized_reg_eq` and
`materialized_index_unique`.
**The COVERAGE ARGUMENT IS NOW COMPLETE — all four steps proved on the same branch.**
(1) Main-table uniqueness `main_table_unique` (`df6a87f4`), discriminating on `rawWidth` via the
pinned profile `ensemble_rawWidths`; the assumable `mem_replay_source_covers`-shaped fallback was
NOT taken. (2) Pull-uniqueness `readMessage_inj` (`1eaa27d1`) — an access timestamp is
`offset + 4 * index`, naming slot and row. (3) Push-injectivity `regPreMessage_inj` (`14514ee8`) —
balance forces push positions = pull positions, two slots give two pushes, at most one pull, so
`2 ≤ 1`; needed a new `pushCount_eq_pullCount_of_balanced` because the existing balance lemma
assumes ONE constant multiplicity, and the whole argument must stay at `List.countP` level since
two rows emitting one message give EQUAL values at different positions. (4) The merge
`bootWalk_merge` (`418bcabf` generic, `d95d926b` instantiated) — two boot walks ending at the same
anchor merge, because reversed they start there and each step is then functional.
**Steps 3 and 4 are both FALSE without the fidelity repair**, which is the evidence the gap was
load-bearing rather than cosmetic. The assumed-field count is **still 504**: S3's composition and
S4's removal remain, and none of this counts as progress on the deliverable until it drops.
Historical framing follows.
**Phase 4 WAS BLOCKED on that repair (found 2026-08-13, by proving toward it).**
Deriving the 116 register fields needs the telescope's coverage argument; coverage needs the
boot-anchored slot to be unique per register; that is FALSE in the model, because
`RegisterBoundaryRow.reg` is a free witness column and `RegisterBoundary.circuit` has `Spec := True`,
so two boundary rows may carry the same `reg`. The PIL is stronger — `main.pil:535-537` emits the
boot pulls from a compile-time `for (ireg …) global_init_mem(sel: 1, addr: ireg + REGS_IN_MAIN_FROM)`,
a literal address per iteration with no witness column at all. This is a model-fidelity gap, not a
ZisK defect. The repair (a fixed enumerated register column) REDUCES prover freedom so costs no
trust, but touches 34 files and all 20 boundary-table construction sites including every checked-in
witness, so it needs owner sign-off on scope. S1 and S2 landed and do not depend on the gap.
**Phase 4 RESTRUCTURED 2026-08-13 to a vertical slice**, because the old machinery-ordered step list
let eight PRs merge (#338/#339/#345/#346/#347/#349/#350/#352) while the assumed-field count stayed
**504 → 504** — every step could finish without touching the deliverable, and it hid a false "both
halves are built" claim (`exists_bootAnchored` binds fresh variables and carries no value; fixed by
`exists_bootWalk`, `54ab4b9d`). New shape: drive ONE field (`h_a_lo_t` on ADD, against the
`addFaithful` witness) end-to-end through S1 value-carrying → S2 `RegAgree` at step 0 → S3 derive →
S4 remove, with **the acceptance gate being the grep count dropping to 503, not a green build**; then
generalize along two axes (other three lanes, then 62 opcodes) as separate PRs. Everything landed is
reused; only the order of consumption changed.
**Phase 4 was BLOCKED on #343** and is now partly unblocked: `SailTrace` was an unchained `Fin n → State`, so `RegAgree`'s induction step had nothing to induct over, and closing that with a `SegmentRegChain.succ` premise would trade 116 per-row assumptions for `n` per-step ones of the same strength. Both halves of Phase 4 are built (PR #351 ZisK side; pre-existing `RegisterWriteback.lean` Sail side), and `chainedSailStates_regs_of_ne_pc` now supplies the missing equation; what remains is that `stepSound_of_programDecodes` still takes a bare `sailTrace`, so the `RegAgree` induction must either move up into `root_soundness` or that layer must migrate too. **#342 is CLOSED**; PR #347 merged as `28b9304b`, with review fixes in **#349** (`dff7ad08`) that record the walk's **path** rather than a bare existential and make V2 check 19 *assert* the axiom closure with build 9163,
V1 20/20, V2 20/20. **One gap remains, split out as #348**: `main.pil:447`'s reload-timestamp check
is unmodelled, so the boundary can self-pair at timestamp `0` — the walk reaches the boundary but
*which* boundary message it lands on is not pinned. #348 now blocks #330.
**Phase 8 (#343) is DONE at the root**, on branch `343-chained-sailtrace` (HEAD `4e6b5fcb`,
worktree `/home/cody/zisk-fv/.worktrees/clean-migration-330`), PR pending: `root_soundness` now
takes an initial Sail state instead of a `SailTrace`, generates the trace with `chainedSailTrace`,
and gets `retire` from the hypothesis-free theorem `chainedSailTrace_retireChain` — so the
`pcChain : SegmentPcChain` binder is **gone**, leaving `pcBoot` alone. **This is the first premise
to actually leave `root_soundness` on this line of work**, because the converse that made Phases
5/6/7 inter-derivable (`sailRetireChain_of_inputsAgree`) needs `retire` to be caller-supplied, and
at the root there is nothing to supply; #343's guardrail is met too, since `inputsAgree` is now
demanded at the generated trace, so a caller can no longer choose the Sail states. #343's own scope
claim was wrong and is corrected in the plan: `InputsAgreeCore`/`StepSoundWithoutDecode` are
parametric in `sailTrace` (the 63 arms need no edit; 11 binder sites exist, 8 in `Dispatcher.lean`),
and only 2 of the 7 witnesses instantiate `root_soundness`, at `n = 1` and `n = 0`, so neither has a
chain step; the other 5 target `stepSound_of_programDecodes`, which keeps its signature. Migrating
those 5 off hand-written traces (13 chain steps, via the `Dispatch/` equivalences rather than by
reducing Sail's `execute`) is real work and is **not** done. Remaining besides that: **#344**, the coverage gap that
nothing exercises `rowsAligned` against a real two-row JALR lowering (the only such witness sits at
`numInstructions = 0`; retirement condition recorded in `trust/defects.md` as
`ZISK-MODEL-GAP-JALR-EXPANSION-STEP-ROW-INDEX`). Earlier
sizing note kept for the record: no new extraction is needed — the a-side operand-sourcing
constraints (`main.pil:385`) are extracted and welded by PR #331, and the register MemBus
(`mem_op=3`) is modeled and balances since #225; both are currently consumed by nothing.

### Aristotle Drive (CLOSED 2026-08-03)

Plan: `docs/ai/plan/archive/PLAN_ARISTOTLE_DRIVE.md` (archived; + `docs/refactor/FINAL-PLAN.md`
on branch `refactor-plan-docs`). **Line fully closed 2026-08-04**: all 18 stack PRs closed
unmerged, `refactor-*` worktrees removed, issues **#323**/**#324**/**#325** all CLOSED. The one
work item that survived, #325 wrapper-binder hygiene, landed as **merged PR #326** (provider
bundles `StaticBinaryProvider`/`ShiftStaticProvider`/`BinaryAddProvider` replace the raw
5-binder provider lists across 28 wrappers + 28 Equivalence + Dispatch/Construction; net −1,252
lines; V1+V2 19/19). Unticketed residue, owner aware: OpEnvelope constructors +
AeneasBridgeTrust builders keep raw provider fields (protected surface). Lake portability
declined; recipe reference = closed PR #255 / branch `aristotle-portability`.

## Archived

Completed, superseded, or inactive plans live in `docs/ai/plan/archive/` (moved 2026-07-22):
the Endgame campaign (ROADMAP, P1/P3/P4 family, P5, XCAP, AENEAS), Fanout Closeout (superseded
by Project Closeout), S3 Lookup Wiring (complete — #249 closed), Aeneas Bridge 111 (landed PR
#160), Arith Range Table 169 (closed), Clean Completeness + Proofs (complete, PRs #66–#73),
RV64IM Completeness Restack (landed), Defects on RowData / trace-local (landed), Root Soundness
Shape (landed), PHASE2_PER_OP_SPEC (historical), PR94 closeout research note.

### Mem Prefix 221 (complete — Stream S5, archived 2026-07-27)

Plan: `docs/ai/plan/archive/PLAN_MEM_PREFIX_221.md` (issues #221 and #74, both CLOSED). Landed as
PR #290 (`daa68b30`, the two-row store→load Mem provider table) and PR #291 (`4a03fe85`, the
`root_soundness` instantiation on the seven-instruction SD/LD/JAL-spin trace): the first accepted
non-empty mutable-Mem trace stores then loads 42, with the load reading back what the store wrote.
Zero new axioms; V1 17/17, V2 18/18, `lake build` 9074 jobs, `nix run .#test` 8/8. #290 also
repaired two elaboration-marginal proofs that had left `d4780eee` failing to compile.
