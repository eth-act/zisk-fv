# PLAN — Project closeout: complete the mvp milestone, no punts

## Context

The project is winding down. Owner ruling (2026-07-13): **go for completeness — no punting.**
This plan supersedes `PLAN_FANOUT_CLOSEOUT.md` (its streams 1–2 landed as PRs #250/#252; its
streams 3–5 carry over here, rescoped) and extends to the actual finish line: every open
**mvp**-labeled issue closed with landed Lean work, the two legible root theorems
(`root_soundness`, the completeness endpoint) non-vacuous with every premise derived or named
trust, and a reader-facing closing audit. The 2026-07-10 ruling that parked the #74 ladder is
**rescinded** — #221/#74 are now in scope, sequenced below.

**What changed vs the fanout plan:** `mem_replay_segment_ranges` is NOT retained as a permanent
named survivor. It is held only until Stream S3 (lookup-wiring extraction) derives and deletes it.
#249 therefore stays open across S1+S3 and closes when the field is gone.

## WHERE WE ARE (dashboard — maintain this section first; updated 2026-08-06)

**Position: S1–S8, S7b, S8b, and S11 (PART I round-trip) landed, plus the #297/#298 repair stack.
S9 (#61) is complete: PRs #313–#318 all MERGED 2026-07-30, `root_soundness_rawProgram` fully gated
(9,132-job `lake build`, V1 18/18, V2 19/19, `nix run .#test` 8/8, 0 new axioms) — #61 is ready to
close. Its #320 non-vacuity follow-on merged in PR #335 as `9b65f7b7`: the raw binding premises now
have production-faithful witnesses and a real executed `Fin 1` ADD instantiation. S11's round-trip
gate is green on `main`
(`176/176, 0 failing`); its only forward items (#328 cross-segment, #330 InputsAgree discharge) are
deliberately out of the PART I finish line.**
Both PRs were reviewed 2026-07-28 (no blockers; V1 17/17 and V2 18/18 on each branch pre-rebase)
and merged the same day: **#293 → `fac67c2f`** (first, because it changes the public
`root_soundness` conclusion shape), then **#294 rebased onto it → `2da97416`**. #280 and #279 both
auto-closed COMPLETED. The one rebase conflict (`StepStrongControlStore.lean`) resolved in S7's
favour; details in S8's closing checklist item.

**✅ Verification debt from the merge — RESOLVED, and it was real.** The post-rebase gate that
was still in flight when #294 landed did fail. CI on `main` (`proofs` run 30367646088) failed the
semantic gate on BOTH root-soundness probes: `DivSpinRootSoundness.olean` and
`JalrSpinRootSoundness.olean` "does not exist". Root cause was a packaging gap, not a proof error —
`ZiskFv` is a root-based Lake library (`roots = ["ZiskFv"]`, no globs) and neither #293 nor #294
imported its witness from `ZiskFv.lean`, so `lake build` never compiled them; the probes had been
passing on developer machines only because of leftover explicit `lake build +<module>` runs. Putting
them in the graph then exposed **four** genuine breakages, one per direction of the merge (each PR's
witness was written against the other's pre-merge shapes), including that #294's headline concrete
DIV `root_soundness` instantiation could not compile against merged `main` at all.

Repaired and merged the same day: **PR #297 → `01f5a5ba`** (imports + the four breakages) and
**PR #298 → `e19f012e`** (the remaining four orphan modules + a V1 reachability gate). `origin/main`
is now `e19f012e`. Standing lesson, worth keeping: *a green gate on a module the build never
compiles is not evidence.* V1 check 18/18 (`check-module-reachability.py`) now makes that failure
mode a build error; it is allowlist-free and comment-aware (a naive line regex would read an
`import` out of a docstring and re-open the hole). Note it runs push-to-`main` only — no workflow in
this repo has a `pull_request` trigger, so the PR→merge window is still unguarded.

The review also added **S7b/#295** (JALR's committed-ROM decode provenance, collapsed by S7) and
left two owner calls on S8, now merged and therefore live: the hand-audited (not machine-welded)
`ArithCompleteConstraints` mirror, and the new `SignedDivQuotientSignForge` defect exclusion plus
reshaped `OpEnvelope.div` / `RowOutsideDefectRegion` protected surfaces.
S6 landed
2026-07-27 as PR #292 (`a60b2bd5`); **#281 CLOSED** after adversarial review corrected the
trust-boundary wording and distinguished Arith's in-component static lookup from the separate
channel-balanced slice-provider routes. S5 landed
2026-07-27 as PR #290 (`daa68b30`) and PR #291 (`4a03fe85`); **#221 and #74 both CLOSED**;
`origin/main` tip = `a60b2bd5`. The full S4 stack landed
(#285/#286/#287/#288/#289) but `d4780eee` did **not** compile — the two elaboration-marginal
proofs flagged in the S5 checkpoint (`MemBusRowBridges`, `BootSegmentMemorySeed`) were genuine
breakage, caught only because S5's root build required them, and repaired inside PR #290. CI
confirms `proofs.yml` failed on `d4780eee` and on `#287`; `#286`/`#288` were cancelled. Neither
S5 PR carried any status check — the push-only `proofs.yml` trigger means PRs are never gated,
so **run `nix run .#test` locally before every merge** and treat a "green PR" as meaningless.
**#242 CLOSED.** MemAlign read-soundness is proven with two real ZisK v0.17.0 defects named and
excluded (narrow-load value-lane forge — *our unreported find*; skippable-prove #1142 — upstream-
known); step-desync #1116 did not surface; AUIPC left as a known completeness gap (we reported it,
ZisK PR #1143). Soundness defect ledger now 5. Owner ruling 2026-07-22: this thread is the
priority; the Aristotle refactor stack DRIFTS. Follow-on: a Docker repro of the narrow-load bug is
in progress in `~/zisk` (plan `~/zisk/mem-align-narrow-load-repro-PLAN.md`) — repro scope is that
one bug only (the others are already known to ZisK).

| Stream | Scope | State |
| --- | --- | --- |
| S1 | #249 row-level certificates | ✅ DONE — PRs #253, #258 |
| S2 | #243 + #226 Clean-fork facilities | ✅ DONE — PR #254; both issues CLOSED |
| S3 | lookup-wiring extraction | ✅ DONE — PRs #259/#263/#265/#266; **#249 CLOSED**; #268 detour CLOSED via #270 |
| S4 | #242 MemAlign read-soundness | ✅ DONE — PRs #285/#286/#287/#288/#289; **#242 CLOSED**; +2 named defects (narrow-load, skippable-prove) |
| S5 | #221 → #74 non-degenerate memory witness | ✅ DONE — PRs #290 (`daa68b30`) / #291 (`4a03fe85`); **#221 and #74 both CLOSED**; +2 `origin/main` build repairs riding in #290 |
| S6 | #281 ArithTable stale-doc disposition | ✅ DONE — PR #292 (`a60b2bd5`); **#281 CLOSED**; focused build + V1 17/17 green |
| S7 | #280 Main source-C copy | ✅ DONE — PR #293 merged `fac67c2f`; **#280 CLOSED**; residual #295 spun out as S7b |
| **S7b** | **#295 JALR committed-ROM decode provenance** | **✅ DONE — PR #299 merged `5b1f4fca`; #295 CLOSED; build/V1/V2 and eight-stage `nix run .#test` green** |
| **S8** | **#279 Arith Div-block model coverage** | **✅ DONE — PR #294 rebased onto `fac67c2f` and merged `2da97416`; **#279 CLOSED**; +1 defect (quotient-sign, ledger now 6); post-rebase gate ran after merge by owner ruling** |
| **S8c** | **#297 + #298 merge repair + build-graph gate** | **✅ DONE — merged `01f5a5ba` / `e19f012e`; 6 orphan modules resolved, V1 check 18/18 reachability gate lands allowlist-free, signed-DIV counterexample repaired and its axioms pinned (V2 check 9/19)** |
| **S9** | **#61 decode-driven export (was S6)** | **✅ DONE — additive `root_soundness_rawProgram`; 63/63 arms; PRs #313–#318 all MERGED 2026-07-30 (`bd9939f1` = #318 tip); 9,132-job `lake build`, V1 18/18, V2 19/19, `nix run .#test` 8/8, 0 new axioms. #61 ready to close (body's merge-gate satisfied). Non-vacuity of the new `ProgramRowsBinding`/`RawProgramDecode` premises → #320.** |
| S10 | capstone #186 + #184 + sweep (was S7) | last — #184 is only honest after S7/S8 |
| **S8b** | **#296 mirror welds (7-PR fan-out)** | **✅ DONE — #300/#305/#306/#307/#308/#309/#310 reviewed and merged through `740f4429`; six focused weld builds, final 9,132-job `lake build`, V1 19/19, and V2 19/19 green. #310 now discovers every weld module plus every circuit instance and pins 11 forward/inverse carriers against nine generated AIR headers, including #308's inverse maps. The three documented model-scope gaps remain explicit inputs to S11 rather than hidden weld claims.** |
| **S11** | **#303 + #304 round-trip verification** | **✅ DONE (PART I) — gate green on `main`: `176/176 comparable, 0 failing` (139 matched + 15 out-of-root + 4 bool-typed + 16 weld-covered + 2 declared reclass; 2 strengthening + 3 unbacked declared). #303 MERGED (PR #312, extraction round-trip). #304 MERGED (PR #327, mirror round-trip). The 9 Main gaps were the circuit's segment-boundary public-value checks (`FullEnsemble.lean:293` was `PublicIO = unit`); closed by **PR #331** — a `MainExposed` carrier + `Iff.rfl` welds — which also added the consumed-check (Track B: 35 consumed / 11 fidelity-only). Residuals (#329) + a real MemAlign L1 `fixedColumns` fix (#332) landed as **PR #333**; both issues CLOSED. #333's anti-laundering pin-check (`_unbacked_clause_is_definitional_pin`) survived three review rounds — committed-cofactor, then two cancellation holes — each with a locking acceptance mutation (25 cases). Forward, out of PART I scope: **#328** (cross-segment continuation = ladder C4, beyond mvp) and **#330** (discharge `InputsAgree` via a register-file simulation, blocked by #184). Superseded intermediate PRs #319/#321/#322; plan `~/.claude/plans/deep-napping-abelson.md` also superseded.** |

**Completeness (#108/#182/#183/#154, #174) is parked in PART II and is not being worked.**

Finish-line scoreboard: **11 closed**, plus the #297/#298 repair stack merged (#249, #243, #226,
#242, #221, #74, #281, #280, #279, #295, + detour #268). Soundness track open:
**#61, #184, #186**. Soundness defect ledger now **6** (S8 added the signed-DIV quotient-sign exclusion,
reproduced by codygunton/zisk#12). Completeness track parked: **#108, #182, #183, #154**.

**Structure (2026-07-27):** this plan is split into **PART I — soundness** (the active work) and
**PART II — completeness** (parked, not a current worry). The soundness sequencing rationale —
including why #279/#280 are *behind* the binders rather than beside them, and why #281 turned out
stale — is in "Soundness finish line" immediately before S6.

**Rescued-worktree disposition (needs an owner decision, small):**
`.worktrees/closeout-cert-burndown` holds the closeout thread's pre-S3 state rescued from the
base checkout on 2026-07-18. It is based on **#160-era main** (weeks stale) and contains:
(a) unpushed doc-only commit `b35df9b9` "Document proof generation flow map" (README.md +30/−19)
— possibly worth rebasing onto current main as a small doc PR; (b) a dirty
`ZiskFv/AirsClean/RangeTables.lean` draft (355 lines divergent from merged main) — an early
Stream-3 exploration **superseded by the merged S3 stack**, recommend discard; (c) a dirty
`trust/proof-tree/index.html` tweak (56 lines) — assess with (a). Nothing here blocks S4.

Cross-thread coordination: the Aristotle refactor stack (PRs #255–#276, separate thread) is
actively reworking Binary/Arith consumer surfaces. S4+ touches MemAlign/Mem — lower overlap, but
whichever thread rebases second across Arith/Binary territory should expect conflicts and
reconcile deliberately (see base `STATUS.md`).

## Defect watch (standing — every agent and every review reads this)

External context (owner, 2026-07-22): there is credible, deliberately unspecific word from the
ZisK team that defects similar to the three we found exist and are not yet exposed, in **table or
inter-channel** territory. Treat this as an experimental control: do NOT hunt, do NOT bias the
modeling — faithful verification is the instrument, and the bugs should be forced out by proofs
that refuse to close. What this section changes is *recognition*, not behavior.

**First control hit CONFIRMED (2026-07-23, S4):** the MemAlign narrow-load value-lane forge —
found blind, no hunting, by the S4 timeline proof refusing to close on `value < 2^(8·width)`.
It is genuinely new/unreported (distinct from eduadiez's #1142 skippable-prove and #1116 step
fixes; not in any ZisK PR/issue), matching the "table/inter-channel" hint. Now ledgered as
`ZISK-DEFECT-MEMALIGN-NARROW-LOAD-LANE-SOUNDNESS` and excluded via `RowOutsideDefectRegion`; a
Docker repro is in progress in `~/zisk`. The methodology worked exactly as designed.

Recognition discipline. Every anomaly so far has been benign and matched one pattern: a shape
mismatch traceable to a specific PIL rendering habit, with source, bus, and tuple all agreeing
(zero-tail, assumes sign-form, mixed-no-hint). A real defect looks different — one or more of:

1. an obligation that closes only at a **weaker bound than the Sail spec** (the LT_ABS_NP
   signature: in-model `≤` where Sail says `<`);
2. a table/ROM whose exact-membership enumeration contains **rows enabling wrong semantics**
   (the ArithTable signed-witness-forge signature) — including ROM rows validating unintended
   control-flow transitions or a malicious cyclic wrap;
3. channel balance provable only by pairing a **different message than the semantic one**, or
   multiplicities that cancel under an unintended pairing (the inter-channel class);
4. the circuit **accepting less than spec** (the FENCE signature — completeness side).

Likely surfacing points, in order: S4's timeline proof (first semantic consumption of the
MemAlign byte tables), the cyclic wrap instance (last-row→row-0 emission vs ROM content),
MemAlignRom control flow, multiplicity evaluation from real emissions (#219 territory), S5's
concrete store→load witness (honest-trace unsatisfiability = completeness bug), later
SpecifiedRanges/VirtualTables composition and Track B #183.

The post-mvp coverage ladder (C1–C4 below) exists partly to shrink this blind spot: C1/C2 close
the transcribed-channel and un-composed-AIR hiding places, C3/C4 bring the misaligned and
cross-segment territory inside the instrument.

Required response on a suspected hit: STOP and report with the concrete extracted terms, the
obligation that failed, and which signature it matches. Never weaken a bound, add a case split,
scope a lemma, or adjust a `Valid_<AIR>` to make a proof close — that is exactly how a real
defect gets laundered into a modeling choice. Carve-outs (defect ledger + `RowOutsideDefectRegion`)
happen only after owner sign-off; upstream reporting is the owner's call. Reviewer side: every PR
review asks explicitly "did any obligation get weakened, scoped, or case-split to close?"

## Finish line (checkable)

- Closed with landed work: #249, #243, #226, #242, #221, #74, #61, #184, #186 (soundness track)
  and #108, #182, #183, #154 (completeness track).
- `AcceptedZiskTrace` certificate fields reduced to the original seven plus survivors that are
  **protocol-soundness class only** (challenge-balance trust) — no constructibility certificate
  survives that the model can derive.
- 0 project axioms maintained; V1+V2+`nix run .#test` green on main; `trust/trusted-base.md` and
  `trust/README.md` reflect the end state; #184's premise audit is the project's closing statement.

**Explicitly out of mvp (owner-labeled beyond-mvp or previously ruled):** #75, #77, #78, #172,
#174 (kernel purity / external checking / Sail grounding research items); #222 (hand-authored
witness literals with regen recipes remain the accepted precedent); hygiene backlog
#116/#118/#127/#128 except where #186 subsumes pieces; #173 standing infra.

## Post-mvp coverage ladder (owner ruling 2026-07-22: cover eventually — not in the mvp finish line)

Sequenced by current marginal cost; each becomes its own stream with issues when activated. All
three overlap the standing Defect-watch blind spot (item 6), which is part of the motivation.

- **C1 — full lookup-wiring link coverage.** Extend validated links across the remaining
  bus-5000/op-bus and family constraints using the existing template vocabulary (direct, cluster,
  derived-mixed, zero-tail, sign-form); converts the last transcribed channel surfaces into
  kernel-checked wiring, closing Defect-watch hiding-place 3. Mostly mechanical post-S4.
- **C2 — compose the un-composed AIRs.** Full SpecifiedRanges and VirtualTables as composed
  provider components (slice pattern generalized), remaining Arith range internals. Mechanical
  extraction + provider work on the S3/S4 pattern.
- **C3 — Zicclsm (misaligned accesses).** Natural S4 follow-on: Sail-profile variant allowing
  misaligned accesses + misaligned arms on the load/store equivalence theorems, riding the proven
  MemAlign timeline. Blocked until S4 lands.
- **C4 — #103 cross-segment composition.** Statement-level first: segment-boundary interface from
  the existing sidecars, N-segment chain composition theorem, recursion/aggregation layer as ONE
  named trust class (same epistemic standing as channel balance), with the banked addChannel seam
  capability as input. Full recursion-circuit extraction stays out (a separate project if ever).
  Comparator-gadget territory — Defect-watch relevant.

---

# PART I — SOUNDNESS TRACK (active — this is the work)

## Stream sequence (one at a time; reviewer pass before every merge; V1 every push)

**Renumbered 2026-07-27** when the model-coverage issues were sequenced in: old S6 (#61) is now
**S9**; old S7 (capstone) is now **S10**. S6/S7/S8 are new streams for #281/#280/#279.

### S1 — #249 row-level (COMPLETE; #253 + #258 MERGED)

#### S1 execution checklist

- [x] Spike the verifier-side fixed-column derivation of `main_step_index_fixed`.
  Result: BLOCKED on a Clean indexed fixed-column facility. `Air.Flat.Table` supplies only an
  unindexed raw row and shared `ProverData` to component constraint/interaction evaluation;
  `main_step` is a raw Main witness input that drives MemBus timestamps. Existing
  `segment_l1_fixed` / `segmentWithFixedL1` precedents do not change that. A projection-only
  override would decouple the proof from the modeled interaction, so it is not a derivation. The
  Clean facility must include an intrinsic no-wrap/domain bound; adding one as a caller-supplied
  promise would not shrink the trust surface.
- [x] Derive and delete `main_step_index_fixed` through the landed indexed fixed-column facility;
  delete `segment_l1_fixed` through the identical canonical route in the same PR. Both derive only
  from the selected Main component's canonical indexed fixed schema and intrinsic fixed-domain
  bound; staged-diff and anti-laundering review found no new caller-supplied hypothesis, axiom,
  `sorry`, native decision, or obligation weakening.
- [x] Compose the Mem row range lookups into the live component and delete
  `mem_replay_row_ranges`. The accepted trace now derives them from its selected table's live
  `constraints_hold`; no replacement caller-supplied field was added.
- [x] Verify no theorem consumes an exact previous-step premise; compute the register timestamp
  chains in the `ofRows` witness builder and remove all hand-written previous-step literals.
  Audit found no such consumer; constructor work is local commit `6aec5c99`.
- [x] Mark `mem_replay_segment_ranges` HELD for S3 in its declaration and in `trusted-base.md`.

Current checkpoint (2026-07-14): S1a merged as PR #253 (`5d39717e`). It computes concrete witness
register predecessor chains, composes the live `mem.pil:384-385,397` lookups, derives and deletes
`mem_replay_row_ranges`, and marks segment ranges HELD for S3. Focused component/trace/witness
builds, V1, full `lake build`, V2, and `nix run .#test` passed; no baseline regeneration was
required. Independent review found no blocking issue; the non-vacuous mutable-Mem fixture gap stays
in S5/#221. `main_step` remains exclusively S1b after S2's facility (ii).

S1b checkpoint (2026-07-15): PR #254 merged as `ed6ba409`, closing #243 and #226 and making
facility (ii) available on `origin/main`. S1b began in
`.worktrees/issue-249-certificate-burndown` on `issue-249-fixed-columns`; it will derive and
delete `main_step_index_fixed`, then delete `segment_l1_fixed` if the same component-owned fixed
schema proves it. #249 remains open until S3 derives and deletes the HELD segment-range field.
The first focused S1b check is green: Main's public canonical-row projections read only fixed
slots 17 (`SEGMENT_L1`) and 37 (`main_step`) through structural `ProvableStruct` evaluation. No
accepted-trace field, caller premise, or alternate projection path was added.
The canonical Main-table bridges now derive the row-index/timestamp no-wrap facts and the complete
`SEGMENT_L1` shape through the intrinsic fixed-domain bound. Both corresponding `AcceptedZiskTrace`
fields are deleted; the degenerate, Single-ADD, ADD-spin (including padded), and ADD/ADDI-spin
constructors have dropped their bespoke proofs. Focused constructor and `BootSegmentMemorySeed`
builds are green, the pinned full `lake build` is green (9,044 targets), V1/V2 are green with no
baseline regeneration required, and `nix run .#test` passes all eight stages; the trust ledger
records the facts as derived. Staged-diff and anti-laundering review found no blocking issue. S1b
is committed as `ce4879fc` (`#249: derive Main canonical fixed-column facts`). The committed-tree
V1 rerun passed and review PR #258 is open at https://github.com/eth-act/zisk-fv/pull/258; it
references but does not close #249. Owner review accepted and merged PR #258 as `13d7dbcb`.
S1 is complete: both fixed-column certificates are deleted, and #249 remains open only for S3's
HELD `mem_replay_segment_ranges` deletion.

**Owner ruling on the blocker (2026-07-13, second ruling):** the spike finding is accepted; the
indexed fixed-column facility is sequenced into S2 as a second minimal fork patch. S1 splits:

- **S1a (resume NOW, this worktree):** the facility-independent items — compose the Mem row range
  lookups and delete `mem_replay_row_ranges`; builder-computed register timestamp chains, deleting
  all hand-written prev-step literals; the HELD docstring on `mem_replay_segment_ranges`. Lands as
  one PR referencing #249. Do not touch `main_step`.
- **S2 (next):** the pinned Clean fork now carries TWO orthogonal minimal facilities — see S2.
- **S1b (after S2):** delete `main_step_index_fixed` via the fork's indexed fixed-column facility,
  applied consistently to constraints, interactions/balance, transitions, and projections, with
  the domain/no-wrap bound intrinsic to the facility (never a caller-supplied promise). Same
  class, same PR: evaluate deleting `segment_l1_fixed` too — it is the identical fixed-column
  certificate and the no-punt ruling wants it gone if the facility makes it cheap.

Rescoped per owner ruling 2026-07-13:
1. **`main_step_index_fixed` via the fixed-column route** the issue pre-ruled (`segment_l1_fixed`
   shape / `segmentWithFixedL1` precedent). PIL's `STEP` is an expression over preprocessed fixed
   columns (`main.pil:90`) — model it as verifier-side fixed data and the certificate deletes
   definitionally. **Spike this first; do NOT build a counter-transition** (unfaithful mechanism —
   the real AIR has no such identity — and it collides with the #226 limitation that S2 exists to
   fix). If the fixed-column route genuinely needs Clean surgery, stop and fold the finding into S2.
2. **`mem_replay_row_ranges`** via in-component `Table.fromStatic` lookups (agent-verified
   tractable; no provider composition needed).
3. **Prev-step chain pins**: first verify by grep that no theorem consumes an exact-prev-value
   fact; then make the `ofRows`-style builder COMPUTE the register timestamp chain from the access
   history (the #250 telescope machinery), deleting the hand-written literals from all witnesses.
   Balance inversion is not required and must not be built for this.
4. **`mem_replay_segment_ranges`**: leave the field in place with a docstring pointing at S3.
   Do not delete (an unlinked static table proves nothing about the sidecar) and do not mark it a
   permanent survivor. #249 stays open; S1 lands as a PR referencing (not closing) #249.

Exit: S1 PR merged; the three row-level items discharged; witnesses literal-free.

### S2 — #243 + #226: pinned Clean fork — TWO minimal facilities (MERGED)

1. Pinned Clean fork (github.com/codygunton or eth-act mirror) with two orthogonal, minimal,
   upstream-shaped patches; `flake.nix` points at it; `nix run .#populate`; fork noted in
   `nix/README.md` + `trusted-base.md` (build-input trust moves with `flake.lock`):
   - **(i) channels + transition coexistence** on one component (the original #226 patch);
   - **(ii) indexed verifier-side fixed columns** for `Air.Flat.Table`: per-row fixed data
     visible consistently to constraint evaluation, channel interactions/balance, transitions,
     and table projections, with the domain size (and hence no-wrap bounds like
     `4·i + 3 < GL_prime`) intrinsic to the facility. This is the S1 blocker's requirement,
     verbatim; it also serves S3's static range tables, #242's MemAlignRom, and the
     `segment_l1_fixed` deletion.
2. Composed Mem component gets `Component.transition` carrying the generated cross-row
   constraints (#163 Main-PC-handshake precedent); derive `mem_replay_constraints` from
   `constraints_hold` + `transitions_hold`; delete the field; update witnesses.
3. Then S1b executes (see S1): `main_step_index_fixed` deleted via facility (ii), and
   `segment_l1_fixed` evaluated for the same deletion.

Do this BEFORE S3 so the Mem model and witnesses churn once. Exit: #243 and #226 closed, S1b
landed, facility (ii) available to S3/S4.

Current checkpoint (2026-07-14): established branch `issue-243-226-clean-fork` from S1a's merge
`5d39717e`; `nix run .#populate` is green. The spike verified that pinned
`codygunton/clean@497e4a41` already carries facility (i), D1's additive transition surface, so S2
will preserve and upgrade it rather than duplicate it. A pair-only transition cannot derive every
generated Mem equation: it lacks the row index, shared `ProverData`, row-0 predecessor semantics,
and final-row fixed-column rotation. The generated formulas need only predecessor/current witness
rows; their `i + 1` terms are periodic fixed-column reads. The fork patch will use one
right-indexed predecessor/current transition, bound by the component constructor to its canonical
fixed schema. The fixed-data spike also verified that Mem's fixed `SEGMENT_L1`/`__L1__` are separate
from its 13 trace columns, while instantiated Main/Mem physical domains are `2^22`; facility (ii)
will compute effective rows from raw rows with a component-declared append/replace layout and
periodic physical-domain access. Canonical `Table.table` will feed constraints, interactions/
balance, transitions, and projections. Its narrowly structural capacity bound is used by the
facility itself and will never become an `AcceptedZiskTrace` certificate or semantic premise. No
Clean, flake, trust, or proof change has yet been made in S2.

Fork checkpoint (2026-07-14): `codygunton/clean` branch
`air-flat-indexed-fixed-columns` commit `c87617d8` implements the two Clean primitives: an
all-row right-indexed predecessor/current transition and canonical effective `Table.table` rows
materialized from raw rows by a declarative periodic component-owned fixed layout. Focused
`Clean.Air.FlatComponent` / `Clean.Air.FlatEnsemble` and full `lake build Clean` passed; the fork
branch is pushed. S2 now pins and integrates that commit. The Mem proof must read canonical
`table.data` plus component fixed columns; legacy trace sidecar fields cannot be correlated by a
new equality premise and remain unconsumed pending S3's lifecycle audit.

Integration checkpoint (2026-07-14): S2 pins immutable `c87617d8` in `flake.nix`/`flake.lock` and
`nix run .#populate` is green. The first concurrent focused Lake invocations raced while this
fresh worktree initialized package artifacts, so they were canceled without treating their
artifact failures as source failures; project verification resumes serially.

Low-level integration checkpoint (2026-07-14): the staged project code separates canonical live
Mem sources from compatibility-only legacy decoders. `Mem.SidecarColumns` owns selected
`ProverData` accessors plus physical `SEGMENT_L1`/`__L1__` slots, and `Airs.Mem` names the 15
non-local segment residual equations with a reconstruction theorem against the existing nine
local equations. Main now declares the raw-41/effective-43 component schema and right-indexed PC
adapter. No accepted-trace field or caller-supplied correlation premise was added; focused Lean
verification is green for Main, `Mem.SidecarColumns`, `Mem.GeneratedTransition`, and
`Mem.Circuit`.

Implementation design checkpoint (2026-07-14): Main's fixed schema is raw-41/effective-43 with
fixed `SEGMENT_L1` and `main_step` at effective slots 17 and 37; Mem is raw-13/effective-15 with
appended fixed `SEGMENT_L1` and `__L1__`. Both use the intrinsic physical `2^22` capacity. Mem's
transition will carry exactly the 15 non-local segment equations and all 10 permutation equations,
while its live row constraints retain the existing nine local equations. The full generated facts
will be derived from the selected table's canonical `ProverData`/fixed schema and live
`constraints_hold` plus `transitions_hold`; no legacy sidecar correlation hypothesis is permitted.
S1b then derives both Main fixed-column facts from the same facility.

Main materialization checkpoint (2026-07-14): `mainRawRow` now explicitly owns the 41 raw cells,
and its reconstruction is proved componentwise (`MainRow` plus `MainRomRow`) rather than by
forcing derived 43-cell flattening. The public evaluator and live-component `rowInput` theorem
consume only the two component-owned fixed-cell equalities; no caller-supplied representation
equality or accepted-trace premise was added. A serial focused Main build is green, and the
concrete-table migration has resumed against that API.

Mem materialization checkpoint (2026-07-14): `memRawRow` owns the 13 raw witness cells, with
`SEGMENT_L1` and `__L1__` appended as component-owned fixed data. Its evaluator and live
`componentWithDualMemBus.rowInput` theorem need no premise; serial focused builds of the generated
transition and Mem component are green. The first projection-bridge build reached only local new
Table API adaptations (fixed-schema rewriting, row-zero saturation, and the `Table.length` index
conversion); the canonical source and no-correlation design remain unchanged.

Physical-rotation checkpoint (2026-07-14): canonical Mem fixed data rotates at the physical domain,
so it is not globally equal to the legacy non-rotating `segmentWithFixedL1` adapter. S2 therefore
stages a replay bridge over the actual segment with a derived fixed-column fact; compatibility
constructors derive that fact locally and the accepted-trace route will derive it from the component
schema. No replacement caller-supplied hypothesis or accepted-trace field has been introduced.

Certificate checkpoint (2026-07-14): the canonical table-projection bridge is focused-build green.
It derives generated Mem constraints from the selected table's live row constraints plus its
right-indexed transition, with pointwise predecessor/current decoding and no false global
fixed-column equality. `mem_replay_constraints` is deleted from `AcceptedZiskTrace`; its replacement
is a theorem over canonical table `ProverData` and component-owned fixed data, not a renamed field or
new caller promise. The HELD `mem_replay_segment_ranges` field is aligned to that canonical source.
Focused builds of `Mem.GeneratedTransition` (including the small-domain physical-rotation regression),
`TableProjections`, `RowsBridgeFacts`, `TimelineEvidence`, `AcceptedZiskTrace`, and Mem providers are
green. `EnsembleWitnessBuilder` has migrated to raw rows plus the component-owned fixed-domain
invariant and its focused serial build is green. The fork divergence record now names D1 and D2 at
`c87617d8`. The first serial `ConcreteRowReductions` build reaches only local normalization work;
no defect has appeared in the Main/Mem materialization or canonical table design. The remaining
active work is completing that concrete-table migration, witness API migration, and final documentation.
The compatibility audit finds no remaining Lean reference to `mem_replay_constraints` or the removed
raw-source reconstruction accessors; the held range fact remains canonical and no correlation premise
was added. The remaining `ConcreteRowReductions` repairs are local prover/verifier-environment and
materialized-list normalization only; they preserve the modeled obligations and intrinsic table bound.
Dependent witness targets remain held until its serial result.
The second serial target reduced its remaining work to two local BinaryAdd/static-Binary raw-width
elaborations; private width-equality lemmas replace expensive component unfolding, without a new
API or caller-supplied premise.
Serial `lake build ZiskFv.Compliance.Instantiation.ConcreteRowReductions` is now green; the repair
remains confined to that file, with only non-blocking existing-style linter warnings. The focused
dependency chain advances to SingleAdd, then AddSpin/AddAddi and their consumers.
The first serial SingleAdd target reaches a stale `RegisterMemBusBalance` Main single-row consumer
before compiling SingleAdd: it expects the old raw environment, omits the two fixed-cell facts, and
has a downstream recursion-depth failure. Repair that narrow consumer, then resume SingleAdd.
The repair must use the live canonical materialized Main environment; the recursion-depth failure is
being solved as proof normalization, not by changing an obligation or trust surface.
Serial `lake build ZiskFv.Compliance.RegisterMemBusBalance` is green: it now evaluates the canonical
Main environment with its fixed-cell facts, and its six-interaction proof is structural rather than
recursion-heavy. Resume SingleAdd.
AddSpin's source review also migrated its stale prover/verifier evaluator bridge and confirms the
canonical materialized-row path with its intrinsic fixed-domain bound; its focused target remains
sequenced after SingleAdd.
Serial `lake build ZiskFv.Compliance.SingleAddWitness` is green after an explicit empty-table
normalization across the two fixed-column branches. Advance to AddSpin.
AddAddi's analogous explicit prover/verifier evaluator bridge is staged and its static audit is
clean; its serial target remains sequenced after AddSpin.
The first AddSpin target reaches stale `MainTransition` code before AddSpin: it supplies a `Nat` to
the indexed transition contract rather than `Fin trace.mainTable.length`. Repair that narrow
consumer and its PC-handshake goal, then resume AddSpin.
AddAddi's local fixed-cell equality inputs are discharged by `rfl` for each concrete row; they add
no accepted-trace field, caller premise, or alternate data source.
The indexed Main handshake uses `Fin ⟨i + 1, h_idx⟩`, whose predecessor/current contract models the
old row-`i` to row-`i+1` transition exactly. The API audit finds no remaining Lean reference to
`mem_replay_constraints`, `Table.width`, or `Table.uniform_width`.
Serial `lake build ZiskFv.Compliance.MainTransition` is green: it derives the raw/effective length
conversion from `Table.table_length` and structurally projects the canonical predecessor/current
environments, with no new trace premise or API. Audit-residue work is AddSpin's stale one-index
transition binders and the two root-soundness raw-Main-environment consumers.
AddSpin's transition branches and its root-soundness raw-Main consumers are being repaired
source-only in parallel; their builds remain sequenced behind the AddSpin target.
All eleven AddSpin transition branches now use the one-`Fin` contract, preserving the empty,
verifier, boundary, and BinaryAdd canonical cases. Rerun AddSpin.
The first AddSpin compiler pass reaches its local materialization migration: fixed-domain,
effective-table list/index normalization, empty branches, evaluator index forms, interaction
unfolding, and one case split remain. The indexed transition conversion itself has no diagnostic.
`AddSpinRootSoundness` is staged on the canonical Main table, replacing raw-array environments,
the retired evaluator helper, and stale `mainRowsTable` references; build it after AddSpin clears.
AddSpin is the sole active compiler repair; verify its already-migrated root consumer immediately
after that gate.
Its remaining proof work is local effective-row/length normalization around the component-owned
Main schema; the fixed-domain proof closes directly, with no new source or caller premise.
The focused rerun confirms every remaining diagnostic is local to AddSpin's materialized-table
proofs. Split that work into fixed-domain/constraint membership, indexing, empties, evaluator and
interaction groups for sharper serial reruns.
The first group is green: fixed-domain and constraint-membership errors are gone. Continue with
table-length/`Fin` normalization, then empty tables, evaluators, interactions, and the JAL case.
The indexing group, including zero-row transition normalization, is now green. Remaining work is
empty tables, evaluator projections, two interactions, and the JAL membership case.
The empty-table group is now green. Continue with evaluator projections, interaction reductions,
and the JAL membership case.
All evaluator projections are now green. Only two interaction-table reductions and the JAL
membership case remain.
The interaction proofs now reduce through a canonical three-row materialization lemma and reuse
their existing per-environment facts; no new data source is introduced.
Both interaction reductions are green. The only remaining AddSpin proof is a materialized JAL
interaction-list membership case split.
Serial `lake build ZiskFv.Compliance.AddSpinWitness` is green; only linter output remains. Advance
to its already-migrated root-soundness consumer.
Serial `lake build ZiskFv.Compliance.AddSpinRootSoundness` is also green without repair. Advance
to AddAddi.
The first AddAddi target reaches only its local materialization migration. Apply the same grouped
constraint/indexing/empty/evaluator/interaction/JAL sequence used for AddSpin.
The constraint-membership group is green. Continue with indexed tables/transitions, then empties,
evaluators, interactions, and the JAL case.
The four-row indexed table/transition group, including zero-transition normalization, is now green.
Continue with empty tables, evaluator projections, interactions, and the JAL case.
All AddAddi empty-table cases are now green. Continue with evaluator projections, interactions,
and the JAL membership case.
All evaluator projections are now green, including the ADDI pair. Only interaction reductions and
the JAL membership case remain.
Both interaction reductions are now green through the canonical four-row materialization. Only the
JAL MemBus membership case remains.
Serial `lake build ZiskFv.Compliance.AddAddiSpinWitness` is green; only linter output remains.
Migrate and verify its root-soundness consumer next.
Serial `lake build ZiskFv.Compliance.AddAddiSpinRootSoundness` is green after canonicalizing its
three Main-row evaluators and dependent table-length facts. All concrete witness owners and root
consumers are focused-build green; advance to broad integration verification.
Serial full `lake build` is green across all 9,044 targets. Proceed with trust V1/V2, baseline
review, and `nix run .#test` after final source/documentation review.
V1's Lean/trust stages pass, but its Aeneas production-boundary stage lacks this worktree's
`zisk/core/src/aeneas_extract.rs` source input. Restore that local setup without changing a gate
or allowlist, then rerun V1.
After initializing the pinned `zisk` submodule, V1 passes all 16 checks, including the Aeneas
production-boundary stage. Advance to semantic V2.
V2 passes its axiom/binder/closure stages and raw extraction closure checks, but its global ADD and
degenerate root consistency fixtures still use the pre-S2 table/builder/certificate API. Migrate
those fixtures to the canonical API without changing a gate or trust policy.
The degenerate root fixture is now focused-build green after canonicalizing its empty provider
tables, intrinsic builder bound, one-index transition proof, and deleted-field construction.
The global ADD consistency fixture is also focused-build green through raw rows, the no-fixed-schema
bound, and its canonical effective-row path. Rerun V2.
V2 now passes all 16 semantic checks; raw extraction/decode closures remain within the permitted
kernel set and baselines match without regeneration. Run `nix run .#test` next.
`nix run .#test` has passed cargo and production extraction and is completing its isolated Aeneas
Lean check; no error has appeared.
The isolated Aeneas Lean-check is quiet while dependencies initialize or fetch; keep the gate
running until it returns.

`nix run .#test` now passes all eight stages, including the isolated Aeneas Lean build, full
9,044-target Lake build, V1, V2, and flake evaluation. The expected false-probe rejection remains
intact and the checked baselines match without regeneration. S2 is ready for its final staged-diff
and anti-laundering review, then a review PR; S1b remains gated on this PR's approved merge.

Final-review checkpoint (2026-07-14): the local audit confirms the canonical replay derivation
uses only selected table `ProverData`, component-owned fixed columns, live constraints, and the
right-indexed transition; `mem_replay_constraints` is absent, while
`mem_replay_segment_ranges` remains explicitly HELD for S3. The fixed schema's effective rows are
the common source for constraints, interactions/balance, transitions, and projections. No new
project axiom, `sorry`, `native_decide`, allowlist edit, weakened obligation, or replacement
accepted-trace/caller-supplied promise was found. Independent review is in progress before staging.

Reviewer gate (2026-07-14): independent read-only review found no blocking trust-surface,
obligation-weakening, Clean-integration, or stale-API defect. It caught two documentation-only
inconsistencies, both corrected before staging: constructor wording now says generated constraints
and row ranges are derived, and `MainStepIndexFixedFacts` is labeled the temporary accepted pin
pending S1b rather than witness data. Commit and open the S2 review PR; do not merge or start S1b.

Commit checkpoint (2026-07-14): S2 is committed as `a4a4840`
(`#243/#226: materialize canonical indexed fixed columns`). The required pre-push V1 rerun passes
all 16 checks, including Clean integration, locality, zero-sorry, Aeneas delegation, and baseline
freshness. Push and open the review PR; do not merge or start S1b.

PR checkpoint (2026-07-14): S2 is open as
https://github.com/eth-act/zisk-fv/pull/254. It closes #243 and #226 on merge, explicitly enables
but does not close #249, and leaves S3 responsible for deriving and deleting the HELD segment-range
certificate. All required S2 gates and independent review are complete. Await owner review/approval;
do not merge or start S1b.

Merge checkpoint (2026-07-14): PR #254 merged as `ed6ba409`, closing #243 and #226. Its full
verification and independent review passed before merge. S1b may now consume facility (ii); S3
retains responsibility for the HELD `mem_replay_segment_ranges` certificate.

### S3 — lookup-wiring extraction (COMPLETE 2026-07-17; #249 CLOSED)

Merge checkpoint (2026-07-17): the four-PR stack merged to main in order — #259 `a45f8f31`
(typed lookup-wiring manifest), #263 `48d4092d` (bus-103 range provider bridge), #265 `93972452`
(derive `MemSegmentGeneratedRangeFacts`, delete `mem_replay_segment_ranges`; **closed #249**),
#266 `31176427` (five legacy sidecar fields deleted after lifecycle audit; MULH/MULHSU lookup
facts derived from the balance-selected Arith provider). All four passed full local gates
(V1+V2, `lake build`, `nix run .#test`) and independent review before merge; post-merge
`origin/main` is byte-identical to the gated stack tip. Follow-on investigation #268 (unlinked
hint dispositions) is also COMPLETE: Phase 1 dispositions (gsum_debug_data stub, Arith c61/c62/c64)
all benign, on record at the issue; Phase 2 landed as PR #270 `28ed2773` (Binary c10
constraint-derived `derivedMixed2` link + consumer connection to exact static providers), #268
CLOSED. No ZisK circuit anomaly surfaced anywhere in the S3/#268 territory.

#### S3 execution checklist

- [x] Refresh generated artefacts and complete the read-only survey. Result: mixed constraints are
  emitted in ten AIR artefacts, while `render_hint_operand` still zero-stubs ExtF-tainted
  `gsum_debug_data` slots; Mem's held range hints are affected. The full table and concrete
  decision gate are in `PLAN_S3_LOOKUP_WIRING.md` in the S3 worktree.
- [x] Spike a lossless typed lookup-wiring manifest, including accumulator-constraint and
  `std_sum.pil:696` global-sum links. Add the row-zero-saturation warning to
  `docs/clean-fork-divergences.md` in this first PR. (PR #259)
- [x] Recognise template-linked surrogate channels and add cited applications of the existing
  lookup/permutation protocol-soundness class; do not add a trust kind. (PRs #259/#263)
- [x] Compose recognised range channels with `RangeTables` and the necessary `SpecifiedRanges`
  slice; derive/delete `mem_replay_segment_ranges` and close #249. (PR #265)
- [x] Delete the five legacy Mem sidecar fields after lifecycle audit and retire the MULH/MULHSU
  shared lookup/range residue through the same route. (PR #266)

Extract the stage-2 lookup **wiring** as structure and derive surrogate channels from it, so the
challenge-mixed lookups stop being hand-transcribed or uncomposed:

1. **Extractor**: emit the stage-2 / airval accumulator (mixing) constraints uniformly — the
   currently ExtF-stubbed slots rendered as F-only syntax over opaque challenge symbols — plus the
   cross-AIR gsum aggregation wiring. (Mem's are already emitted: `permutation_every_row` carries
   `distance_base_0 · α + 103 + γ`. Survey which other AIRs' mixing constraints render in
   recognizer-friendly Horner shape — that survey is the spike.)
2. **Recognizer**: a generic derivation mapping an extracted accumulator family of shape
   `im · (mix(t) ) + sel = 0` to a surrogate-channel emission (tuple `t`, multiplicity `sel`,
   lookup id). Purely structural — no probabilistic content. The single existing
   protocol-soundness trust class ("the real challenge-mixed logUp certifies this channel's
   balance") gains new CITED applications, no new trust kind. Each application cites the extracted
   constraint + PIL line in `trusted-base.md`.
3. **Compose the static range tables** (`ZiskFv/AirsClean/RangeTables.lean`; SpecifiedRanges slice
   as needed) against the recognized channels; derive `MemSegmentGeneratedRangeFacts` from balance;
   **delete `mem_replay_segment_ranges`** (and any row-range residue S1 left). Closes #249.
4. **Same-route completeness items** (no-punt additions, same recognizer, marginal cost):
   - MULH/MULHSU indexed-range-lookup discharge — their only blocker is this fidelity gap;
     retires the signed-M export cap on this route.
   - Audit whether the `mem_replay_gsum/im0/im1/permutation` sidecar fields can be restructured
     onto modeled columns as a consequence; if yes, delete those too (design note, not a gate).

Spike-first: the pilout render-shape survey (1) decides feasibility per AIR before any modeling.
If a family renders algebraically normalized beyond recognition, that finding comes back as a
decision request with the concrete constraint text — not a silent re-punt.

Exit: #249 closed (all three families derived); MULH/MULHSU blockers retired; trusted-base updated.

### S4 — #242: MemAlign-family read-soundness (✅ COMPLETE — checklist reconciled 2026-07-27)

1. MemAlignRom as a first-class extracted static table — now an instance of the S3 recognizer/
   static-lookup route rather than bespoke modeling (`tools/pil-extract` + wrapper + populate).
   Still a slice of #108; the rest of #108 belongs to Track B.
2. The through-MemAlign timeline argument: Main pull → MemAlignByte/ReadByte byte assembly →
   Mem-table aligned reads → accepted replay, consuming the residues enumerated in #242
   (`MemAlignLoadProviderRomValueFacts`, `MemAlignCoreLookupFacts`, branch pins), generalizing
   #115 read-soundness beyond direct-Mem scope.

#### S4 execution checklist

- [x] Survey the MemAlign lookup/hint surface in the generated manifest (same read-only survey
      shape as S3's). The only out-of-template family shapes were exact zero-tail and direct
      assumes-neg forms; the owner approved distinct templates, accepted solely by kernel `rfl`.
      All active PIOP constraints are now linked; only the std_sum finalizers remain unlinked.
- [x] Extract MemAlignRom as a first-class static table via the S3 route (`tools/pil-extract` +
      wrapper + populate; exact provider slice following `BinaryTableSlice` /
      `SpecifiedRangesSlice`). The 256 source rows, including 68 exact
      `[0, 0, 0, 0, 0, 512]` reset-padding rows, are preserved.
- [x] Connect the recognized consumer wiring with no caller promise: h1022/h1049 now emit the
      exact aligned-read negative MemBus tuples from the byte-assembly AIRs; h1029/h1052 use the
      in-component 16-bit static table and h1030/h1053 the exact two-byte static product table.
      Their completeness ranges are `ProverAssumptions` only; soundness uses the lookup operations.
      MemAlign h998 emits the exact negative bus-133 tuple. D3 supplies `DELTA_PC` from the
      intrinsic cyclic successor view; finished-channel balance selects the static provider and
      derives exact ROM membership. The accepted trace carries this D3 relation as verifier-checked
      `cyclic_successor_transitions_hold`, never as a caller assumption or soundness-side
      `ProverAssumptions` premise.
- [x] Prove the through-MemAlign timeline (Main pull → byte assembly → Mem aligned reads →
      accepted replay), consuming and then DELETING the #242 residues
      (`MemAlignLoadProviderRomValueFacts`, `MemAlignCoreLookupFacts`, branch pins).
      **The blocker recorded here was resolved inside PRs #288/#289** — see the S4 closeout
      note below for the file/line evidence and the one caveat on what "consuming" meant.
- [x] Update `trusted-base.md` (MemAlign carve-out removed from the Sail Memory Timeline
      section); full gates + independent review; close #242. **`trusted-base.md:282` now reads
      "the former provider-side carve-out is closed"; #242 auto-closed on #289's merge.**

#### S4 checkpoint (2026-07-22)

- [#285](https://github.com/eth-act/zisk-fv/pull/285) (base `main`) contains the bounded exact
  MemAlign zero-tail / assumes-neg lookup templates. [#286](https://github.com/eth-act/zisk-fv/pull/286)
  stacks the virtual-ROM extraction, static provider, Clean D3 pin, and fork-divergence accounting.
  [#287](https://github.com/eth-act/zisk-fv/pull/287) stacks the consumer, finished bus-133
  provider-match proof, accepted-trace D3 certificate, and witness updates. All are OPEN with
  clean merge state; no merge has been requested or performed.
- #287's independent review found and then cleared an acceptance gap: the generated h998 tuple is
  now linked in Lean by `MemAlign.h998Wiring.sourceBinding`, which maps the actual rotated
  `(stage 1, column 4, row +1)` witness to the successor PC and proves the live tuple equality by
  `rfl`. The Nix suite guards c36's generated rfl identity.
- V1, full `lake build ZiskFv`, V2, `nix run .#test`, and independent review pass for the stack;
  no canonical binder or axiom-closure baseline moved. The wrap check found no circuit anomaly:
  row 0 and the 68 tail padding rows provide the required `[0, 0, 0, 0, 0, 512]` tuple.

#### S4 closeout (2026-07-27, coordinator — checklist reconciled against the tree)

The two boxes above sat unticked from 2026-07-22 to 2026-07-27 while the work they describe
actually landed in PRs #288/#289. Audited against `4a03fe85`, every item the "blocked" box
listed as missing is present and intrinsic:

| Listed as missing | Now at |
| --- | --- |
| gated `delta_addr` predecessor constraint | `ZiskFv/AirsClean/MemAlign/Circuit.lean:234` — `delta_addr - (addr - previous.addr) * (1 - reset) = 0`, cited to `mem_align.pil:116-117,142` / c1/c29 |
| predecessor register continuity (D1) | `Circuit.lean:235-242` — eight `down_to_up` continuities |
| successor register continuity (D3) | `Circuit.lean:255-263` — eight `up_to_down` continuities plus h998's `delta_pc = successor.pc - pc` |
| eight bus-107 register-range consumers | `MemAlign/Constraints.lean:123` + `AirsClean/MemAlignRangeSlice.lean` |
| stale `CrossRow.lean` comment references | gone; the only surviving `CrossRow` is the real `ZiskFv/AirsClean/Main/CrossRow` |

D1/D3 are checked by the accepted trace's `transitions_hold` /
`cyclic_successor_transitions_hold` certificates — intrinsic, as the box required, not caller
promises. Both residues are genuinely deleted: `MemAlignLoadProviderRomValueFacts` and
`MemAlignCoreLookupFacts` have zero references in `ZiskFv/`; the only three surviving mentions
are in `trust/trusted-base.md` and `trust/defects.md` recording their retirement.

**Caveat on "consuming", to state plainly:** the narrow-load residue was closed by derivation
**plus a named defect exclusion**, not purely by proof.
`Defects.MemAlignNarrowLoadLaneForge` negates the complete selected-row shape and
`RowOutsideDefectRegion` excludes it for LBU/LHU/LWU/LB/LH/LW only; that negation derives the
value shape at the bridge point and deletes `MemAlignLoadProviderRomValueFacts`
(`trusted-base.md:738-751`). This is the narrow-load value-lane forge — our unreported ZisK
v0.17.0 find — with a source repro in
`trust/consistency/memalign_narrow_load_lane_defect.lean` and an anti-vacuity guard
(`Defects.honest_memAlign_narrow_load_not_forge`). It does **not** cover `LD`, which is why
S5's LD instantiation is unaffected. Ledgered in `defects.md` with a count baseline, so it is
not laundering — but "residue deleted" and "residue proven away" are different sentences, and
the checkbox wording above reads like the stronger one.

**Process lesson:** a checklist box is not evidence. Reconcile boxes against the tree at every
stream closeout, not against the last checkpoint narrative.

Exit: #242 closed — read-soundness covers all RV64IM memory accesses at single-segment scope,
with the six narrow-load arms carried as a documented claim boundary.

### S5 — #221 → #74: the non-degenerate memory instantiation

Execute `PLAN_MEM_PREFIX_221.md` (already authored; its Phase 0 trigger is now "S1–S4 landed").
The surface is friendlier than that plan's worst case: S1 deleted `main_step_index_fixed` and row
ranges, S2 deleted `mem_replay_constraints`, S3 deleted segment ranges AND the five legacy sidecar
fields — the accepted-trace certificates are down to the structural core plus
`mem_replay_table`/`mem_replay_source_covers`, so the spike PR shrinks to the concrete Mem table +
per-row facts. Then close #74: its remaining OPEN criterion is exactly #221's artifact; the
"decode-driven instantiation" stretch is #61's (S6) and per #74's own text does not gate.

#### S5 execution checklist

- [x] Phase 0 setup per `PLAN_MEM_PREFIX_221.md` (**already reconciled against `d4780eee`
      2026-07-23** — the certificate-surface + defect-surface blocks in its header are resolved
      facts; just re-verify they still hold and re-resolve line numbers): create
      `.worktrees/issue-221-mem-prefix` manually from then-current `origin/main`, populate +
      cache + full build, STATUS.md.
- [x] Spike PR: the concrete 2-row store→load Mem table (SD then LD at one address, non-zero
      value) satisfying the live generated constraint surface, with provider emissions in
      balance-ready shape. If the table is unsatisfiable, STOP — that is a model finding, not a
      reason to weaken `Valid_Mem`. **MERGED 2026-07-27 as PR #290 (`daa68b30`); the table is
      satisfiable, so the make-or-break passed.**

#### S5 checkpoint (2026-07-23, coordinator)

Phase 0 complete: worktree `.worktrees/issue-221-mem-prefix` created manually from `origin/main`
`d4780eee`, populate + cache + full build green, STATUS.md current; worker0 executes via
ai-coord, coordinator lead0 in the base checkout. Phase 1 spike is built and fully gated (V1, V2
18 checks incl. the new `trust/consistency/memory_prefix_sd_ld_mem_table.lean` constructibility
witness, `nix run .#test`) and open UNMERGED as PR #290 — the 2-row store→load table satisfies
the full generated Mem surface, so the spike's make-or-break passed. Phase-2 construction then
exposed a plan-default defect: RegisterBoundary boot pulls are definitionally zero-valued
(`bootMessage`, faithful to `mem.pil:507-508`; `aRegPre_eq_boot` forces the first pull to match),
so nonzero x1/x2 cannot be boot-seeded and the plan's original 3-instruction program is
unwitnessable. **Coordinator ruling:** in-program ADDI/SLLI preamble computing
`x1 = 0xA0000008` / `x2 = 42` from zero-booted registers (program now 7 instructions + spin;
LUI avoided for RV64 sign-extension reasons); no new seed capability — that would be unfaithful
to the circuit. `PLAN_MEM_PREFIX_221.md` amended in place. PR #290's step-dependent literals
shift to SD/LD indices 4/5 and are being amended before its reviewer pass. Two narrow
statement-preserving `origin/main` repairs ride in the PR (MemBusRowBridges, BootSegmentMemorySeed)
— coordinator-reviewed, no obligation change; they indicate `d4780eee` carries two
heartbeat/elaboration-marginal proofs worth watching in CI.
- [x] Main PR: the SD/LD/JAL-spin witness — Main/RegisterBoundary rows, ensemble, balance, the
      first memory-carrying `BootSegmentMemorySeed` (real `boot`/`step`/`placement`/
      `readSoundInputs`, refl order certificate), `root_soundness` applied at all steps, V2 gate
      hooks mirroring the AddAddiSpin wiring. **MERGED 2026-07-27 as PR #291 (`4a03fe85`).**
- [x] Close #221 with the landed-work comment (program + regen recipe); tick #74's OPEN
      criterion and close #74. **Both CLOSED 2026-07-27.**

#### S5 closeout (2026-07-27, coordinator)

Reviewed both PRs independently before merge; verdict sound, merged on explicit owner approval.
Findings worth carrying forward:

1. **`d4780eee` did not compile.** `BootSegmentMemorySeed.lean` had an unconditional
   `(ma.value_0 0).val < 256` where `SubdoublewordLoadProviderWitness`'s fourth disjunct field has
   been width-*conditional* (`ma.width r = 1 → …`) since PR #13, plus a `norm_num` that cannot
   refute `(1 : FGL) = 2`; `MemBusRowBridges.lean` had a `/-- doc -/ set_option … in theorem`
   ordering that is a **parse error**, so its heartbeat bump never applied and two `whnf` timeouts
   followed. Both repaired in #290. The S5 checkpoint's "worth watching in CI" was an
   understatement — they were already red.
2. **`std_alpha = 0` is benign and should stay documented.** `Clean.Air.Balance.BalancedInteractions`
   is exact-message multiset balance (`.msg = msg` array equality), challenge-free, so the full
   MemBus tuple including the timestamp is bound between Main and Mem independently of the
   challenge. The α=0 fold-blindness only makes the *generated* logUp surface a weaker exercise
   than a generic challenge would give; it does not reach `root_soundness`.
3. **Squash-merging a stacked PR breaks the child.** #291 went `CONFLICTING` the moment #290's
   squash landed and #291 was retargeted; fixed with
   `git rebase --onto origin/main issue-221-mem-prefix issue-221-mem-prefix-root` (resulting tree
   byte-identical, re-verified with `lake build` before merge). Expect this on every future
   stacked pair.

Exit: #221 and #74 closed. ✅ **S5 COMPLETE.**

### Soundness finish line — what actually has to close (analysis 2026-07-27)

Written to answer: are #279/#280/#281 related to each other and to S6, in what order do they get
attacked, and is each specified well enough to execute. All claims below were checked against
`4a03fe85`, not against issue prose.

#### The measuring stick

`root_soundness` has exactly eight binders
(`trust/generated/baseline-strong-export-binders.txt`): `numInstructions`, `ziskTrace`,
`sailTrace`, `ziskStep`, `programDecodes`, `inputsAgree`, `bootSeed`, `hAvoidKnownBugs`. That
list is clean and stable — and it is **not** where the remaining weakness lives. The weakness is
*inside* binder 5, `inputsAgree`, whose per-op `Inputs_<op>` record is thin for some arms and very
fat for others. Contrast:

- `Inputs_ld` / `Inputs_sd` / `Inputs_addi` — register/PC/memory read agreement. S5 discharged all
  of these concretely with zero new axioms.
- `Inputs_div` (`RowDataArithMem.lean:1093-1140`) — the caller hands over **an entire
  `Valid_ArithDiv` legacy AIR model** plus `h_row_constraints`, `h_boundary`, `arith_table`,
  `arith_chunk_ranges`, `arith_carry_ranges`, `h_na_bool`, `h_nb_bool`, `h_nr_bool`, `h_np_xor`,
  `h_nr_pin`, … — the 16 premises of #279, sitting directly in a root-theorem binder.
- `Inputs_jalr` (`RowDataControl.lean:749-779`) — `h_operand_offset` asserts the committed Main
  `b`-lane already equals `rs1_val + signExtend imm` in **both** lowerings. In the unaligned
  lowering that is precisely what the un-modeled source-C copy chain of #280 would have proved.

**The honest metric is therefore not "how many binders" but "which arms can actually be
instantiated".** S5 instantiated ADDI/SLLI/SD/LD/JAL. **Nobody has ever instantiated DIV or JALR
concretely** — and #279/#280 are exactly why they would be painful.

#### Are they related?

Yes, but along **two orthogonal axes** that meet at one place.

- **Axis A — caller burden on the binders.** #61 (derive `ziskStep`/`programDecodes` from the
  committed raw program via the proven decoder), #172 (Sail-side grounding of that raw program,
  beyond-mvp), #184 (classify every surviving premise).
- **Axis B — model-coverage gaps behind the binders.** The Clean circuit the ensemble validates
  covers fewer generated constraints than the physical AIR, so facts that *should* be derivable
  are carried as `Inputs_<op>` fields. #279 (Arith Div block: `inv_sum_all_bs` unmodeled, Div
  `constraint_9-30/47-48` unvalidated) and #280 (Main `main.pil:386` source-C copy: not per-row,
  not on `Component.transition` — confirmed, `Main/Circuit.lean:932` is
  `transition := pcHandshakeTransition`, PC-handshake only).

They meet at **#184**. The premise audit's job is to say of every surviving premise "derived /
protocol-soundness class / cited defect-gate". That sentence cannot be written honestly while
Axis B leaves premises in the third, unnamed category — *"should be derivable, isn't, because our
model is thinner than the circuit"*. #279 says this outright and generalizes it to a **class**.

#### #281 is neither — it is stale

Checked: the file it names (`ZiskFv/Airs/Tables/ArithTable.lean:66-75`) **does not exist**; the
module moved to `ZiskFv/AirsClean/ArithTable.lean`. The `arith_table_op_*` axioms it warns about
are **gone** — zero declarations survive anywhere, and the repo has **0 project axioms** (V1 check
16). What actually exists is the *correct* pair: `AirsClean/ArithTableProjections.lean` holds
`mulh_np_xor_not_static`, `mulhsu_np_xor_not_static`, `mulw_sext_zero_not_static`,
`divuw_sext_zero_not_static`, `divw_sext_zero_not_static` — **formal counterexamples proving those
claims are not ROM facts** — alongside true-subset projections. Those are an asset, not a hazard.
The one real residue is a **stale docstring** (`AirsClean/ArithTable.lean:43-83`) still describing
the axioms as live and saying the module "retires zero axioms". That is a doc fix, not soundness
work. #281 should be re-scoped to that docstring or closed as obsolete.

#### #279's stated remediation is stranded

#279 says the fix is "in flight as refactor turn R15 (branch `refactor-15`)". That branch is part
of the **DRIFTING** Aristotle stack (owner ruling 2026-07-22). Confirmed:
`ZiskFv/AirsClean/ArithCompleteConstraints.lean` — the complete generated-constraint mirrors —
exists on `refactor-14/15/16` and **does not exist on `main`**. So the issue's remediation
pointer is dead as written. Either that work is cherry-picked out of the drifting stack onto a
fresh branch, or #279 is re-planned from scratch. **This needs an owner decision and is the single
biggest hidden cost in the remaining soundness work.**

#### Recommended order

1. **#281 first — hours, not days.** Fix the stale docstring (or close as obsolete). Removes a
   false hazard from the board and stops it distorting the audit.
2. **#280 next — bounded and pre-priced.** Extend Main's `Component.transition` with the source-C
   copy equations beside the PC handshake, derive the ControlFlow bridge premises, delete them.
   The issue already enumerates every witness re-discharge site. Note S5 added two more
   (`SdLdSpinWitness`, `SdLdSpinRootSoundness`) — the issue's site list needs that amendment.
   Do this **before** #61: it is the same "extend `Component.transition`, delete premises" move
   #61 will make at scale, on a small target, and it is the cheapest way to re-validate the
   `pcHandshakeTransition` precedent against a second constraint family.
3. **#279 third — the real unknown.** Decide the stranded-remediation question first
   (cherry-pick vs. re-plan), then materialize `inv_sum_all_bs` + the audited generated
   constraint set in the shared provider circuit, swap the ensemble onto the completed component,
   derive the 16 premises. Gate: a concrete **DIV instantiation** on the S5 pattern. If DIV
   cannot be instantiated, the premises were not really derived.
4. **#61 (S6) fourth.** Axis A at scale. Its regression anchor is S5's witness.
5. **#184 last**, as the plan already sequences — it is a reporting task and is only honest once
   1–4 have emptied the "should be derivable, isn't" bucket.

Note this **contradicts the GitHub dependency graph**, which has #61 `blockedBy` #186 and #184.
Those edges look inverted (the audit depends on #61, not the reverse) and need an owner ruling —
recorded here, not silently mutated, per AGENTS.md.

#### Sufficiency verdict

| Issue | Specified well enough to execute? |
| --- | --- |
| #280 | **Yes** — finding, fix shape, and re-discharge sites all concrete. Only amendment needed: add S5's two new witness sites. |
| #281 | **No, but only because it is stale** — wrong path, hazard already gone. Needs re-scope or closure, not planning. |
| #279 | **No.** The finding is excellent and verified; the *remediation* is a dead pointer into a drifting branch. Needs an owner decision plus a real plan before anyone starts. |
| #61 (now S9) | **Was the gap** — five checklist bullets for the largest remaining soundness item. Full plan folded into S9 below 2026-07-27 (no separate plan file); owner reviews before build. |

Also note #61's own body is stale: it quotes the pre-2026-06-25 signature with `rowDecodes :
RowDecode` and a `RowOutsideDefectRegion` taking `sailTrace`/`inputsAgree`. Current is
`programDecodes : ProgramDecode` and a trace-row-local defect predicate
(`trusted-base.md`, 2026-07-23 note). Refresh the body before the stream starts.

### S6 — #281: ArithTable stale-doc disposition (smallest; clears a false hazard)

#281 as written is stale — see "Soundness finish line" above for the audit. The file it names does
not exist, the `arith_table_op_*` axioms it warns about are gone (0 project axioms repo-wide), and
`AirsClean/ArithTableProjections.lean`'s `*_not_static` theorems are *counterexamples*, i.e. an
asset. The only live residue is a docstring.

#### S6 execution checklist

- [x] Rewrite `ZiskFv/AirsClean/ArithTable.lean:43-83`: the two "findings" describe a retired
      state. Say plainly that the `arith_table_op_*` axioms are deleted, that the module's role is
      the proven `StaticTable` mechanism, and that `ArithTableProjections.lean` carries both the
      true ROM-data subsets and the five `*_not_static` refutations. **Landed as PR #292
      (`a60b2bd5`).**
      Audit also found a *second* stale claim the issue did not mention: the note said the module
      "is not on the global theorem's dependency graph", but it is — imported by
      `AirsClean/Arith{Mul,Div}/{Spec,Constraints}.lean`, with `ArithTableProjections` imported
      across `AirsClean/FullEnsemble/Balance/`. Corrected in the same PR.
- [x] Retarget #281's body to the real path and the real (doc-only) residue. **Retitled + audit
      comment posted 2026-07-27; PR #292 carries `Closes #281`.**
- [x] Verified: `lake build ZiskFv.AirsClean.ArithTable` (8035 jobs) + V1 17/17. V2 not run —
      cannot alter any elaborated type or axiom closure.
- [x] Adversarial review corrected two overclaims before landing: zero source Lean trust
      declarations does not erase the documented extraction/protocol/root premises, and the live
      Arith route is the shared ArithMul provider's in-component `Table.fromStatic` lookup rather
      than the channel-balanced `BinaryTableSlice` / `SpecifiedRangesSlice` route.
- [x] Merge PR #292 and confirm #281 closes. Squash commit `a60b2bd5`, 2026-07-27.
      Worktree `.worktrees/issue-281-arithtable-doc` remains for explicit cleanup.

Exit: #281 closed; no reader can mistake the refutations for over-claims.

### S7 — #280: Main source-C copy constraint (the `Component.transition` precedent, second use)

`main.pil:386`'s source-C copy (`b_src_c` copies the previous row's `c0/c1` lanes) has no home:
not in the live per-row circuit, and not on Main's `Component.transition`, which is
PC-handshake-only (`Main/Circuit.lean:932`, `transition := pcHandshakeTransition`). It is carried
instead as caller burden — surfacing as `Inputs_jalr.h_operand_offset`
(`RowDataControl.lean:761-767`), which asserts the committed `b`-lane already equals
`rs1_val + signExtend imm` in both lowerings. In the unaligned lowering that *is* the source-C
chain.

Sequenced **before** S9: it is the same "extend the component, delete the premise" move S9 makes
at scale, on a small target, and it re-validates the `pcHandshakeTransition` precedent against a
second constraint family.

#### S7 execution checklist

**Read-only convergence checkpoint (2026-07-27):** exhaustive search found one transition
definition site plus four concrete proof files: `Main/Circuit.lean`,
`SingleAddWitness.lean`, `AddSpinWitness.lean`, `AddAddiSpinWitness.lean`, and S5's
`SdLdSpinWitness.lean`. `ConcreteRowReductions`, `EnsembleWitnessBuilder`, and the three
`*RootSoundness` modules are constructor/regression consumers, not direct transition-discharge
sites. The extracted constraints also contain first-segment boundary inputs absent from the Clean
transition model, so implementation must state and prove the honest non-segment specialization;
it must not present that specialization as the full extracted boundary equation.

**Implementation gate finding (2026-07-27):** the real unaligned lowering is two Main rows
(`[ADD, AND]`), but the current trace-level API identifies architectural step `i` with physical
Main row `i`; its JALR decode simultaneously requires that row to have Sail PC, be terminal AND,
and have `jmp_offset2 = 4`. The real terminal row instead has PC+1 and `jmp_offset2 = 3`, so no
current index can instantiate the required gate. S7 therefore includes an internal
execution-step/lowered-row grouping plus lowering-indexed JALR decode migration, while preserving
the eight-binder `root_soundness` statement. Source-C will delete `h_operand_offset`; the strictly
smaller Main-source↔Sail-rs1 agreement survives explicitly as genuine cross-world `InputsAgree`
evidence and is not claimed derived.

- [x] Extend Main's `Component.transition` with the source-C copy equations beside the PC
      handshake, cited to `main.pil:386` and its extracted constraint fact. Intrinsic transition,
      never a caller promise.
- [x] Re-discharge at every concrete witness site. #280 enumerates: `SingleAddWitness.lean:190-217`,
      `AddSpinWitness.lean:434,566`, `AddAddiSpinWitness.lean:545,617`,
      `Instantiation/ConcreteRowReductions.lean`, `EnsembleWitnessBuilder.lean:119-125`, and the
      two `*RootSoundness.lean` consumers. **Amend that list with S5's two new sites:
      `SdLdSpinWitness.lean` and `SdLdSpinRootSoundness.lean`.**
- [x] Derive the ControlFlow bridge premises from `transitions_hold` and **delete** them
      (`EquivCore/Bridge/ControlFlow.lean`). Deriving means deleting the field, not moving it.
      `a1050558` removes `Inputs_jalr.h_operand_offset`; the unaligned route now composes the
      physical ADD provider, Main `transitionBetween` source-C copy, and terminal AND row.
      Forced StepStrong, Dispatcher, Soundness, and the concrete accepted witness are green at
      normal limits. The retained `h_rs1_start` is the strictly smaller genuine cross-world
      register/Sail agreement, not a relocated offset premise.
- [x] Gate: a concrete **JALR instantiation** on the S5 pattern, covering the unaligned lowering.
      If JALR still cannot be instantiated, the premise was not really derived — report, do not
      widen. `6919940e` applies the public eight-binder `root_soundness` theorem to a concrete
      two-step ADDI/JALR trace whose unaligned JALR occupies physical `[ADD, AND]` rows followed
      by its successor. `a0204359` registers the gate in the semantic trust witness roster.
      Forced `ConstructionAdd` and `JalrSpinRootSoundness`, full `lake build`, both trust suites,
      and `nix run .#test` pass at the restored 2M `ConstructionAdd` heartbeat limit; `109d9b2b`
      removes the temporary 32M/recursion-limit escalation and `fb907994` updates the degenerate
      root regression for decode-indexed `StepSound`. The fully gated branch is open as PR #293;
      merge and issue closure remain owner-controlled.
- [x] Ledger + cleanup pass on review findings (`720d4bfa`). `transitions_hold` now cites
      `main.pil:386` and documents the extension: only the `(1 - SEGMENT_L1)` within-segment case
      is modeled (segment boundary and a-lane copy deliberately omitted, so the model is implied
      by the PIL and never stronger), it is a REDUCTION not a shift, and `root_soundness`'s
      conclusion is decode-indexed for JALR without a new binder. Removed the declarations the
      new route orphaned (`RowData_jal`/`RowData_jalr` + builders, `jalr_link_bridge_unaligned`);
      **kept `Decode_jalr_of_program`** — S7 updated it for `JalrLoweringRows` and then stopped
      calling it, so it is S7b's starting point, not dead code. Full `lake build` (9074), V1
      17/17, V2 18/18 green.
- [x] Close #280. **MERGED 2026-07-28** — PR #293 squashed to `origin/main` `fac67c2f`; #280
      auto-closed COMPLETED. Landed first of the two deliberately, because it changes the public
      `root_soundness` conclusion shape (decode-indexed `StepSound`) and S8 had to rebase onto that
      rather than the reverse.

Exit: #280 closed; `Inputs_jalr.h_operand_offset` gone or reduced to a genuine cross-world fact.
**MET** — the field is deleted and the surviving `h_rs1_start` is the genuine cross-world register
agreement.
**S7 exits with one named residual, #295 — see S7b.** Do not treat S7 as clean; the JALR premise
reduction is real and gated, but it was paid for partly with decode provenance that S7b must
restore.

### S7b — #295: restore JALR committed-ROM decode provenance (S7 residual)

**This is scope ADDED by S7's review, not work closed.** Recording it here so the finish line stays
honest: S7 genuinely retired `Inputs_jalr.h_operand_offset` (a cross-world sum identity that in the
unaligned case assumed the whole ADD computation) in favour of `h_rs1_start`, but it also replaced
JALR's ROM-backed decode bundle with a passthrough.

Before S7, `rowDecode_of_programDecode`'s JALR arm read
`Decode_jalr_of_program … pd.h_idx pd.h_flag pd.h_a_mask_lo … pd.h_prog`; it now reads
`| jalr _ => exact pd.toDecode`, and `ProgramDecode_jalr` is a single
`toDecode : Decode_jalr` field. JALR is therefore the **only one of 63 families** whose program
decode does not reduce to committed-ROM evidence. Nothing is unsound — every field is still a
proposition about the committed trace and the axiom closure is unchanged — but the audit trail
that the other 62 families carry is gone for this one.

**Cause (durable lesson, same shape as #279's).** The `h_prog` bundle indexes the committed program
at a single line (`(trace.program j).line = mainOfTable … .pc i.val`), i.e. it assumes
architectural index = row index. S7 made JALR the first family whose one instruction may span two
Main rows (unaligned `[OP_ADD, OP_AND]`), which that shape cannot express — so the whole family was
collapsed rather than just the unaligned arm. **Any future multi-row lowering will hit this same
wall**; the fix should generalize the bundle, not special-case JALR.

**Independently actionable.** S7b does *not* depend on S9's Phase-0 stop condition (the raw-word →
lowered-`ZiskRomMessage` join). It uses the existing block-1 `Decode_<op>_of_program` route that
already works for the other 62 families, so it can be scheduled at any point after S7 lands.

**STATE 2026-07-28: MERGED.** PR #299 was squash-merged as `5b1f4fca`; #295 auto-closed
COMPLETED. Built by a
dispatched agent on `.worktrees/issue-295-jalr-decode`, branch `issue-295-jalr-decode`, 2 commits
(`46f74cbc`, `1c93d11c`), pushed, **no PR opened**. Two adversarial verifiers returned SOUND.
The decisive scouting result: the unaligned PC relation is **derivable, not a new premise** —
`mainTransition_to_next_pc` + `mainTable_fixed.segment_l1_succ` + `Airs.Main.pc_handshake_branch`,
consuming only pins the unaligned `JalrLoweringRows` arm already carries. One new lemma was needed
(`romASourceImmColumn_of_romFlags_eq_packFlags`), which must live in `RomDecodeBinding.lean` for
private-lemma visibility.

Blocking / sequencing:
- **UNBLOCKED 2026-07-28**: #297 (`01f5a5ba`) and #298 (`e19f012e`) are merged, so `origin/main` is
  green and carries the build-graph gate. S7b branches from the older `2da97416` and must be rebased
  onto `e19f012e`. `git merge-tree` against the repair stack was **clean**: its second commit
  duplicates #297's `componentComplete` realignment of `JalrSpinWitness` byte-for-byte, so the
  duplication costs nothing to unwind.
- Its reported "V2 18/18" is **not trustworthy as-is**: the branch does not add the
  `JalrSpinRootSoundness` import, so — exactly like #293/#294 — that pass rests on an explicit
  `lake build +<module>` in its worktree. #297 supplies that import, so after the rebase its
  256-line rewrite of `JalrSpinRootSoundness.lean` is gated by default `lake build` for the first
  time. **Re-gate after rebasing; do not carry the pre-rebase result forward.** #298's V1 check
  18/18 also now applies whole-tree, and V2 is 19/19, so the post-rebase numbers differ from the
  branch's recorded ones.
- It touches no gate scripts and adds no modules, so it does not collide with #298's check 18/18
  (unlike S8b/#296, which does).

Residuals the verifiers named, to settle before or at PR:
- the new `.aligned` arm of `ProgramDecode_jalr` has **no instantiating witness** anywhere, so its
  non-vacuity is unproven (the spin witness exercises the unaligned arm);
- `h_offset_aligned` is a net-new caller premise relative to the pre-#293 bundle — smaller than what
  it replaces, but the branch's self-report overstated it as exact parity.

- [x] Re-wire the aligned arm through the retained `Decode_jalr_of_program` (already carries
      `h_offset_aligned` and builds the `Or.inl` lowering). **Done** — `46f74cbc`.
- [x] Add the unaligned sibling: a ROM-lookup constructor over the `OP_ADD` row at `line = pc(i)`
      and the terminal `OP_AND` row at `line = pc(i) + 1`, yielding `Or.inr`. Needs an
      `h_prog`-shaped premise indexed at two committed lines.
- [x] Re-expand `ProgramDecode_jalr` to ROM-backed fields (two-arm bundle, or one bundle
      parameterised by the lowering) and restore the real dispatch; delete the gap docstring
      `720d4bfa` added. **Done** — now a two-constructor inductive (`.aligned` / `.unaligned`).
- [x] Update `JalrSpinRootSoundness.lean`, which currently supplies the passthrough decode. **Done** —
      rewritten (256 lines) to build the unaligned two-arm decode.
- [x] Rebase `issue-295-jalr-decode` onto `e19f012e`. **Done** — the duplicate `JalrSpinWitness`
      commit dropped itself (`patch contents already upstream`); branch is now `95e6c0a1` +
      `973dc02c`.
- [x] Settle the two verifier residuals. **Done** — both were smaller than flagged. The `.aligned`
      arm's missing witness is PRE-EXISTING (checked `a60b2bd5`: no witness instantiated a JALR step
      at all before #280), now recorded in the `ProgramDecode_jalr` docstring; an aligned spin
      witness would close it. The `h_offset_aligned` parity overclaim never reached the code — it
      was only in the agent's self-report — and the PR body states it as net-new-but-smaller.
- [x] **RE-GATED AFTER REBASE.** `lake build` green 9118 jobs; V1 18/18 (688 modules reachable, 0
      unreachable, 0 dangling); V2 19/19 exit 0 with `jalrSpinRootSoundness` / `jalrStepSound` /
      `jalrAcceptedTrace` certified. First time this module is gated by default `lake build`
      rather than an explicit target. No new axioms/`sorry`/
      `native_decide`; JALR spin root-soundness still instantiates.
- [x] Open the PR — **#299**.
- [x] Close #295 on merge — **PR #299 merged as `5b1f4fca`; #295 auto-closed COMPLETED.
      Adversarial review found no blockers; focused Lean build and all eight `nix run .#test`
      stages passed.**

Exit: `ProgramDecode_jalr` carries committed-program evidence for both lowerings; no family is
left on a passthrough decode.

**Adjacent, deliberately NOT folded in:** other families still assume arch-index = row-index in
their step effects, so an instruction *following* an unaligned JALR is not yet instantiable at the
trace level. That stays with S9 unless S7b's work makes it free — if it does, say so explicitly
rather than widening silently.

### S8 — #279: the Arith Div-block model-coverage gap (the real unknown)

The live ensemble validates `ArithMul.componentWithArithTable`, whose circuit mirrors only a
subset of the physical Arith AIR: the Div-block generated constraints (zero-divisor/overflow
boundary `constraint_9-24`, inverse-sum detector `constraint_25`, scope/disjointness
`constraint_26-30`, W-mode lanes `constraint_47-48`) are not validated. `ArithMulRow` does not
model `inv_sum_all_bs` (stage-1 col 38) and the row-view converter fabricates it as `0`
(`Compliance/ConstructionDivu.lean:133`), under which the generated inverse-sum equation is false
on ordinary nonzero DIV/REM rows. Consequently `Inputs_div` (`RowDataArithMem.lean:1093-1140`)
demands a whole `Valid_ArithDiv` model plus 16 row-constraint premises — inside root-theorem
binder 5.

**#279 generalizes to a class** and that framing is the durable part: *the Clean circuit the
ensemble validates can silently cover fewer generated constraints than the Lean mirrors or the
legacy `Valid_<AIR>` models suggest.* Per-family Q2 audits compare constraint lists; they do not
check which circuit the ensemble validates.

**Owner ruling 2026-07-27: CHERRY-PICK.** #279's remediation was written as refactor turn R15 on
branch `refactor-15`, part of the DRIFTING Aristotle stack.
`ZiskFv/AirsClean/ArithCompleteConstraints.lean` (the complete generated-constraint mirrors) exists
on `refactor-14/15/16` and **not on main**. That work is salvaged onto a fresh branch off current
`main` rather than re-derived. Rationale: the mirrors are already written against the cited
generated facts, and re-deriving them would duplicate weeks of transcription for no epistemic gain
— the anti-laundering guarantee comes from each `assertZero` citing its `constraint_N_every_row`
extraction fact, which is a property of the file, not of which branch produced it.

**Cherry-pick discipline** — the stack is stale and was never rebased, so this is a salvage, not a
merge:
- Take the *content*, not the history: identify the minimal file set (start with
  `ArithCompleteConstraints.lean`) and port it onto a branch off current `main`. Do not attempt to
  rebase the refactor stack or cherry-pick whole turns; expect Binary/Arith conflicts with the
  merged S3/S4 landings.
- Every ported `assertZero` must be **re-verified against the current extraction** before use —
  the mirrors were written against a pre-S3/S4 tree. A citation that no longer resolves to a live
  `constraint_N_every_row` fact is a defect to fix, not a line to copy.
- The refactor stack itself stays DRIFTING and untouched. Porting content out of it does not
  reactivate it and does not commit the project to landing it.

#### S8 execution checklist

**Read-only salvage checkpoint (2026-07-27):** all 38 distinct generated facts used by the
candidate mirrors still exist under unchanged names and their polynomials match the current
extraction; none moved or disappeared. All recorded `arith.pil` line numbers are stale, however,
and the candidate file's extraction citations are comments rather than machine-checked Lean
links. Salvage is therefore transcription-small but integration-medium/high: materializing
stage-1 column 38 changes both Arith row records and propagates through providers, conversions,
the ensemble, and Compliance constructors. Implementation must correct the source map and must
not describe comment-only citations as formal linkage.

**Implementation gate finding (2026-07-27):** checking the appended assertions is insufficient if
the live component `Spec` forgets them. S8 must expose a kernel-proved `CompleteSpec` from
`constraints_hold` before deleting any `Inputs_div` field. The current balance layer also lacks a
signed `OP_DIV` provider-selection theorem (only unsigned DIV/REM siblings exist), so the concrete
DIV gate includes that signed balance route; a compile-only component swap is not acceptance.
The deletion audit further found that `h_r_le` comes from the physical ArithDiv→Binary LTU
finished-channel edge at `arith.pil:274`, not local constraints 0–48; the current live ensemble
does not compose that edge and `ConstructionDivu` retains it as `remainder_bound`. S8 therefore
includes composing this real edge and deriving the bound from its balanced provider message.

**Physical-edge implementation checkpoint (2026-07-27):** the completed Arith provider now exposes
the real conditional remainder-bound consumer, full-ensemble balance can resolve non-Main
consumers to spec-carrying provider rows, all four signed selector opcodes (`6/80/81/8`) have exact
static-provider chain constructors, and the irrelevant Arith/BinaryExtension alternatives are
being eliminated from the provider classification. The divisor-zero row has zero multiplicity, so
the final bound must be conditional on a nonzero divisor; retaining the old unconditional
`Inputs_div.h_r_le` would be uninstantiable, not stronger. The remaining proof kernel is an honest
8-byte weak signed-comparison lift: strict comparison is invalid because the documented
`LT_ABS_NP` equality false-positive is real, while the theorem boundary deliberately retains that
case in `Compliance/Defects.lean`.
The three required packed lifts (`LT_ABS_NP`, `LT_ABS_PN`, and `GT`) are implemented, but a forced
downstream rebuild exposed stale-olean masking in their prerequisite special-chain constructors:
the earlier ordinary focused command had not re-elaborated the changed source. Those constructor
errors are repaired by `82d690e5`; the forced
`+ZiskFv.EquivCore.Bridge.Binary` gate is warning-clean green (8213/8213). The packed lifts and
four-sign-case lane transport must continue to use forced targets.
The independent balance specialization is forced-green (`ece9239`, 8295/8295): an active
remainder selector request at op `6/80/81/8` can only be served by the spec-carrying static Binary
provider, with the other live provider families excluded from their checked opcode sets.
Anti-vacuity review also rejected the provisional signed witness shape that demanded all four
op-pinned chains on one Binary row. A physical row has exactly one selected opcode, so the witness
must carry a sign-indexed four-way selected-chain alternative; proving consequences from the
impossible all-chains bundle would not satisfy the concrete-instantiation gate.
That correction is now committed as `0d2e01fc`: the witness contains exactly one chain selected by
`(nr, nb)`, and the strict `pos0 = 0` NP/PN packed lifts share an eight-byte kernel. Forced
`+BinaryPackedCorrect +Bridge.Arith` is green (8236/8236). The conditional weak signed bound and
concrete DIV construction remain pending; no `Inputs_div` field is counted as derived yet.
The next anti-vacuity audit found that the special-chain predicate itself erases the row opcode.
Commit `9582393a` therefore retains the exact row-native `b_op` pin in each selected arm; combined
with the bus selector this derives `mode32 = 0` before interpreting the chain. Forced
`+Bridge.Arith` remains green (8236/8236). Signed provider-row selection and its `FullSpec` /
primary-message projections are committed as `c5302c7b`; deletion still waits for the completed
Div-block and weak-bound consequences to reach `Inputs_div`.
The static provider selector is committed as `82996228` and forced-green (8085/8085). A GT-arm
audit then found that same-sign unsigned comparison needs the physical high-byte sign equality;
this is derived, not assumed: `426afe9a` proves opcode-186 `nb`/`nr` polarity for
`range_ab + 17` / `range_cd + 17` from live Arith-table membership, and the indexed range lookup
supplies the corresponding divisor/remainder MSB facts. Forced `+ArithTableProjections` is green
(8091/8091). The NP arm is now split into declaration-safe raw/normalization pieces and forced
`+Bridge.Arith` green (8236/8236), preserving the documented equality false-positive; PN, GT,
and the combined weak bound are now committed as `785d0dd8`. The exported
`arith_div_remainder_bound_signed` consumes the selected physical witness, chunk ranges,
`ArithTableSpec`, `IndexedRangeSpec`, and op=186; forced `+Bridge.Arith` is green
(8244/8244). It preserves the NP/PN equality false-positive and derives the GT high-byte signs
from indexed range lookups rather than a premise.

**Concrete-gate construction checkpoint:** `RegisterBoundary.bootMessage` fixes every initial
register to zero, so the initially proposed two-step DIV/JAL trace is not constructible. The
smallest honest gate has four executed steps:
`ADDI x1,x0,6`; `ADDI x2,x0,2`; `DIV x3,x1,x2`; self-looping `JAL`, plus the duplicate
physical JAL successor row used by the established witnesses. Its completed Arith row has
remainder zero and selects the static LTU provider, so the Main↔Arith and Arith↔Binary pairs
cancel and the row is outside the preserved forge boundary (`0 < 2`); the two ADDI rows also
carry their real BinaryAdd providers. The physical witness must construct the completed row
from `arithDivRowOf 6 2` plus the real completed-only columns; it must not reuse the MUL-only
`arithMulRowOf`.

**Deletion audit:** the exact 16 S8 fields are `v`, `r_a`, `h_match_primary`,
`h_row_constraints`, `h_boundary`, `arith_table`, `arith_chunk_ranges`,
`arith_carry_ranges`, `h_na_bool`, `h_nb_bool`, `h_nr_bool`, `h_np_xor`, `h_nr_pin`,
`h_r_le`, `h_r_sign`, and `h_not_forge`. The genuine cross-world fields
`h_rs1_value`, `h_rs2_value`, and `h_pc_bridge` remain, retargeted to the internally selected
`divArow`/row 0. `h_not_forge` disappears because the dispatcher already supplies the exact
row-local defect exclusion; it is not inferred from the weak remainder bound.

The last local signed semantic field, `h_r_sign`, is now derived generically by
`arith_div_remainder_sign` (`6bce2b72`) from real chunk/table/indexed evidence, the
table-derived remainder-sign pin, and retained `h_rs1_value`. Forced `+Bridge.Arith` is green
(8244/8244), and axiom verification reports only Lean's standard logical axioms.

**Canonical-interface correction:** exact `np = na XOR nb` is false for valid ordinary DIV
rows when the quotient/product is zero (for example `1 / -2 = 0` remainder `1`); the physical
ROM intentionally permits the product sign flag to stay zero. S8 therefore generalizes the
internal signed-DIV arithmetic lemma to the faithful zero-product disjunction, then derives
that exception and `nr=np ∨ remainder=0` jointly from real table/indexed/carry/bound evidence.
Keeping the old exact XOR as an `Inputs_div` field would be uninstantiable laundering, not a
stronger completion.

The dynamic exception proof legitimately needs the dispatcher-supplied exact
`¬ DivRemForge`: the physical comparison proves only weak `|D| ≤ |B|`, and the excluded
equality case is precisely the counterexample to forcing the zero quotient/sign exceptions.
The direct construction therefore threads the existing row-local defect exclusion (not an
Inputs field), upgrades to strict bound, and reasons from the raw signed carry-chain identity
before the old exact-XOR normalization. This statement predates the owner's later authorization
to add the independently reproduced quotient-sign defect; the final implementation changes
`Compliance/Defects.lean` only for that explicit boundary extension.
That non-circular substrate is committed as `80f225fd`: `div_signed_chain_witnesses_raw`
exports the real signed coefficient before XOR rewriting, while the old theorem remains an
API-compatible wrapper. A later forced downstream rebuild invalidated the initially reported
green: the commit also accidentally removed the pre-existing MUL theorem's local
`h_np_bool` derivation. The exact parent proof is restored pending a separate forced-green
repair commit; stale-olean output is not counted as evidence.

**Formally verified S8 stop condition (2026-07-27, `3e624f98`):** the completed live component
admits an
ordinary op-186 row with flags `(na,nb,np,nr)=(0,1,0,0)`, `A=1`, signed divisor `B=-1`,
`C=1`, and `D=0`. The individual carry equations use
`cy0..cy6=(-1,-1,-1,-1,0,0,0)` and satisfy the signed ranges; strict remainder bound and
`¬DivRemForge` both hold, but the encoded quotient is +1 rather than RISC-V -1.
`Regression/SignedDivOrdinaryCounterexample.lean` proves the actual
`componentComplete.operations.ConstraintsHold`, exact ROM row, all eight indexed lookups,
all chunk/carry ranges, primary operation-bus payload, and the active static-Binary remainder
provider before deriving the completed Div block and the physical/Sail mismatch. Normal and
forced targets are green (8635 jobs each); five key endpoints verify with only `propext`,
`Classical.choice`, and `Quot.sound`, and the source/trust scans are clean.

This is therefore a genuine untracked AIR soundness defect, not a thin-model artifact. The exact
XOR premise had masked it. The 16-field deletion and required concrete DIV instantiation are
impossible without either laundering the missing fact or changing the defect/theorem boundary;
both are forbidden by this stream. Positive ConstructionDiv/DivSpin drafts remain uncommitted,
`Compliance/Defects.lean` and `trust/defects.md` remain byte-unchanged, and the two acceptance
checkboxes below intentionally remain open as stop-and-report evidence rather than being
relabelled as completed. The checked evidence is preserved in draft PR #294 and reported on
#279 in issue comment `5096667020`; neither is presented as a completed remediation, and the
issue remains open pending an owner-approved boundary or physical-AIR correction.

**Owner ruling 2026-07-27 — resume under the existing defect-qualified theorem.** Upstream
reproduction PR codygunton/zisk#12 verifies the `DIV(1,-1)=+1` witness end-to-end against the
stock proving key and identifies it as the DIV analogue of the already-recorded signed-MUL
product-sign forge: the DIV path fails to pin the quotient sign `na = np XOR nb` for a nonzero
quotient. It is distinct from codygunton/zisk#5's remainder-magnitude defect. S8 is therefore
authorized to extend `hAvoidKnownBugs` / `RowOutsideDefectRegion` with this precise signed-DIV
quotient-sign shape and continue. This is an explicit theorem-boundary change, not a derivation:
the defect ledger, Lean predicate, row-local matcher, and anti-vacuity witness must move together.
The separate `DivRemForge` equality exclusion remains load-bearing. After threading the new
exclusion, derive and delete the remaining `Inputs_div` fields and complete the concrete DIV gate;
do not retain `h_np_xor` as a caller field.

**Resume checkpoint (2026-07-27):** the precise theorem-boundary extension is implemented locally
as a separate `arithDivQuotientSignSoundness` defect ID and
`SignedDivQuotientSignForge := div_overflow = 0 ∧ quotientMagnitude ≠ 0 ∧
np ≠ na XOR nb`; the `.div`
trace-local matcher supplies it alongside the independent `DivRemForge` negation. The defect
ledger, generated defect-count baseline, envelope bridge, and anti-vacuity lemma have moved with
the Lean predicate. The faithful arithmetic kernel is focused-green:
`abs_euclidean_to_signed_euclidean_div_rem_zero_quotient_exception` plus
`h_rd_val_mdrs_div_chunked` preserve the exact-XOR route and separately prove the two physical
table exceptions from the raw carry chain after the new exclusion forces quotient magnitude zero.
Focused builds are green through `EquivCore.Div` and `Compliance.Wrappers.Div`. The old
`Inputs_div.h_np_xor` has not yet been deleted; the next integration step is deriving the table
classification at the balance-selected `divArow` and threading the row-local exclusion through
the internal envelope.

**Live-provider coverage matrix (2026-07-27):** no third local-model thinning was found. Main
source-C (#280) and the Arith Div block (#279) remain the two gaps. Mem is full only because its
component-owned `generatedTransition` supplies the segment residual and permutation groups omitted
from the row circuit; MemAlign/MemAlignByte/MemAlignReadByte cover their local algebraic and
transition groups with finished channels abstracting accumulators. RegisterBoundary has no
standalone physical table AIR and remains an explicit protocol/boot grounding item for #184, not
an S8-class mismatch. Static providers use exact `Table.fromStatic`/lookup-aware membership; no
omitted semantic membership group was found.

**Remainder-sign audit correction (2026-07-28):** formalizing the initially proposed
`-7 = (-3) * 3 + 2` row showed it is rejected by the physical carry chain: the AIR's magnitude
identity reduces to `3 * 3 + 2 = 7`, leaving residual `4`. The genuine unconstrained-sign row is
`-7 = (-2) * 3 + 1`: it leaves opcode-186 DIV's observable quotient correct but makes opcode-187
REM return `+1` instead of `-1`. This distinct REM defect is disclosed as
`codygunton/zisk#13`; it does not justify widening DIV's defect boundary. Consequently S8 must
remove `h_nr_pin` from the DIV semantic route rather than derive it or add a replacement
assumption—the quotient proof does not semantically need the internal remainder sign.

**Remainder-sign-independent kernel checkpoint (2026-07-28, `3352704a`):**
`h_rd_val_mdrs_div_quotient_chunked` now derives the signed DIV result from the raw carry
identity, physical ranges, quotient sign classification, operand bridges, nonzero divisor, and
strict remainder magnitude only. It constructs a canonical dividend-signed remainder and applies
signed Euclidean uniqueness; neither `h_nr_pin` nor `h_r_sign` occurs in its statement or proof.
The focused direct compile and Lake target are green. Downstream selected-row construction and the
concrete DIV/root gate remain open.

**S8 implementation closeout (2026-07-28):** all exact 16 audited `Inputs_div` fields are
physically deleted. The retained operand/PC bridges target the balance-selected physical
`divArow`; completed Arith constraints, chunk/carry/indexed ranges, sign classification, and the
conditional weak remainder bound are derived internally. The dispatcher supplies both independent
row-local exclusions through the existing `hAvoidKnownBugs` boundary. The acceptance gate is a
real four-instruction trace (`ADDI x1,6`; `ADDI x2,2`; `DIV x3,x1,x2`; self-looping `JAL`)
whose physical Arith and Binary provider rows, operation-bus balance, register-memory telescopes,
all channel balances, and all eight `root_soundness` binders are constructed in
`DivSpinWitness` / `DivSpinRootSoundness`. An independent anti-laundering audit passed. Full
`lake build` (9076 jobs), V1 (17/17), V2 semantic (18/18, including the new DIV root witness),
and `nix run .#test` all pass. Implementation is ready for review in PR #294; issue closure remains pending
owner-approved merge.

- [x] Salvage `ArithCompleteConstraints.lean` (and whatever minimal companions it needs) from
      `refactor-15` onto a fresh branch off current `origin/main`; re-verify every constraint
      citation against the current extraction; record which ones moved or no longer resolve.
- [x] Materialize `inv_sum_all_bs` and the full audited generated local-constraint set in the
      shared provider row/circuit. Constraint list frozen to the cited generated mirrors; each
      `assertZero` cited to its `constraint_N_every_row` extraction fact + `arith.pil` line.
- [x] Swap the live ensemble onto the completed component with real witness values;
      constructibility prechecked per concrete row **before** any derivation is attempted.
- [x] Derive the 16 `Inputs_div` premises and **delete** them. The owner-authorized, separately
      reproduced quotient-sign defect extends `Compliance/Defects.lean` and the trust ledger
      together; no deleted field was relocated or replaced.
- [x] Gate: a concrete **DIV instantiation** on the S5 pattern. If DIV cannot be instantiated, the
      premises were not derived — that is a stop-and-report, not a partial win.
- [x] Run the class check the issue asks for: a live-provider coverage matrix across
      Main/Mem/MemAlign/RegisterBoundary and the static-table families, so any remaining instance
      of the class is named rather than discovered later.
- [x] Close #279 after PR #294 receives explicit owner merge approval and lands. **MERGED
      2026-07-28** — owner approved both PRs in-thread; squashed to `origin/main` `2da97416`;
      #279 auto-closed COMPLETED. Rebased onto `fac67c2f` first: 41 commits, one real conflict in
      `StepStrongControlStore.lean`, resolved in S7's favour — S7 **deleted**
      `stepStrong_jal`/`stepStrong_jalr` while S8 had only added an extra `(fun h => h)` defect
      lambda to those same two theorems (diffed both sides; that was the sole difference), so
      nothing of S8's was lost and no references survive.
      **Owner ruled: do not hold the merge on gates.** The post-rebase full `lake build` + V1/V2
      were therefore still running at merge time. Both branches were independently green
      pre-rebase; the *merged* state is unverified until that run reports. If it fails,
      `origin/main` is red and repairing it is the immediate next action — see the S5 precedent at
      `d4780eee`, where exactly this gap let two elaboration-marginal proofs land broken.

Implementation exit met: DIV is concretely instantiable and the coverage-matrix result is recorded
for #184.

### S11 — #303 / #304: round-trip verification (systematic coverage)

Added 2026-07-28 after the weld fan-out. Welding ties one mirror clause to one generated constraint
and is kernel-checked, but **a missing weld fails nothing** — so welding cannot find a constraint
nobody modelled. Every mirror gap found on 2026-07-28 (Main's missing a-side C-copy at
`main.pil:385`, MemAlign's ninth conjunct with no generated counterpart, MemAlign `constraint_16`
treating a fixed column as a witness, `RomBoolSpec` having no consumers) surfaced because a person
happened to work that AIR. None was caught by a gate.

**The structure.** With `f : pilout → Lean` the extractor, build `g : Lean → Expression` and check
`g(f(t)) ≡ t` in the pilout's own algebra. A dropped constraint shows up as a coverage failure, a
distorted one as a non-equivalence, and coverage is derived from the data rather than from a
declaration list that can go stale. Applied in the other direction (mirror → generated) the same
machinery reports gap / strengthening / lane-reclassification per AIR.

**`≡` is polynomial normal form, not a rewrite list.** Both sides are polynomials over column
atoms, so canonicalize to sorted monomials over Goldilocks and compare exactly — total, and stronger
than an enumerated set of allowed rewrites. Random evaluation is a fast screen for candidate
mismatches, not the decider; it matters only if Arith's carry chains make expansion costly.

**Two conditions.** (1) `g` must not reuse `f`'s code — a `g` derived from `f` lets compensating
errors round-trip clean, the same failure as the `romRowOf` cross-check where five identical slots
made the equality hold by `rfl`. (2) `f` must be injective on the constraint set, or coverage must
be counted on the image, or two constraints collapsing to one definition hides a drop.

**Scope.** Polynomial identities only. Lookups, permutations, fixed columns and public inputs are
separate proto messages and are NOT covered; extending to them is a separate decision. Closes the
extractor step only — not PIL itself, and not PIL matching the Rust prover.

- [x] #303 P0: parse pilout, count per AIR, diff against the 355 emitted `constraint_N`.
- [x] #303 P1: `g` — emitted Lean → proto `Expression` AST.
- [x] #303 P2: canonicalizer + comparator; report matched / mismatched / pilout-only / lean-only.
- [x] #303 P3: gate after extraction in `nix run .#populate` and CI.
- [x] #304: same machinery on the mirror side; absorbs the per-AIR column-map gate, which must carry
      lane KIND from the extractor header.

**#304 done — PR #319, stacked on #312, branch `s11-mirror-roundtrip`, worktree
`.worktrees/s11-mirror-roundtrip`.** Result: `139/176` matched, **35 gap, 2 strengthening, 3 unbacked,
2 reclassification, 1 unreachable mirror**, 0 unparsed. The tool reports; nothing under `ZiskFv/` or
`trust/` was touched. `acceptance.py` is the evidence it works: the 4 hand findings rediscovered
without being told where to look, 8 mutations of a copy of the mirrors each classified as predicted,
3 neutral controls unmoved, and 1 blind spot measured rather than claimed (deleting a clause a second
mirror also restates keeps the match — pairing is set-to-set with no per-mirror coverage count).

**OWNER DECISION PENDING: the gate fails at HEAD, so merging reds `nix run .#test`.** Either (a) merge
as written for maximum pressure, or (b) add a citation-bearing baseline that can only shrink, in the
`check-shrinkage.sh` / `check-defect-count.sh` idiom this repo already uses — which the issue's own
text authorises ("either fixed or explicitly declared with a citation"). (b) was deliberately not
built by an agent.

The 35 gaps are not one thing:

- **15 are Mem's and are modelled out-of-root.** `segmentResidualEveryRow`
  (`ZiskFv/Airs/Mem.lean:296`) states exactly those 15, with `:334-339` destructuring a 24-conjunct
  `segment_every_row` into them. The declared mirror root is `ZiskFv/AirsClean` per the issue's own
  wording, so it does not see them. Widen the root or declare the split.
- **9 Main.** #3/#9 are the flagship a-side C-copy (`main.pil:385`); `grep a_src_c ZiskFv/` returns
  zero files, so it is unmodelled tree-wide. #0, #19, #20, #21, #38 are a **second unmodelled cluster
  the hand fan-out never named** — the segment boundary (`main.pil:86,423,426,508`).
- **7 MemAlignWriteByte** — no mirror at all, no `AirsClean/MemAlignWriteByte/` directory. All three
  byte-family AIRs instantiate one PIL template but over different stage widths, so MemAlignByte's
  clauses are different polynomials and do not cover it. Plausibly a deliberate loads-only scope;
  nothing declares it.
- **4 MemAlignByte.**

So constraints nothing models anywhere: **20**, not 35.

**Two follow-up PRs landed on top of #319, both stacked on it:**

- **PR #321 (`s11-mirror-toolscope`)** — closes the 19 tool-artefact gaps honestly. The 15 Mem now
  pair against `segmentResidualEveryRow` by exact canonical equality (`OUT_OF_ROOT`, empty symmetric
  difference, through the same `lanes.LaneMap` — not a declared exclusion); the 4 MemAlignByte are
  `BOOL_TYPED`, recognised mechanically (canonical `a*(1-a)` + a checked `Bool` decl or `.val<2`
  bound), which **discriminates** — MemAlignWriteByte's identical selectors have no bound and stay
  gaps. Result `158/176 covered; 16 gap` (was 35). Diff confined to `tools/mirror-roundtrip/`;
  `acceptance.py` 18/18, real tree byte-identical; pilout gate still 355/355. Verified independently.
- **PR #322 (`s11-main-copyc-investigate`)** — docs-only findings doc on Main #4/#10. Verdict:
  real, soundness-safe, **untracked cross-segment limitation** (corrected after external review —
  see below). Proved `mirror = (1-segment_l1) × generated` *modulo the boolean relation `L² = L`*
  (`SEGMENT_L1` boolean, `main.pil:19`; raw diff `L·B·(x-s)`); `b_src_c` byte-identical to the mirror
  expansion (`main.pil:350/355`); the mirror enters as a *hypothesis* and its only soundness consumer
  (`source_c_copy_lanes_of_between`, `StepStrongControlStore.lean:383`) requires `segment_l1 = 0`,
  exactly where the two forms agree — so the dropped boundary half is never read. The boundary
  constraint is `b_src_c·(b − segment_previous_c) = 0` (a public air-value with no
  `Component.transition` accessor), so the mirror genuinely cannot state it. Distinct from the
  #0/#19/#20/#21/#38 cluster (modelled nowhere): #4/#10 are fully modelled in-scope. **Recommends**
  teaching the tool to read the `(1-SEGMENT_L1)` cofactor as coverage-plus-boundary-delegation — a
  reclassification, left for owner sign-off; not done in either PR.
  - **Review correction (commit `a21d390a`):** an external review caught three doc errors, all fixed;
    the central conclusion held. The load-bearing one: the boundary term is **NOT** already-tracked
    #103/#76 scope — **#103 and #76 are both CLOSED and memory-specific** (#103 cross-segment Mem
    seam, #76 load memory floor), and neither tracks Main's `segment_previous_c` source-C constraint.
    So this is an **untracked** cross-segment limitation — as is the #0/#19/#20/#21/#38 cluster, which
    is only comment-referenced (`RegisterBoundary.lean:30`), not tracked by any open issue.
    **NEW OWNER ACTION:** make a real tracking decision (new/reopened cross-segment issue or an
    explicit known-limitation record) for #4/#10's boundary term and the #0/#19/#20/#21/#38 cluster
    together — do not attribute either to the closed #103/#76.

Remaining genuine gaps after #321: **16** = Main 9 (#3/#9 unmirrored a-side; #4/#10 the weakened
b-side, now characterised by #322; #0/#19/#20/#21/#38 the untracked segment boundary) +
MemAlignWriteByte 7.

Also worth acting on independently of the gate decision: the two existing `Expr`→field maps
(`MemAlign/Bridge.lean:31` `h998ExprToField`, `Binary/Wiring.lean:33` `c10LookupExprToClean`) both end
in `| _ => 0`, each gated by a single `rfl` over one tuple, so a wrong or missing index becomes a
silent zero. `Mem/RangeWiring.lean:29` refuses instead (`| _ => none`) and is the pattern to copy.

**Coordination point: #304 overlaps PR #310.** #310 ("make the weld column-map gate
AIR-parameterised", stacked on #300) and #304's lane map are two attempts at the same gate. #304's
issue text says it absorbs the column-map gate, and #304's version additionally carries lane KIND
(stage-1 witness / stage-2 / fixed / exposed), which is what makes the MemAlign `constraint_16`
fixed-as-witness class mechanical. Decide which survives before both land; do not merge them
independently and leave two column-map gates in the tree.

**#303 done — PR #312, branch `s11-roundtrip`, worktree `.worktrees/s11-roundtrip`.** Result:
`355/355` matched, 0 dropped, 0 distorted, 0 invented, 0 `skipped:` stubs. Tool is
`tools/pilout-roundtrip/` (Python 3 stdlib only, own protobuf decoder, own Lean parser, ~1.5 s), gated
at the tail of `nix run .#populate` and as step 3/9 of `nix run .#test`. A 33-case mutation selftest
is the evidence it can fail: 28 defect classes caught, 5 neutral controls green.

Three things the work changed about the plan's own assumptions:

- **The per-AIR files are not what the proofs read.** Nothing under `ZiskFv/` imports
  `Extraction.<AIR>`; the real dependencies are `Extraction.LookupWiring` (×3) and
  `Extraction.MemAlignRom`. The extractor emits every *mixed* constraint a second time into
  `LookupWiring.lean` over an `Expr` inductive — 124 + 79 = 203, exactly the 203 ExtF-collapsed defs
  — and that is the rendering `ZiskFv/AirsClean/*` consumes. Checking only the per-AIR files would
  have validated files nobody reads, so the gate now decides both (`P3 203/203`). The open weld PRs
  are what make the per-AIR files load-bearing (`ArithMirrorWeld.lean:1: import Extraction.Arith`).
- **`Circuit.exposed` conflates `AirValue k` with `AirGroupValue k`.** In `BinaryAdd.lean`,
  `exposed (index := 0)` is `BinaryAdd.padding_size` in `constraint_7` and `Zisk.gsum_result` in
  `constraint_8`. 54 constraints across 8 AIRs, always index 0; MemAlign and Arith are clean. No
  single constraint mixes them, so nothing emitted is wrong today, and `LookupWiring` decides all 54
  unambiguously — but it is an overstrong-assumption direction and worth closing in the emitter.
- **Every constraint in the pilout is `EveryRow`** — all 4095 across all 35 AIRs. `first_row`,
  `last_row` and `every_frame` are unexercised, so for those kinds the row restriction lives only in
  the emitted definition name.

Exit: a generated constraint that no mirror models, or a mirror clause no constraint backs, is a
build failure rather than something the next person to touch that AIR happens to notice.
#303's half of that exit is met for the extractor step; #304 carries the mirror half.

### S9 — #61: decode-driven trace-level export (was S6; the largest remaining item)

Replace caller-supplied opcode classification/placement with derivation from the committed raw
program via the proven in-build decoder (#162/#164) and the ROM decode binding (#159/#170).
Sail-side grounding of the raw program (#172) stays out (beyond-mvp).

**Where the burden sits.** `ziskStep` (`Claim_<op>`): which op the row decoded to, plus decoded
operand/destination indices and the committed bus row — **derive**. `programDecodes`
(`Decode_<op>`): Main AIR op selector, `is_external_op`, `m32`, `store_pc`, exec-row length,
multiplicities — already `sailTrace`-free, the principal dischargeable bucket — **derive**.
`inputsAgree` (`Inputs_<op>`): register/PC/memory read agreement is the genuine irreducible
premise and stays; placement facts (`h_rd_idx`, store address) are targets. `bootSeed` /
`hAvoidKnownBugs`: out of scope.

**Scope fence.** This stream does **not** touch `Inputs_div`'s `Valid_ArithDiv` bundle (S8) or
`Inputs_jalr.h_operand_offset` (S7). Those facts are unavailable because the *ensemble* is thin,
not because the decode route is missing; reaching for them here would be laundering. If a sweep
family turns out to be blocked on one, stop and report — do not widen.

**Assets already landed (do not rebuild):** #162/#164 proven kernel-sound decoder
(`zisk_decoder_accepts_supported_shape`, `real_decoder_accepts_in_shape`); #159/#170 ROM decode
binding; #111/#160 all 63 ops' static decode pins discharged in-build, gated by
`trust-gate check-extraction-closure`; #100/#163 `Air.Flat.Component.transition`; S5's seven-arm
instantiation as regression anchor. The missing link is the **join**: nothing currently carries a
raw 32-bit word from the committed program through the decoder to a constructed
`Claim_<op>`/`Decode_<op>`.

#### S9 execution checklist

**Phase-0 survey result (2026-07-27): STOP CONDITION (1).** `AcceptedZiskTrace.program` is a
lowered 11-slot `ZiskRomMessage`, not a raw 32-bit instruction, while
`real_decoder_accepts_in_shape` classifies a separately supplied raw word.
`RomDecodeBinding.lean` explicitly records that it does not yet tie the trace program entry to a
raw word's lowering. Treating the lowered tuple as the raw word would be laundering.

**Phase-0 DESIGN COMPLETE (2026-07-28) — the stop condition is cheaper than it looked.** Full
document: `docs/ai/research/NOTE_61_RAWWORD_JOIN_DESIGN.md` (read it before starting; every claim
below is cited there against primary sources).

- **Pivotal finding:** ZisK's raw-word → `ZiskInst` lowering is **already Aeneas-extracted and
  already in the Lake build graph** — `ProductionM2.lean:3642-3672`, calling the *production*
  `lower_rv64im_single_row_input`, the same entry point the ELF transpiler uses. The join is
  composition of existing pieces, not new extraction.
- **A ~4.7k-line 63-op join already exists** at `a16bd97c` and was never merged. It is kernel-sound
  but carries **three confirmed serialization defects**: `SRC_IND` written as literal `3` when it is
  `5` (`3` is `SRC_STEP`); unsigned coercion of `a/b_offset_imm0` where `rom.rs` reinterprets as
  `i64` and negates; and ungated `a_imm1`/`b_imm1`. The first is **already falsified by a witness in
  the semantic gate**: `SdLdSpinWitness.lean:105-119` sets `b_src_ind := true`, which the June asset
  computes as `decide (5 = 3) = false`.
- **Route ranking: (c) ≫ (a) > (d); (b) is eliminated on a proved fact.** (b) — recover the word by
  inverting the lowering — is dead because the lowering is provably non-injective (FENCE routes to
  `nop`, discarding operands). (c) attaches the ROM↔raw agreement certificate to a NEW additive
  endpoint rather than to `AcceptedZiskTrace`; (a) would attach it to every existing witness and to
  #74, creating direct pressure to weaken the field on hand-built witnesses — the failure mode to
  avoid. (d) — accept it as a named trust residual — is where we already are, so it is not a result.
- **Spike order (hard gates):** **S1** land `Extraction/Totality.lean` alone (discharges a side
  condition #111 and block-2 already assume; independently valuable even if the rest dies);
  **S2** re-transcribe `romRowOf` line-by-line from `rom.rs:204-260` as a SECOND independent
  definition and prove the two equal, so a transcription slip fails a proof instead of passing
  silently; **S3** inhabitation on `SdLdSpinWitness` plus a negative-offset load.
- **Kill criterion, stated in advance:** S3 failing after S2 is correct — i.e. an honest,
  constraint-satisfying committed ROM row that is provably not the lowering of any 32-bit word.
  Then `ProgramBinding` is not a property of honest witnesses, (c) collapses to (d), and the right
  output is a blocker naming the offending slot. NOT kill criteria: heartbeat pressure, or
  `romMessageOfRaw` being `noncomputable`.
- **Carry-over hazard:** PR #293 made `root_soundness`'s conclusion decode-indexed, so the June
  asset's "same conclusion, thinner premises" framing no longer typechecks unchanged.
- **Bookkeeping discrepancy to resolve (no progress claimed):** #159 is CLOSED/COMPLETED and #172's
  body asserts `root_soundness_rawProgram` landed, but that identifier does not exist on `main`, and
  PR #170's own body says it "no longer closes #159".

The exhaustive family survey grouped fields as follows:The exhaustive family survey grouped fields as follows:

| Families | `Claim_<op>` | `Decode_<op>` | Category (c) / layering finding |
| --- | --- | --- | --- |
| register/immediate ALU, shifts, LUI/AUIPC, MULW, branches, JAL, FENCE | raw fields (A), except W-shift runtime input bundles | Main/ROM pins (B), with FENCE subset facts and JALR parity partly A | W-shift `PureSpec` inputs bundle decoded and runtime data |
| stores and loads | runtime input bundle (B) | Main/ROM pins (B) | memory claims bundle raw indices/immediate with runtime values |
| signed Mul/Div/Rem | raw register fields (A) | Main/ROM pins and bounds (B) | `ExternalArithMemoryWitness` (C); S8-fenced Inputs bundle untouched |
| unsigned M-extension | raw register fields (A) | Main/ROM pins and bounds (B) | remaining arithmetic Inputs facts are outside this decode survey |
| signed loads | runtime input bundle (B) | Main/ROM pins (B) | `Valid_BinaryExtension`, static lookup, environment, and Main↔Binary match (C): another model-coverage surface |
| JALR | raw fields including aligned offset choice (A) | parity A; remaining Main/ROM/control pins B | **Superseded 2026-07-28 by S7/#293**: `h_operand_offset` is gone, but `ProgramDecode_jalr` is now a passthrough and the decode is stated at the lowering row, not at `i`. **S7b/#295 owns restoring it** — do not re-survey or re-derive JALR decode here; inherit S7b's result. |

No category-(c) fact may be moved into a differently named decode premise. The raw/lowered join,
signed-load provider surface, signed-Arith witness, and bundled-runtime layering must be resolved or
explicitly ruled before code moves.

- [x] **Phase 0 — raw-word join.** Execute the revised P0-1…P0-12 checklist in
      `docs/ai/research/NOTE_61_RAWWORD_JOIN_DESIGN.md` §7 on route (c): an additive
      `ProgramBinding` endpoint through the already-extracted production lowerer. Do not modify
      `AcceptedZiskTrace` or `root_soundness`.
      - [x] **P0-1 lowerer totality/static pins.** Landed locally as `c4482255` +
        `a748e5f0`; focused
        `lake build +ZiskFv.Compliance.AeneasBridgeTrust.Extraction.Totality` passes.
        This proves each opcode builder succeeds under its honest dispatcher-routing hypotheses
        and removes the success premise from the static-pin endpoints. It does not yet prove
        unconditional `extract_transpile_rv64im_raw` totality: the ADD/OR/ADDI/ADDIW alternate
        copyb/hint/precompiled routes remain separate obligations.
      - [x] **P0-2…P0-4 fidelity + layout.** Landed locally as `14a7c7e`. Correct the recovered
        serialization against
        `rom.rs`, prove the immediate-flag side lemmas, and index binding by
        `Fin trace.programLength`. The immediate-source gating is encoded directly in both
        independently named serializer definitions and their equality is kernel-checked by
        `romRowOf_eq_serializeExtract`; the binding carries an explicit strictly increasing
        address layout. Direct
        `lake env lean ZiskFv/Compliance/TraceLevelExport/RawProgramBinding.lean` passes.
      - [x] **P0-5 non-vacuity hard gate.** The existing hand-built `sdLdProgram` is not itself
        a production-lowered ROM: slots 0 and 3 use OP_ADD for rs1=x0 where production emits
        CopyB, and slot 6's hand-written JAL flags/store_pc are not producible. Build an
        independently hand-written honest lowering witness (including SD, LD, and
        `LD x3,-8(x1)`) and prove its binding; do not define its program through
        `romMessageOfRaw`.
        A first accepted full-row inhabitant landed as `f714d9b` for the independently written
        single-ADD witness; its kernel closure is standard-only. This does not check the hard gate
        until the required SD/LD and negative-offset accepted witness also lands.
        Completed in `a3a4e710`: an independently hand-written accepted nonempty ROM with SD,
        LD-zero, and LD(-8) is proved exactly equal to production serialization (including FGL
        `p-8`); `memoryProgramBinding` has standard-only closure and is in the root import graph.
        Commit `dbf2f8c3` adds the semantic-gate probe under the required
        `root_soundness_instantiation_*.lean` glob; its direct Lean run passes with standard-only
        closure for the binding and representative SD/negative-LD row equalities.
      - [x] **P0-5b external Rust cross-check.** Submodule commit `1362c58` runs the real
        `compute_trace_rom` over a checked-in transpiled ELF, independently checks all 11 row
        fields, and includes `ld a5,-40(s0)` to exercise signed offset serialization. This is
        executable test evidence only, not kernel or trust-ledger evidence.
      - [x] **P0-9 extraction-closure coverage.** `cf77c98` imports the recovered modules
        through `ZiskFv.lean` and adds `ZiskFv.Compliance.RawProgramBinding` to the V2 raw
        axiom-closure namespaces; the rebuilt root olean and focused gate pass.
      - [x] **P0-6…P0-12.** Current `ProgramDecode` retarget, fifth `h_prog` clause,
        63-arm sweep, extraction-closure coverage, additive endpoint, ledgers, and full gates.
        `2ad5a49` is the current-API SUB pilot: it derives the fifth `store_offset` clause and
        excludes `STORE_IND` through the production builder, then constructs
        `ProgramDecode_sub` from raw claim-register bit fields. Direct elaboration and closure
        checks pass; 62 arms remain.
        `6e2b2a8` generalizes the same construction to all 14 unconditional register-family
        arms; representative closure audits pass. Conditional ADD/OR and 47 non-register arms
        remain.
        `9ce0d0e` recovers kernel-sound transpile/decode-field proofs for the 11
        branch/control/U-type arms and imports them into the build graph; their current
        `ProgramDecode` retarget remains.
        `ec7a53a` recovers the five conditional CopyB-family lowering/decode-field routes
        (ADD/OR/ADDI/XORI/ORI) with genuine routing side conditions and standard-only closure.
        `2df002cf` retargets all 12 remaining M-extension arms to current `ProgramDecode`,
        including exact production-derived destination/store pins and the existing arithmetic
        witness surfaces. Direct elaboration and all 12 constructor closure audits pass with
        standard axioms only.
        `4abc9a16` retargets the six shift-immediate arms (SLLI/SRLI/SRAI and
        SLLIW/SRLIW/SRAIW) with production-derived destination/store pins. Its focused target,
        direct elaboration, and representative closure audits pass; 32/63 current constructors
        are green and 31 remain. The four plain-immediate arms and three immediate CopyB arms
        shared a raw-12-bit decoder sign-extension prerequisite; `88d9abcd` now proves it
        kernel-only as `decode_i_rawIType_imm`, with focused build and standard-only closure green.
        `f80151ad` uses it to retarget SLTI/SLTIU/ANDI/ADDIW, deriving the serialized immediate
        lanes and production destination/store pins while retaining ADDIW's honest nonzero-rd
        routing witness. Direct elaboration and all four constructor audits pass; 37/63 current
        constructors are green.
        `5b23814e` retargets all five conditional CopyB arms (ADD/OR/ADDI/XORI/ORI), retaining
        their genuine dispatcher conditions and deriving full destination/store/immediate pins.
        Direct elaboration and all five constructor audits pass with standard axioms only;
        42/63 current constructors are green, with 11 load/store and 10 control arms remaining.
        `e24bde1c` retargets SB/SH/SW/SD with exact raw S fields, STORE_IND, faithful signed
        offsets, and production flags/jumps/width pins. Direct elaboration and all four constructor
        audits pass with standard axioms only; 46/63 current constructors are green. The seven
        loads remain behind the protected offset mismatch, while nine ordinary control arms and
        expansion-blocked JALR remain.
        `d04e21c1` retargets FENCE with only its existing non-ROM defect witnesses; direct
        elaboration and closure audit pass, bringing the sweep to 33/63. JALR exposed a genuine
        design obstruction: unaligned production lowering emits ADD then AND, but the Phase-0
        one-word/one-row `ProgramBinding` serializes only `extract_transpile_rv64im_raw`'s terminal
        AND row, so current `ProgramDecode_jalr`'s preceding ADD program fact is not derivable.
        No raw `% 4 = 0` restriction or ROM-row premise has been introduced.
        The load retarget also exposed a protected-interface mismatch: for immediate `4095#12`
        (-1), production/`ProgramBinding` serializes `signedOffset = p - 1`, while current
        `ProgramDecode_{lbu,lhu,lwu,ld}.h_prog` requires the FGL cast of the unsigned representation
        (`4294967294`). That equality is false; no nonnegative-immediate premise or protected
        interface edit has been introduced.
        AUIPC exposes the same protected unsigned-value defect for `jmp_offset2`: negative
        U-immediates demand an unsigned 64-bit `toNat` in `ProgramDecode_auipc.h_prog`, while
        production serializes the signed I64 offset into FGL. The interface remains unchanged
        and no nonnegative/top-bit premise was added.
        `90486796` retargets LUI with production-derived destination/store and ROM pins; its
        direct elaboration and closure audit pass, bringing the sweep to 47/63. `0e5ba108`
        records the representative aligned negative-branch counterexample (`-4096`): production
        serializes `p-4096 = 18446744069414580225`, while all six protected branch interfaces
        demand unsigned `18446744073709547520`. `f7a208b8` records the analogous negative-JAL
        counterexample (`1048576#21`) with standard-only closure. No branch/JAL premise or
        protected interface was changed.
        Continuation ruling: correct the protected interfaces in the faithful direction without
        another owner round-trip. Load, branch, AUIPC, and JAL surfaces must use production's
        signed `Int → FGL` representation; JALR must expose the real one-or-two-row lowering
        expansion. This authorizes the interface edits but not theorem weakening, added caller
        premises, or trust expansion.
        Initial correction commits: `5a7cc859` retargets ROM-backed constructors for the seven
        loads, six branches, AUIPC, and JAL; `b3e3a78c` repairs load/AUIPC row interfaces plus
        load StepStrong address derivations; `ea8dd5d4` updates all corresponding
        `ProgramDecode` records. Direct elaboration/focused load builds are green. Control
        StepStrong/Pilot still requires the faithful signed modular PC-addition repair.
        The load constructor pass also found that all seven protected load bundles incorrectly
        demand `STORE_REG` even for legal `rd = x0` encodings. Retarget this bit to production's
        exact destination-dependent condition; do not narrow raw decoding with `rd ≠ 0`.
        JALR expansion model `b0b5c029` (submodule `b3ef56247`) now exposes the production
        aligned AND / unaligned ADD+AND rows and binds architectural raw words to an exact,
        gap-free physical ROM layout with aligned, nonwrapping addresses and primary/successor
        eliminators. Rust/Aeneas/boundary/focused Lean checks and standard-only closure audits
        pass. `ec4f931f` adds the signed FGL PC-addition kernel lemma for branch/JAL semantics.
        Follow-up verification caught a real `Extraction.Totality` regression in `jalr_ok`'s
        expanded branch: the proof state did not yet carry the new first-row snapshot. Repair and
        rerun the exact target before accepting expansion-dependent builds.
        Repaired in `acf1c18e`; the exact three extraction targets pass with no new premise/trust.
        A shared-index collision included the already-reviewed signed branch/JAL/AUIPC control
        chunk in the same commit; retain it without amend and require a post-commit Dispatcher and
        axiom review.
        Post-commit review is green (Dispatcher 8,765 jobs, no new trust). Existing constructor
        fronts are now being migrated from physical one-row indexing to architectural
        `ProgramRowsBinding`; SUB is the dependency pilot for the ready load/control chunks.
        `393f60cb` records the final regenerated extractor pointer/artifact; `5df123dc` lands the
        shared non-JALR primary projection and all register-family architectural migrations.
        Direct elaboration and representative standard-only closures pass; Immediate/CopyB/M-ext
        continue on the same adapter.
        `27651608` completes the 12-arm M-extension migration; direct elaboration, its 9,025-job
        focused build, and all constructor closure audits pass.
        `cb37d5ce` completes all ten immediate/shift migrations with direct elaboration, a
        9,026-job focused build, and standard-only closures for every constructor.
        `82a22a4e` completes the five conditional CopyB migrations; routing hypotheses are
        unchanged, the 9,027-job focused build passes, and all closures are standard-only.
        `f4d3a755` completes all eleven memory migrations, including the faithful conditional
        load destination selector; its 9,027-job build and all closures pass.
        JALR production pins found the same class of selector defect on the unaligned ADD row:
        `rs1 = x0` uses immediate zero, not `b_src_reg`. Correct the protected JALR selector
        surfaces conditionally; do not add `rs1 ≠ 0`.
        The complete expanded-row audit also found that legal `rd = x0` suppresses both the
        destination store and `store_pc`, while aligned `jmp_offset1` is the signed I-immediate.
        The final JALR constructor must preserve those conditional/signed facts through
        ProgramDecode, RomDecode, and downstream semantics; no `rd ≠ 0`, alignment, or
        nonnegative-offset narrowing is allowed.
        `964d37e9` lands the production expanded-row pin theorem: aligned AND, unaligned first
        ADD, and unaligned successor AND are all derived with conditional x0 selectors and exact
        immediate limbs. Exact checking corrected the draft ADD opcode from `2` to production
        `10`; exact JSON elaboration, the 8,512-job aggregate build, and standard-only closure
        audit pass. Protected interface and raw-constructor integration are in progress.
        `fba84a47` completes the ten ordinary control arms (migrated LUI/FENCE plus new AUIPC,
        JAL, and six branch constructors); direct/focused builds and all standard-only closure
        audits pass. Constructor coverage is 62/63, with only expanded JALR remaining.
        `e5d8563b` integrates the JALR protected-interface correction through Dispatcher: signed
        `jmp_offset1`, conditional `rs1=x0` source selection, conditional `rd=x0` store/link
        selection, and signed target-domain next-PC arithmetic all rebuild in the exact
        8,765-job Dispatcher target, and the concrete unaligned JALR root witness directly
        elaborates. The `rd=x0` semantic branch retains the established
        multiplicity-one `eRdAt` adapter and proves its x0 pointer makes the write inert; it does
        not pretend the adapter has multiplicity zero. The final raw constructor is being made
        dependent on production's computed aligned/unaligned extraction result and is extending
        the proved aligned row pins with exact `jmp_offset1`; no alignment caller premise is
        permitted.
        `9cc02860` completes the production-selected aligned/expanded JALR constructor, the 63-arm
        `RawProgramDecode` dispatcher, and additive `root_soundness_rawProgram`. The combined
        9,040-job build and semantic axiom probe pass; the constructor dispatcher uses only
        `{propext, Classical.choice, Quot.sound}` and no endpoint premise/trust surface was added.
        P0-11 documentation now records the three residual boundaries, the independent
        non-vacuity witness, and both extraction fidelity qualifications; #61's body is refreshed.
        P0-12 full gates remain. The first full `lake build` exposed four stale concrete JAL
        domain witnesses (ADD-spin, ADD/ADDI-spin, SD/LD-spin, and DIV-spin) still naming the
        pre-`e5d8563b` `h_no_fgl_wrap` field. They are migrated to the exact signed-target
        nonnegative/upper-bound fields in `3d5beacc`; Lean LSP diagnostics and the combined
        9,085-job focused rebuild pass. The repaired full `lake build` passes all 9,132 jobs.
        V1 passes 18/18 (702 reachable modules, 28 semantic probes). V2 passes 19/19, including
        2,964 raw extraction/decode declarations with standard-only closure.
        The first `nix run .#test` exposed four stale production-extraction harness fixtures:
        stage 3/8 failed because their hand-written `Riscv2ZiskContext` literals omitted the new
        JALR expansion field `extract_first_inst`. The source template now initializes it to
        `none` in all four locations (no generated artifact was edited). The exact focused
        harness passes 1,732 jobs and reports 70 production starts / 206 declarations; the fix is
        committed as `14b679de`. The full `nix run .#test` rerun passes all eight stages,
        including the 9,132-job Lean build, V1 18/18, V2 19/19, and flake reproducibility.
        Register-family lowering progress: `7ccce3f` recovers 14 unconditional R/W-register
        transpile + decode-field lemmas; `8295fb6` recovers conditional ADD lowering and field
        binding. Both pass direct file elaboration with only
        `{propext, Classical.choice, Quot.sound}`. Further P0-8 chunks: `08fb253`
        load/store, `676ea32` immediate/shift/ADDIW, and `fabfd99` the remaining
        M-extension; all pass direct elaboration with the same axiom closure.
- [x] **Phase 0.** Refresh #61's body — it still quotes the pre-2026-06-25 signature
      (`rowDecodes : RowDecode`, a `RowOutsideDefectRegion` taking `sailTrace`/`inputsAgree`).
      Completed 2026-07-30: the body now documents the additive raw-program endpoint, exact
      expanded JALR path, current residual boundaries, and final full-gate results.
- [x] **Phase 0.** Survey, per op family, which `Claim_<op>`/`Decode_<op>` fields are (a) a
      function of the raw word alone, (b) raw word plus Main row, (c) neither. Record the table
      here. Category (c) is either an S8-class item or a genuine premise, and must be named
      before any code moves.
- [x] **Phase 1 spike — ADDI** (SUPERSEDED by the revised route-(c) P0-6…P0-10 checklist,
      which constructs all 63 current `ProgramDecode` arms through the additive endpoint without
      mutating the existing S5 witnesses). The original task was:
      (S5 instantiates it three times, so the anchor is immediate and the
      arm is free of memory and control complexity). Chain committed raw word →
      `real_decoder_accepts_in_shape` → classification → Aeneas lowering pins → constructed
      `Claim_addi`/`Decode_addi`; re-prove S5's `sdLdAddiA0Claim`/`sdLdAddiA0ProgramDecode` through
      the new route; delete the now-derivable fields on the ADDI path only.
      **Stop conditions** — failure comes back as a written decision request naming which:
      (1) the committed program is not the raw-word form the decoder consumes (representation gap,
      possibly #172-adjacent); (2) the Main row does not pin enough to identify the arm without a
      caller hint (an S8-class finding — route to a new issue); (3) the decode route works but
      `Claim_<op>` fields are needed before the decode fact is available (layering inversion).
- [x] **Phase 2 sweep** (FULFILLED by revised P0-8): all 63 arms construct current
      `ProgramDecode`, including production-selected aligned/expanded JALR. The original ordering
      was:
      ordered by blast radius, each family its own reviewed PR, S5's witness
      re-proved after each: ALU/shift immediate + register → W-mode ALU → LUI/AUIPC → loads and
      stores (memory evidence stays; only classification/placement moves) → branches + JAL
      (**JALR last, and now deferred behind S7b/#295, not S7** — S7b restores JALR's committed-ROM
      decode on the existing block-1 route; if S7b has landed, this arm inherits it, and if it has
      not, do that work as #295 rather than re-inventing it here) → M-extension (**expect to stop
      here if S8 has not landed**).
- [x] **Phase 3 binder change** (SUPERSEDED by the approved additive route-(c) design):
      `root_soundness` and `AcceptedZiskTrace` remain unchanged; `root_soundness_rawProgram`
      provides the raw-program surface and delegates to the existing theorem. The original task
      proposed: land the `root_soundness` signature change (raw committed program
      in, per-word decode facts out) as its own reviewed PR; regenerate
      `baseline-strong-export-binders.txt` deliberately with the diff explained line by line;
      never regenerate past a surprise.
- [ ] **Phase 4.** Landing/review. The completed implementation is split into six CLEAN PRs:
      #313 raw-binding foundation; #314 initial decoders; #315 fidelity/non-vacuity; #316 signed
      and expanded control rows; #317 architectural decoder migrations; #318 final control/JALR
      endpoint and closeout fixes. Merge in order, then close #61 with the already-recorded exact
      gate results and residual boundaries. The issue was reopened because local commits are not
      landed work.

Exit: #61 closed; additive `root_soundness_rawProgram` derives the existing per-row
`ProgramDecode` burden from the raw image and exact production-row binding. The headline
`root_soundness` and `AcceptedZiskTrace` remain unchanged by the approved route-(c) design.

### S10 — capstone: #186 + #184 + final sweep (was S7)

#### S10 execution checklist

- [ ] #186 proof-tower naming/structure refactor (legibility for readers) — before the audit so
      the audit documents the final shape. Renames land as separate rename-only commits/PRs
      (no content rewrite in a rename commit).
- [ ] #184 reader-facing premise audit of `root_soundness`: classify every
      `InputsAgree`/`SailTrace`/seed field; every surviving premise is derived, protocol-soundness
      class, or explicitly cited defect-gate. This is the project's closing statement — it should
      read as the paper-style trust story. (The openvm-fv comparison in
      `docs/ai/research/COMPARISON_OPENVM_FV.md` is source material; its §6 skeptic's list is the
      checklist of premises the audit must classify.) **Only honest once S7/S8 have emptied the
      "should be derivable, isn't" bucket** — that is why the capstone is last.
- [ ] Final sweep: `trust/trusted-base.md` + `trust/README.md` + `CLAUDE.md` status refresh;
      full `nix run .#test`; close remaining issues with landed-work comments; regenerate
      baselines deliberately and review the diffs.

## Sizing and risk (soundness track; ordering rationale only — no wall-time estimates)

S1–S5 are complete. Of what remains: S6 is trivial (docs). S7 is bounded and pre-priced — the
`Component.transition` route has precedent. **S8 is the real unknown.** The cherry-pick ruling
(2026-07-27) removes the *decision* risk but not the execution risk: the salvaged mirrors were
written against a pre-S3/S4 tree, so the first honest estimate comes only after the citation
re-verification pass reports how many still resolve. S9 is large but leads with a spike whose failure modes
come back as concrete decision requests, not silent scope cuts. S10 is mechanical but must be last.

## Standing constraints (both tracks)

Anti-laundering per AGENTS.md and `trust/README.md#anti-laundering-terms` throughout: deriving a
certificate means DELETING the field, never renaming or splitting it; new trust applications must
fit the existing documented classes with citations; 0 project axioms; one live branch per stream;
STATUS.md + this plan's stream list current at every checkpoint; reviewer pass and full gates
before every merge; no merges without explicit owner approval in-thread. `proofs.yml` is
push-only, so a green PR means nothing — run `nix run .#test` locally before every merge.

**Checklist hygiene (lesson from S4, 2026-07-27):** a checkbox is not evidence. Reconcile every
stream's boxes against the tree at closeout, not against the last checkpoint narrative — S4's two
final boxes sat unticked for five days while the work they described was already merged.

---

# PART II — COMPLETENESS TRACK (parked; not a current worry)

Separated 2026-07-27 by owner direction: **the soundness track is the concern; completeness is not
being worked and should not compete for attention.** Nothing here is cancelled — the completeness
endpoint remains part of the eventual mvp finish line — but no stream below is scheduled, and
agents should not pick these up without an explicit owner instruction.

Current completeness state is honest and stands on its own: `root_completeness_sail` is PROVEN;
`eventual_zisk_coverage` and `eventual_root_completeness` are CONDITIONAL and labelled as such.
The checked-in acceptance/coverage endpoints live in `ZiskFv/Completeness.lean`.

### Track B — completeness axis mvp (#108, #182, #183, #154)

Runs in the completeness stream's designated worktree (`.worktrees/completeness`). Each issue is
its own PR-sized stream. May interleave with the soundness track if a second agent is explicitly
assigned — the worktree separation exists for exactly this; coordinate via STATUS.md files.

#### Track B execution checklist (unscheduled)

- [ ] Author `PLAN_COMPLETENESS_CLOSEOUT.md` at track start (owner review before build).
- [ ] #108 — extraction of table data + witness builders (reduces the hand-maintained surface;
      MemAlignRom slice already covered by S4). Note this is also listed as a slice of the
      soundness track's extraction work; the remainder is Track B's.
- [ ] #182 — wire the proven decoder into `skeletal_root_completeness` → `root_completeness`
      (discharges `decoderAcceptsInShape` at the endpoint via `real_decoder_accepts_in_shape`).
- [ ] #183 — concrete `OutstandingZiskPredicates` instance from a real trace (the completeness
      twin of #74's non-vacuity; **the S5 SD/LD witness trace is the natural candidate** and is
      now landed, so this is cheaper than when it was written).
- [ ] #154 — close as the axis meta once the other three land.

### Completeness-labeled beyond-mvp

#174 (de-`native_decide` the Sail-decode encode-equality bridge) is completeness-labeled and
beyond-mvp; it is not scheduled here. #75/#77/#78 are dual-labeled research items, also out.
