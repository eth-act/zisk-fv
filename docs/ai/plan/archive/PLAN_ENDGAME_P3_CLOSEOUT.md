# Plan: ENDGAME P3 CLOSEOUT — honest reshape + auditability + precise P4 hand-off

Status: READY FOR EXECUTION. **This is the single authoritative plan for closing
P3.** It SUPERSEDES the "PR 5" section of `PLAN_ENDGAME_P3.md` and the earlier
`PLAN_ENDGAME_P3_PR5_REWORK.md`. Reviewer: the plan author. Open each PR per
protocol and STOP; do not merge. Anchors: #76, #74 (stage 3), #61.

---

## §0. What P3 is — and what it is NOT (read first; the plan depends on it)

**P3 cannot reduce memory trust. That is now proven, not suspected.** Deep
survey of the codebase established that every reducible memory fact requires
P4's whole-trace `AcceptedTrace → OpEnvelope` construction:

- `prefixReadSound` IS derivable from the Mem AIR constraints — but only
  **single-segment** (orphaned chain at `ZiskFv/AirsClean/FullEnsemble/Balance.lean`
  ~6474, output type `AcceptedMemoryReplayEvidence`). The load residual needs
  `prefixReadSound` over the **whole-trace** row list (multi-segment), and the
  cross-segment chronological assembly **does not exist** — building it IS P4.
- `initialAgreement` (Sail `initialState.mem` = circuit `initialMemory`) has
  **no producer anywhere** and mentions the Sail initial state, so it is an
  irreducible **boot premise** — P4/program-binding, never `Valid_Mem`.
- `MemoryPrefixStateAlignment` (`state = stateAfterMemoryBusRows initialState
  priorRows`) is the execution-timeline identification — **P4-bound** by
  definition.

Therefore the **honest, correct goal of P3** is NOT a trust reduction. It is:

> **Reshape the single opaque memory promise into the MINIMAL NAMED residual,
> make that residual AUDITABLE, and hand P4 a precise obligation ledger.**

This is genuinely valuable — it is exactly what makes P4 tractable and what
stops the laundering #88 risked (an unmeasured reshape that reads as a
discharge). But anyone — including the executing agent — who tries to make P3
"shrink the TCB" is chasing something that lives in P4. **Do not.**

The single real reduction P3 *already* banked (via #87): `selectedRead` and
`stateBytesAtPrefix` are now DERIVED from the alignment + structural promises
rather than assumed. That is the whole micro-reduction available at this layer.

---

## §1. The memory trust ledger (definitive — this IS the P4 hand-off)

For each component of the load residual `Nonempty (MemoryTimelineEvidence
state e1)` / `LoadMemoryTimelineConstructionEvidence` (`ZiskFv/Compliance/OpEnvelope.lean:2272`):

| Component | Status after P3 | Who removes it | Asset for the remover |
|---|---|---|---|
| `selectedRead` | **DERIVED** (`Construction.lean`, from `LoadStructuralPromises` tags) | — (done) | — |
| `stateBytesAtPrefix` | **DERIVED** from `alignment` + `initialAgreement` (`Construction.lean:43`) | — (done) | `replayAgreement_after_memoryBusRows` |
| `prefixReadSound` | **NAMED, P4-bound** | P4 | orphaned single-segment chain `Balance.lean:6172/6474` (`mem.pil:377`) + a NEW cross-segment whole-trace assembly P4 must build |
| `initialAgreement` | **NAMED, P4/boot premise** | P4 / program-binding | none — irreducible boot fact (Sail-tied) |
| `MemoryPrefixStateAlignment` | **NAMED, P4-bound** | P4 | the trace construction's running-state invariant |
| store RMW preserved bytes (`sb`/`sh`/`sw` `h_m*`) | **bucket-(c), OUT OF P3 SCOPE** (load-only) | P4 | flagged by the #61 bucket audit; extend `memoryTimelineEvidence` to store events |

Writing this ledger down precisely, as `trust/memory-argument-obligation-map.md`,
is P3's most valuable deliverable. P4's plan will be written against it.

---

## §2. Close-out sequence — the PRs

P1 is fully landed (#83 merged via #89; `envelope-burden-audit.md` on main,
commit `cf2a4aa6`). P3 PRs #84–#88 are open, stacked, and forked off a stale
pre-#81 base — **all must be rebased onto current `origin/main` first** (a survey
confirmed merging them un-rebased would revert #79/#81 work).

| PR | Action to close it | Blocking fix |
|---|---|---|
| #84 obligation map | Fold its obligation-map deliverable into §3 PR-A (it was skipped). Keep the CLAUDE.md baseline-path fix. | rebase |
| #85 ordering lemmas | Merge as-is; they are sound but **orphaned** — record in the obligation map that they are available to P4 (single-address ordering), unused by the current construction. | rebase |
| #86 linkage | **Fix the false PR-body axiom-closure claim** (two `traceSplit` lemmas inherit `ofReduceBool`/`trustCompiler` from upstream `native_decide`; on current main re-check whether that still holds post-#81 and state it correctly). | rebase + body fix |
| #87 construction core | Sound; merge after rebase. It defines the residual + the `selectedRead`/`stateBytesAtPrefix` derivations. | rebase |
| #88 "reduce…" | **REWORK per §3.** As-is it is an unmeasured, undocumented, degenerately-witnessed reshape. | full rework |

Merge order after rebase: #84 → #85 → #86 → #87 → (#88 rework). Each is its own
PR; do not re-stack on phantom bases.

---

## §3. The #88 rework — the substantive remaining work (two PRs)

### Rework-PR-A — auditability apparatus + obligation map

The fix for the root cause: the trust gate is **blind** to the global theorem
(its baselines cover only the 63 `equiv_<OP>`; the global hypothesis list is in
no baseline — only its axiom closure). That blindness is why #88's reshape moved
no metric. Close it.

- [x] **Global-theorem-binder baseline.** Add a `print-global-binders` subcommand
      to `bin/TrustGate/Main.lean` (hardcode the target `ZiskFv.Compliance.zisk_riscv_compliant_program_bus`
      exactly as `cmdCheckClosureVsBaseline` does, `Main.lean:308`), backed by a
      render-only sibling of `checkTheorem` in `bin/TrustGate/TypeWalk.lean:85`
      (reuse `Meta.forallTelescope` + `Meta.inferType` + `Meta.ppExpr`; emit
      `idx :: name :: type` per binder; NO forbidden-set match). Generate
      `trust/generated/baseline-global-theorem-binders.txt` capturing the CURRENT
      main state (`h_bridge`, `h_memory_timeline`, `h_known_bugs`). Add a
      regenerate line to `trust/scripts/regenerate.sh` (in the `.lake/build`
      block); add checker `trust/scripts/check-global-theorem-binders.sh` (copy
      `check-closure-vs-baseline.sh` conventions, exact diff); wire into
      `trust/scripts/check-all-semantic.sh`; add a README "Generated Files" row.
- [x] **Obligation map.** Create `trust/memory-argument-obligation-map.md` =
      the §1 ledger verbatim, with file:line citations and the explicit statement
      from §0 that P3 reduces nothing and every named residual is P4-bound. This
      is the deliverable #84 skipped and the document P4's plan is written against.
- [x] Verification block (§5). The global-binder baseline is NEW here (not a
      diff). Open PR per protocol; STOP.

### Rework-PR-B — honest residual + non-degenerate witness + the visible diff

Rebase #88's content onto Rework-PR-A.

- [x] Keep #88's `memoryTimelineConstructionEvidence` residual + the three
      dispatcher rewires + `OpEnvelope` glue (architecturally correct). Do NOT
      revert to the opaque `memoryTimelineEvidence`. Do NOT re-assume
      `selectedRead`/`stateBytesAtPrefix`.
- [x] **Regenerate the global-binder baseline.** It MUST now show exactly one
      reviewable change: the memory hypothesis line
      `... : env.memoryTimelineEvidence` → `... : env.memoryTimelineConstructionEvidence`.
      Paste this diff in the PR body — **this diff IS the audit evidence that the
      reshape happened.** `h_bridge`/`h_known_bugs` lines unchanged.
- [x] **Non-degenerate alignment witness.** Add
      `trust/consistency/memory_prefix_alignment_witness.lean` proving
      `MemoryPrefixStateAlignment initialState (stateAfterMemoryBusRows
      initialState [storeRow]) [storeRow]` for a concrete single-store `storeRow`
      — a NON-empty prefix, so the residual is shown satisfiable beyond the
      `priorRows=[]` case #88 used. No sorry/axiom. Wire into the semantic gate.
- [x] **LD instantiation** (`trust/consistency/global_theorem_instantiation_ld.lean`):
      keep, but add an in-file + obligation-map + PR-body note that it is the
      empty-prefix satisfiability witness and the non-empty case is covered by
      `memory_prefix_alignment_witness.lean`. No silent degeneracy.
- [x] Confirm `baseline-hypothesis-count.txt`, `baseline-caller-burden.txt`,
      `baseline-wrapper-caller-burden.txt`, `baseline-equiv-axiom-deps.txt` are
      **byte-identical** (P3 touches no canonical `equiv_<OP>` signature). If any
      changed, you diverged — revert.
- [x] **PR body** (honest): Summary / Scope / Verification / Notes + the §4
      self-check. State plainly: this is a RESHAPE to a named P4-bound residual,
      NOT a trust reduction; list the §1 residual ledger; name P4 as the remover.
- [x] Verification block; open PR per protocol; STOP.

---

## §4. Hard guardrails (anti-divergence — violating any fails review)

1. **No trust-reduction / shrink / removal / discharge claim.** The honest verb
   is **reshape** / **reduce-to-named-P4-fact**. The PR title/body/commits say so.
2. **Do NOT wire `prefixReadSound`.** It needs P4's cross-segment whole-trace
   assembly (the single-segment `Balance.lean` chain does not match the residual's
   whole-trace `rows`). Attempting it is the #1 divergence trap. Record it in the
   obligation map as P4-bound with the `Balance.lean` asset pointer and STOP.
3. **Do NOT add any `OpEnvelope` field, `Valid_Mem` field, or new hypothesis** to
   make anything "go through." If a step seems to need a new assumption, that
   assumption is a P4 residual — name it in the ledger and stop.
4. **Do NOT slim `equiv_<OP>`** from `LoadPromises` to `LoadStructuralPromises`.
   It is cosmetic for the global trust surface (dispatch constructs the timeline
   from the single `h_memory_construction`) and would GROW the per-opcode
   caller-burden. Canonical load signatures stay byte-identical.
5. **No new `axiom`/`sorry`/`opaque`/`partial def`/`unsafe def`/`native_decide`.**
   Global project-axiom closure stays 0.
6. **No strengthening of `Valid_Mem`/`Spec`/`Assumptions`**; new helpers
   `@[reducible]`.
7. **Do NOT edit** `trust/forbidden-*.txt`, `trust/allowed-axiom-files.txt`,
   `trust/structural-unpacking-exceptions.txt`.
8. **Do NOT delete `#85`'s ordering lemmas** and do NOT force a contrived use —
   document them as a P4 asset.

---

## §5. Verification block + Definition of Done (grep-able)

Run before each PR, in order:
```bash
lake build
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh        # must include the new global-binder check
nix run .#test
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
git diff origin/main -- trust/
```

DoD (the reviewer runs these):
- [x] `test -f trust/generated/baseline-global-theorem-binders.txt`; it lists the
      global theorem's binders incl. the memory hypothesis line.
- [x] After PR-B: `git log -p` of the baseline shows the memory line changed
      `memoryTimelineEvidence` → `memoryTimelineConstructionEvidence` (the audit
      evidence of the reshape).
- [x] `test -f trust/memory-argument-obligation-map.md`; it contains the §1 table
      with `prefixReadSound`, `initialAgreement`, `MemoryPrefixStateAlignment`
      each marked P4-bound, plus the `Balance.lean` asset pointer.
- [x] `git diff origin/main -- trust/generated/baseline-hypothesis-count.txt
      trust/generated/baseline-caller-burden.txt
      trust/generated/baseline-wrapper-caller-burden.txt` is EMPTY.
- [x] No new axioms/sorry/native_decide in the diff; closure print = 0.
- [x] `test -f trust/consistency/memory_prefix_alignment_witness.lean`; non-empty
      prefix; typechecks; no axioms/sorry.
- [x] PR body contains "reshape" / "reduce-to-named-P4-fact", names the §1
      residual, and does NOT claim removal/shrink.

---

## §6. What P3 hands P4 (why this close-out matters)

On completion, P4 inherits a clean, named, measured starting point:
1. A minimal residual `LoadMemoryTimelineConstructionEvidence` with every leaf
   either derived (`selectedRead`, `stateBytesAtPrefix`) or named P4-bound.
2. The obligation ledger (§1) telling P4 exactly what to build: whole-trace
   cross-segment `prefixReadSound` assembly (reusing the orphaned `Balance.lean`
   chain), the running-state `alignment`, the `initialAgreement` boot premise,
   and the store-side bucket-(c) extension.
3. A gate that will MEASURE P4's actual reduction: when P4 discharges the
   residual, `baseline-global-theorem-binders.txt` will show the memory
   hypothesis shrink/vanish — the proof, finally, that trust was reduced.

P3 done ≠ trust reduced. P3 done = P4 is now a well-scoped, measurable job.

## Log
(append one line per milestone; do not expand the plan body)

- 2026-06-13: Execution started. First operation is restacking the existing
  #84–#88 branches onto `origin/main` at `cf2a4aa6`; local STATUS/submodule
  dirt in the per-PR worktrees will be preserved outside the PR payloads.
- 2026-06-13: Restack complete and pushed with leases. New heads: #84
  `8cf7639b`, #85 `a02899f0`, #86 `ac8fc613`, helper
  `endgame-p3-pr4-base` `9b58b5f4`, #87 `7703486e`, #88 `f6cd723d`; all
  range-diffs were identity. Verified on #88 head: `lake build`,
  `trust/scripts/check-all.sh`, and `trust/scripts/check-all-semantic.sh`.
- 2026-06-13: Rework-PR-A branch/worktree
  `.worktrees/endgame-p3-closeout-prA` created from #87 (`7703486e`).
  TrustGate `print-global-binders` now renders the current global theorem
  binders, including `h_memory_timeline :: env.memoryTimelineEvidence`;
  checker/regenerate wiring and the obligation map are in progress.
- 2026-06-13: Rework-PR-A payload implemented: global-binder baseline,
  exact-diff checker, semantic-gate wiring, regenerate/README entries, and
  `trust/memory-argument-obligation-map.md`. Focused
  `lake build ZiskFv.Compliance trust-gate` passed; §5 verification block is
  next.
- 2026-06-13: Rework-PR-A committed as `544dcda` on
  `endgame-p3-closeout-prA`. Verification passed: `lake build`,
  `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`,
  `lake build LeanRV64D Clean` (fresh-worktree dependency oleans for semantic
  scripts), `nix run .#test`, empty global axiom-closure print, and
  `git diff origin/main -- trust/`. Next: push and open PR against
  `endgame-p3-pr4`.
- 2026-06-13: Rework-PR-A pushed and opened as #90
  (`https://github.com/eth-act/zisk-fv/pull/90`) against `endgame-p3-pr4`;
  GitHub reports CLEAN. Per protocol, stop here before §3 Rework-PR-B unless
  directed.
- 2026-06-13: Rework-PR-B execution started on top of Rework-PR-A / #90
  (`544dcda`). First step is creating a separate PR-B worktree, then porting the
  #88 reshape onto the new global-binder gate and adding the required
  non-empty alignment witness.
- 2026-06-13: Rework-PR-B worktree created and #88 payload replayed without
  committing. Added the non-empty store-prefix alignment witness, wired it into
  the semantic gate, and added LD/obligation-map notes separating the LD
  empty-prefix witness from the new non-empty prefix witness.
- 2026-06-13: PR-B fresh-worktree setup completed: `nix run .#populate`, `lake
  exe cache get`, and `lake build LeanRV64D Clean` passed. Focused
  `lake build ZiskFv.ZiskCircuit.MemTimeline.Construction`,
  `lake env lean trust/consistency/memory_prefix_alignment_witness.lean`,
  `lake build ZiskFv.Compliance trust-gate`, `lake build ZiskFv`, and full
  `lake build` passed.
- 2026-06-13: PR-B regenerated `baseline-global-theorem-binders.txt`; the diff
  is exactly the memory binder line changing from `env.memoryTimelineEvidence`
  to `env.memoryTimelineConstructionEvidence`. Canonical baselines
  `baseline-hypothesis-count.txt`, `baseline-caller-burden.txt`,
  `baseline-wrapper-caller-burden.txt`, and `baseline-equiv-axiom-deps.txt` are
  byte-identical vs PR-A and `origin/main`.
- 2026-06-13: PR-B verification passed: `trust/scripts/check-all.sh` after
  initializing the pinned `zisk` submodule, `trust/scripts/check-all-semantic.sh`,
  `nix run .#test`, explicit empty global axiom-closure print, and post-commit
  `git diff origin/main -- trust/`. Payload grep found no added proof escapes
  beyond semantic-script guard text.
- 2026-06-13: Rework-PR-B committed as `5236c19b`, pushed, and opened as #91
  (`https://github.com/eth-act/zisk-fv/pull/91`) against
  `endgame-p3-closeout-prA`; GitHub reports CLEAN. Per protocol, stop here.
- 2026-06-13: Re-read #91 after PR-body correction; body starts with
  `Queued for Claude review — do not merge.` and still reports CLEAN.
