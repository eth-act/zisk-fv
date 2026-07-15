# 07 — Root-statement stability & upstream Clean

This document answers two sanity-check questions raised after the initial review:

1. **Root stability.** How do we run this refactor *without* destabilising the
   root theorem statement? The ideal: almost all work happens *below* the root,
   and any change to the root is a small, principled, provably-equivalent
   restatement that only *unlocks simplifications* underneath — never a change to
   what is actually claimed or trusted.
2. **Upstream Clean.** Did we look at upstream `Verified-zkEVM/clean`? How far has
   it moved since the fork, and which incoming PRs matter for this project?

Both answers change the *sequencing and framing* of the plan in `03`/`06`, not
its destination. This document is the authoritative statement on those two
points; where it differs from `03`/`06`, follow this document.

---

## Part A — Keep the root statement stable

### A.1 The governing principle

Treat the root theorems as a **frozen public API**. The refactor is overwhelmingly
an *implementation* change beneath a fixed interface. Concretely, split every
proposed change into one of three tiers and gate each tier differently:

| Tier | What it changes | Allowed? | Gate |
| --- | --- | --- | --- |
| **T0 — below the root** | Anything strictly under `root_soundness` / `root_completeness`: lemma structure, the `Airs`↔`AirsClean` model, per-opcode→per-shape factoring, deriving facts at the ensemble seam. The root's *type is byte-for-byte unchanged*. | **Default.** This is where ~95% of the work in `04`/`06` lives. | `git diff` shows no change to the root's signature; `#print axioms` unchanged. |
| **T1 — reskin the root, same content** | Re-package the *existing* hypotheses/conclusion (e.g. bundle already-present binders into a `SoundnessTrust` record, rename an internal theorem, turn a `True`-padded conjunction into a dependent match). No premise is added, removed, weakened, or strengthened. | **Only with an equivalence proof** (A.3). | A machine-checked `old ↔ new` bridge theorem + unchanged `#print axioms`. |
| **T2 — change what is claimed/trusted** | Add/remove/relocate a *trusted* premise, change the conclusion's strength, or move something between "checked" and "believed". | **Rare, explicit, reviewed.** Never a side effect of a cleanup. | Its own PR, its own trust-ledger delta, called out in the summary; must *shrink* (never grow) the TCB. |

The initial review's R1 (§`03` 3.2) was written as if the trust-surface record is
free to alter the root binders. Re-classified under this tier system, and
**corrected** for a stale premise, R1 is a **single T1 move**:

- R1 only *renames/bundles binders already present* on `root_soundness`
  (`inputsAgree`, `bootSeed`, and the scope binder) — that is **T1**, made safe by
  an equivalence bridge (A.3) with an unchanged `#print axioms`.
- The originally-proposed second move — *lifting "hidden trust"*
  (`aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`) from internal
  `OpEnvelope` fields up to root binders — is **dropped**. It rested on a stale
  premise: those fields are **not** hidden trust of `root_soundness`. They are
  hypotheses of the *internal* `zisk_riscv_compliant_program_bus`, discharged on
  the path to the root (`StepStrongAluArith.lean:223`; `trivial`/`bootSeed`-derived
  for memory), as the frozen `#print axioms root_soundness` in `ZiskFv/Audit.lean`
  confirms. Making them binders would re-introduce discharged premises and
  *weaken* the root — a trust-*growing* change, not an honesty fix — so there is no
  legitimate T2 component here.

### A.2 Sequence so the root moves last, once, and provably

Reorder the roadmap around root stability:

1. **Do all T0 work first, under the unchanged root.** Phases 2–4 of `06`
   (derive-at-seam, one circuit model, shape factoring) are *entirely* T0. None of
   them needs the root's type to change. Land them first. The payoff — smaller
   `equiv_*` signatures, no `Bridge.lean`, ~12 shapes instead of ~63 opcodes —
   accrues without an auditor ever seeing a different `root_soundness`.
2. **Add the audit surface without touching the root (T0).** `Audit.lean` (§`03`
   3.5) and the `#print axioms` / `#guard_msgs` golden test (A.4) are pure
   additions. Do this early: it is the tripwire that makes every later step
   prove it did not disturb the root.
3. **Only then, if still desired, reskin the root (T1) behind an equivalence
   proof** (A.3). By this point the binders being bundled are already minimal
   (T0 removed the derivable ones), so the record is small and honest.
4. **No residual trust-visibility (T2) step is required.** The once-suspected
   hidden trust (`aeneasBridgeTrust`, `memoryTimelineConstructionEvidence`) is
   discharged, not trusted (A.1), so there is nothing to lift. Making them root
   binders would *weaken* the theorem and is explicitly **not** planned. If a
   genuine future trust change ever arises (e.g. importing generated Aeneas Lean
   that removes an assumption), it ships as its own reviewed PR and must *shrink*
   the TCB.

Net effect: the root statement is untouched through the entire high-risk portion
of the work, and changes at most once, late, under a proof obligation.

### A.3 The equivalence-bridge discipline (how a T1 change is made safe)

Never edit the root statement in place. Instead:

```lean
-- 1. Keep the current root verbatim, renamed as the internal engine.
theorem root_soundness_core … := <existing proof>

-- 2. State the new, prettier root.
theorem root_soundness … := <thin adapter around root_soundness_core>

-- 3. Prove they say the same thing (both directions), machine-checked.
theorem root_soundness_iff_core : (statement of root_soundness) ↔ (statement of root_soundness_core) := …
```

The `_iff_core` bridge is the receipt that the reskin is content-preserving; it is
what lets an auditor trust that the "beautiful" statement did not quietly drop a
hypothesis. Once the bridge is proven and reviewed, `_core` can be inlined or kept
as an internal lemma. The same pattern covers the completeness rename
(`skeletal_root_completeness → root_completeness`) — trivially, since that is a
pure rename.

### A.4 Make root drift *impossible to do by accident*

Add two mechanical guards so any unintended root change fails CI, not review:

- **Axiom golden test.** In `Audit.lean`:
  ```lean
  /-- If this breaks, the TCB of the root changed. Update deliberately. -/
  #guard_msgs in #print axioms root_soundness
  #guard_msgs in #print axioms root_completeness
  ```
  Any new dependency (a stray `sorry`, a new trusted premise reached through the
  proof) changes the printed axiom set and breaks the build.
- **Statement snapshot.** Keep the pretty-printed type of each root in a checked
  file (a `#check @root_soundness` under `#guard_msgs`, or a committed
  `.txt` compared in CI). A binder rename or a lifted premise then shows up as a
  failing snapshot diff — turning "did the root change?" from a review judgement
  into a build result.

With these in place, T0 steps are provably root-neutral (both guards stay green),
and only a deliberate T1/T2 step is *allowed* to update the snapshot — in the same
PR that explains why.

### A.5 Bottom line on stability

The good news is that the two changes the request cares about most — collapsing
the per-opcode multiplicity and making Clean the spine — are **100% T0** and need
no root change at all. The trust-surface record is a nice-to-have that can be done
later, safely, behind an equivalence bridge, or skipped. So the principled answer
is: **freeze the root with a golden test, do the structural work beneath it, and
let the root simplify last (if at all) as a provably-equivalent reskin.**

---

## Part B — Upstream Clean status and incoming work

### B.1 Where the fork sits

The vendored copy under `.lake/packages/Clean` was committed as a squashed
"Initial commit" (no upstream history), but its content pins the fork precisely:

- **Fork base ≈ mid-May 2026**, around upstream `main` commit `2de99379`
  ("minor", 2026‑05‑11), i.e. the **PR #384 / #372 (sha256) era**. Matched by
  content: the vendored tree differs from `2de99379` in only **6 files**, all of
  them deliberate local edits (below).
- **Upstream `main` HEAD is `1e563b9c` (2026‑07‑06)** — roughly **two months and
  ~16 merged PRs ahead** of the fork base.

So yes: upstream has moved significantly since the fork, and the fork is now about
a release-quarter behind.

### B.2 What the fork changed locally in Clean (6 files)

These are the fork's own patches — the things a re-base must preserve or
reconcile:

| File | Local change | Status vs upstream |
| --- | --- | --- |
| `Clean/Air/Balance.lean` | Strengthened the "balanced ⇒ a non-pull push exists" lemma to tolerate **zero-multiplicity (padded / selector-gated) rows** (conclusion `b.mult ≠ -1 ∧ b.mult ≠ 0`), plus a new `balanceOf_eq_neg_count_of_mult_neg_one_or_zero`. | **Now upstreamed differently** — see B.3, PR #398. Reconcile, don't keep both. |
| `Clean/Air/FlatComponent.lean` | Added an **adjacent-row `transition` field** + `TransitionConstraints`, so a component can constrain consecutive rows (VM step transitions). | **Genuinely local.** Upstream `FlatComponent` still says "no direct adjacent-row constraints." See B.4. |
| `Clean/Air/FlatEnsemble.lean` | Ensemble-level `TransitionConstraints` to match. | Local, paired with the above. |
| `Clean/Utils/Misc.lean` | Wrapped `Fin.foldl_eq_foldl_finRange` in `namespace Clean`. | Cosmetic; trivially rebased. |
| `Clean/Gadgets/Keccak/Permutation.lean` | One `simp` name update for the above namespacing. | Cosmetic. |
| `Clean/Examples/FibonacciWithChannels.lean` | Example tweak. | Cosmetic; upstream owns examples. |

The load-bearing local patches are exactly the two that matter for this project's
correctness story: **channel balance with padding** and **adjacent-row
transitions**.

### B.3 Incoming upstream PRs of interest

Merged on upstream `main` since the fork base, ranked by relevance to this project:

1. **#398 `fix-zero-multiplicity-channels` (2026‑06‑25) — highest priority.**
   Upstream reworked `Air/Balance.lean`, `Air/Vm.lean`, `Air/OrderedChannel.lean`
   to handle zero-multiplicity channels (new `balanceOf_eq_filter_ne_zero`,
   `balanceOf_eq_of_const_zero`, explicit zero-padding balance lemmas). **This is
   the same problem the fork patched locally in `Balance.lean`.** The two solutions
   overlap and will conflict on merge. Action: adopt upstream's version as the
   canonical treatment and delete the local patch, re-checking that the project's
   `AcceptedZiskTrace` channel reasoning still goes through. This is both a
   de-duplication *and* a chance to inherit upstream's more general lemmas. It is
   the single most important item to track from upstream, because channel balance
   is exactly the seam `04`/R4 wants to derive facts from.

2. **`Air/Vm.lean` overhaul (+~413 lines, part of #398 and neighbours).** The VM /
   ordered-channel soundness layer — the machinery the review (`02`, `04` R4)
   flagged as *used in ≈0 project files despite being the intended source of the
   provider/lane/pin facts* — has been substantially expanded upstream. Before
   building the project's own `provider_row_facts` (roadmap 2.1), **read the
   current upstream `Vm.lean`/`OrderedChannel.lean` first**: some of what 2.1
   plans to prove locally may now exist upstream.

3. **#375 `autoelaborate` (2026‑06‑04) + #425 `elaborate-circuit-parametric`
   (2026‑07‑06).** Major expansion of `Circuit/Explicit.lean` (+~1000 lines) and a
   new `Circuit/ExplicitAttributes.lean`: automatic / parametric circuit
   elaboration. Directly relevant to the "idiomatic component definition" goal
   (`02`) — the per-component `GeneralFormalCircuit` boilerplate the project writes
   by hand may shrink with the newer elaborator.

4. **New `Circuit/Formal.lean` (+~446 lines, not present in the fork).** Upstream
   consolidated the `FormalCircuit` / `GeneralFormalCircuit` API into a dedicated
   file. Since the whole `AirsClean/` layer is built on these, a re-base needs to
   account for the moved/renamed API surface. This is the biggest *mechanical*
   merge cost.

5. **#370 `bump-lean-4.29` (2026‑07‑06).** Upstream is now on **Lean 4.29**; this
   project is on **4.28** (`lean-toolchain: leanprover/lean4:v4.28.0`, mathlib
   `v4.28.0`). Any upstream re-base past this PR forces a coordinated Lean+mathlib
   bump of the whole project — a non-trivial, all-or-nothing step. Plan the re-base
   as either "stop just before #370" (stay on 4.28) or "bump everything at once."

6. **witgen / witness-export track: #403 `witgen-ir` (2026‑07‑01), #413
   `witgen-ir-framework` (2026‑07‑04).** New `Circuit/WitnessIR.lean`,
   `WitnessExport.lean`, `WitnessGeneration.lean`, `WitnessIRSugar.lean` (~1800 new
   lines) — a deep-embedded witness-generation IR with an exportability checker and
   JSON serializer. Not needed for soundness/completeness, but **highly relevant if
   the project ever wants a verified extraction path** from the Lean circuits to a
   runnable prover. Worth tracking as a future capability, not a current merge
   need.

7. **Gadget/infra:** #372 `sha256` (new gadgets), #406 rotation `bvdecide` timeout
   fix, and several bench/CI PRs (#384/#385/#390/#393). Low relevance unless the
   project uses those gadgets.

### B.4 The transition-constraint divergence is worth resolving upstream-first

The fork's `FlatComponent.transition` field is a genuine capability upstream
lacks *at the `Air` layer*. But upstream already provides adjacent-row / two-row
semantics at the **`Table` layer** via `InductiveTable` (`Clean/Table/Inductive.lean`:
a `step : Var State → Var Input → Circuit (Var State)` with soundness/completeness
over consecutive rows). So there are two ways the project's VM-step transitions
could be expressed, and the fork chose a third (a bespoke `Air`-layer field).

Recommendation: before investing further in the local `transition` field,
evaluate whether the project's step transitions can be expressed with upstream
`InductiveTable` (or by upstreaming the `FlatComponent.transition` field as a PR).
Either path removes a load-bearing local divergence from Clean and keeps the
project on the idiomatic upstream track — which is the whole point of the "use
Clean idiomatically" goal. This is a T0 change from the *project's* perspective
(it does not touch the root), but it is the highest-value Clean-alignment item
after adopting #398.

### B.5 Suggested Clean-tracking policy

- **Adopt #398 now** (reconcile the local `Balance.lean` patch away); it is
  correctness-relevant and de-duplicates a local patch. Do this as an isolated,
  well-tested step because it touches the channel-balance seam everything rests
  on.
- **Read current upstream `Vm.lean`/`OrderedChannel.lean` before roadmap 2.1**, to
  avoid re-proving `provider_row_facts` from scratch.
- **Decide the transition-constraint story** (B.4): upstream `InductiveTable`,
  upstream the field, or keep local — but stop maintaining a silent divergence.
- **Defer the full re-base past #370** (Lean 4.29) until the T0 structural work is
  done; a toolchain bump mid-refactor multiplies risk. Pin the intended upstream
  target explicitly (e.g. "re-base to the last pre‑4.29 commit, then bump
  separately").
- **Track witgen (#403/#413) as a future extraction capability**, not a current
  dependency.

None of the above changes the root theorems; all of it is T0 for the project.
Upstream alignment and root stability are therefore compatible: the Clean work is
merge/rebase discipline underneath a frozen public interface.
