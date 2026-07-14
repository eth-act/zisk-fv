# Summary of changes for run b5c2364e-1f9d-43a4-8a4f-46079c9f14b5
I folded the full architecture review into a single, self-contained final plan/overview and wired it in as the top-level entry point.

## What I added
- **`docs/refactor/FINAL-PLAN.md`** — one comprehensive document that consolidates the entire review (the `README` plus docs `01`–`07`) into a single narrative you can read top-to-bottom. Its ten sections are:
  1. The engagement in one paragraph.
  2. Headline conclusions (the Clean seam is more idiomatic than feared; the problems S1–S5 sit *above* it; nothing proposed weakens a theorem or grows trust).
  3. Architecture as-is — mass distribution, the data-flow pipeline, the two stacked root theorems, per-opcode multiplicity, and the inverted dependency direction.
  4. Clean idioms — the north star, what the project already does right, an idiomatic-Clean scorecard, and the four divergences D1–D4 to fix.
  5. Top-level theorem API redesign — one `SoundnessTrust`/`SoundnessScope` record so the TCB is visible in the type, demoting the old global theorem to an internal per-arm lemma with dependent-match dispatch, symmetric `root_completeness`, and one `Audit.lean`.
  6. Proof-architecture refactor — R2 (make Clean the spine, retire the `Airs/` records), R4 (derive facts at the ensemble seam), R3 (factor per shape, not per opcode), R5 (idiomatic dispatch), reusable abstractions, and file-size hygiene.
  7. Inconsistencies and correctness-adjacent smells (C1–C5, naming hazards, trust-visibility T1–T4, review gates Q1–Q4).
  8. Root-statement stability — the T0/T1/T2 change-tier discipline, the equivalence-bridge protocol, and the `#print axioms` golden test that make the refactor safe.
  9. Upstream-Clean status and tracking policy (fork base, the 6 local patches, ranked incoming PRs including #398, the `Vm.lean` overhaul, autoelaborate, Lean 4.29, witgen-ir).
  10. The sequenced, build-green, trust-monotone roadmap (Phases 0–5) with an effort/risk table, plus a mapping back to your original request and to the existing `simplification-suggestions.md`.

- **`docs/refactor/README.md`** — added a "Start here" pointer and an index row so `FINAL-PLAN.md` is the clear front door; the numbered documents remain as the detailed backing.

No proof code was changed (this is documentation/planning, as before). Everything is committed and pushed to `main`; the working tree is clean.

# Summary of changes for run eaad5f5a-e5a5-436b-b7f8-ab0a2c770e10
You're seeing a git-history artifact, not an old checkout. Here's what actually happened, based on inspecting the repo you received.

## What the returned repo looks like
The repo has exactly one commit:
- `2224b0e "Initial commit"`, authored `Aristotle <aristotle@harmonic.fun>`, dated today (2026-07-14), working tree clean.

There is no other history. Notably, even the internal commit `71d192b` that the previous run's `ARISTOTLE_SUMMARY.md` says it "committed and pushed to main" does **not** exist in what you got back. In other words, the returned repository was flattened into a single fresh snapshot commit that shares **no common ancestry** with your branch.

## Why it *looks* two weeks old (but isn't)
Because the returned snapshot has no shared history with your repo, git can't find the true merge-base when you compare/merge/rebase it against your branch. It falls back to the nearest commit whose **content** overlaps. Since your recent commits (including the build-structure change) aren't present as ancestors, the closest content match surfaces as "a commit ~two weeks old." That ancestry is an illusion produced by the history being squashed on the way back to you — it is not evidence that an old checkout was used.

## The content is NOT stale — your build-structure change IS present
I confirmed the returned working tree contains exactly the build structure you added to make the CLI launch the run:
- `lakefile.toml` explicitly documents the immutable-git-package inputs and says "Lake and Aristotle consume this exact commit directly," and wires up `ZiskFvLeanInputs`, the `Clean` fork, `ProductionM2` (`trust/aeneas`), and the `TrustGate` lib/exe.
- `flake.nix` defines the `aristotle-inputs-src` input and states "Lake and Aristotle consume it by the same immutable Git commit; CI checks it is byte-for-byte the output of packages.aristotle-inputs."
- `scripts/check-aristotle-inputs.sh` and `scripts/sync-aristotle-inputs.sh` are present.
- The previous run's actual deliverables are all present and match the summary: `docs/refactor/01..07` plus `README.md` (doc 07 = root-stability + upstream-Clean analysis).

So the run genuinely operated on the branch you sent, with your new build structure — the CLI succeeded precisely because that structure was in place. What came back is a squashed single-commit snapshot of that work; only the git history was lost, not the content.

## Two things worth double-checking on your side
1. The returned work is (per the prior summary and the files present) **documentation/plans only** — no proof code was changed. If you expected code changes, that matches the earlier "no code changes, as requested" scope, not a lost/old build.
2. To be fully certain nothing in the build wiring regressed, diff these between your branch tip and the returned tree: `lakefile.toml`, `flake.nix`, `flake.lock`, `lake-manifest.json`, and `scripts/*aristotle*`. You should find them identical (or only your intended changes).

## How to reconcile it cleanly
Don't rely on ancestry-based merge. Options:
- Treat the returned tree as a snapshot: check out your branch and overlay the returned files (e.g. copy in the new/changed files — chiefly everything under `docs/refactor/` and `docs/clean-fork-divergences.md`), then commit on top of your branch so your history is preserved.
- Or add the returned repo as a remote and `git merge --allow-unrelated-histories`, resolving conflicts, which keeps your branch history and layers the new docs on top.
- Use `git diff --no-index <your-branch-tree> <returned-tree>` to see the true content delta regardless of history.

Bottom line: the agent worked on your correct, new-build-structure branch; the "two-week-old base commit" is a side effect of the returned repo being a single squashed snapshot with no shared history, not a sign that outdated code was used.

# Summary of changes for run 0d7220f8-6f22-4d00-9646-6abb6f4de92c
I addressed both sanity-check concerns and folded the answers into the plan. No proof code was changed; the work is a new plan document plus an index update, committed and pushed to `main` (see `docs/refactor/07-root-stability-and-upstream-clean.md`, referenced from `docs/refactor/README.md`).

## 1. Keeping the root statement stable (Part A of doc 07)

You're right that the earlier plan (doc 03/R1) was too casual about editing `root_soundness`. The revised, principled approach:

- **A change-tier discipline.** Every proposed change is classified: **T0** = strictly *below* the root, the root's type is byte-for-byte unchanged (this is the default, and ~95% of the real work); **T1** = re-package existing binders only (allowed *only* behind a machine-checked equivalence proof); **T2** = actually change what is claimed or trusted (rare, isolated, its own reviewed PR, must shrink not grow the TCB).
- **The two changes you care about most — collapsing the ~63× per-opcode multiplicity and making Clean the spine — are 100% T0 and need no root change at all.** So the high-risk structural work all happens under a frozen root.
- **The root moves last, once, and provably.** Do all T0 work first; add the audit surface early; only then, if still desired, reskin the root as a T1 change behind an `old ↔ new` equivalence-bridge theorem; treat lifting hidden trust to root binders as an optional, clearly-flagged T2 step that can be deferred indefinitely.
- **Mechanical guards make accidental drift impossible:** a `#print axioms root_soundness/root_completeness` golden test under `#guard_msgs`, plus a committed statement snapshot, so any unintended root change fails the build rather than relying on review. Net: the root is untouched through the whole risky portion and simplifies below it, exactly as you asked.

Where this conflicts with the sequencing in docs 03/06, doc 07 supersedes them.

## 2. Upstream Clean (Part B of doc 07)

Yes — I examined upstream `Verified-zkEVM/clean` directly and pinned the fork precisely by content (the vendored copy was committed as a squashed "Initial commit" with no history):

- **Fork base ≈ mid-May 2026** (around upstream `main` ~`2de99379`, the PR #384 / sha256 era). Upstream `main` HEAD is `1e563b9c` (2026-07-06) — about two months and ~16 merged PRs ahead.
- **The fork carries only 6 locally-modified Clean files.** The two load-bearing ones: (a) `Air/Balance.lean`, patched to tolerate zero-multiplicity (padded) channel rows, and (b) `Air/FlatComponent.lean`/`FlatEnsemble.lean`, which add a bespoke adjacent-row `transition` field. The rest are cosmetic.
- **Incoming PRs of interest, ranked:**
  1. **#398 `fix-zero-multiplicity-channels`** (highest priority) — upstream solved *the same problem* the fork patched locally in `Balance.lean`, differently and more generally. The two overlap and will conflict on merge; adopt upstream's version and delete the local patch. This matters because channel balance is exactly the seam the proof-architecture refactor wants to derive facts from.
  2. The **`Air/Vm.lean` / `OrderedChannel.lean` overhaul** (~+400 lines) — this is the ensemble/channel-soundness machinery the review flagged as barely used; read it *before* re-proving `provider_row_facts` locally, since some of it may now exist upstream.
  3. **#375 `autoelaborate` + #425 `elaborate-circuit-parametric`** — big circuit-elaboration improvements relevant to writing components idiomatically with less boilerplate.
  4. A **new `Circuit/Formal.lean`** consolidating the `FormalCircuit`/`GeneralFormalCircuit` API the whole `AirsClean/` layer sits on — the main mechanical re-base cost.
  5. **#370 bump to Lean 4.29** — upstream is on 4.29; this project is on 4.28, so a re-base past this point forces a coordinated toolchain+mathlib bump. Recommendation: stop the re-base just before 4.29 and bump separately.
  6. **witgen-ir (#403/#413)** — a new verified witness-generation/extraction IR; not needed for soundness/completeness but worth tracking as a future extraction capability.
- **One extra finding:** the fork's local `transition` field duplicates capability upstream already offers at the `Table` layer via `InductiveTable`. Worth resolving (use `InductiveTable`, or upstream the field) rather than maintaining a silent divergence.

Suggested Clean-tracking policy (in doc 07 §B.5): adopt #398 now as an isolated well-tested step; read the current `Vm.lean` before the derive-at-seam work; settle the transition-constraint story; defer the full re-base past Lean 4.29 until the structural work is done. Importantly, **none of this touches the root theorems** — upstream alignment is all T0 from the project's side, so staying current with Clean and keeping the root stable are fully compatible.

# Summary of changes for run 91b6fca9-d7d2-42b5-8624-0b3e49bc31a2
I delivered a comprehensive, code-grounded architecture review and refactor plan (no code changes, as requested) under `docs/refactor/`, committed and pushed to `main`. It's built from a read of `ZiskFv/`, the vendored `Clean` package, and `trust/`.

**Documents (start at `docs/refactor/README.md`):**
- `README.md` — executive summary, top-10 findings, and the three highest-leverage recommendations.
- `01-architecture-map.md` — the as-is layer cake, mass distribution, the two stacked root theorems, and the ~7–9 near-parallel per-opcode layers.
- `02-clean-idioms-and-usage.md` — upstream Clean idioms vs project usage, with an idiomatic-Clean scorecard.
- `03-root-theorem-api.md` — concrete redesign of `root_soundness`/`root_completeness` (Lean sketches).
- `04-proof-architecture-refactor.md` — the structural refactor (one circuit model, per-shape factoring, deriving facts at the ensemble seam, reusable abstractions).
- `05-inconsistencies-and-correctness.md` — a located checklist of doc/code drift and correctness-relevant smells.
- `06-roadmap.md` — a sequenced, build-green, trust-monotone plan with effort/risk and exit criteria.

**Key findings.** The two seams that matter most are actually idiomatic Clean: per-component circuits are real `GeneralFormalCircuit`s with `ProvableStruct` rows and `circuit_proof_start`, and the full circuit is a `FormalEnsemble` whose per-table specs are derived from constraints + channel balance (`AcceptedZiskTrace`). The real problems sit above that seam:
1. Two stacked soundness statements — the advertised `root_soundness` (per-step, over `AcceptedZiskTrace`) is implemented by constructing `OpEnvelope` arms and invoking the older `zisk_riscv_compliant_program_bus`, so the trusted premises are split between the theorem's binders and internal `OpEnvelope` fields (`aeneasBridgeTrust`, memory-timeline evidence) that are invisible in its type.
2. Two parallel circuit models — a legacy record model (`Airs/`, `Valid_Main` referenced by ~299 files) bridged per-opcode into the Clean components, so the idiomatic layer is a tributary rather than the spine.
3. ~63 opcodes × 7–9 near-identical layers (`Airs`, `AirsClean`, `EquivCore`, `Equivalence`, `Compliance/Wrappers`, `Compliance/Construction*`, `OpEnvelope`, `TraceLevelExport`).
4. A bespoke promise/caller-burden/forbidden-shape trust discipline standing in for facts that Clean's ensemble soundness (`Vm.lean`/`OrderedChannels.lean`, used in ~0 files) is designed to derive.
5. Documentation that contradicts the code (e.g. `EquivCore/README.md` actually documents `Equivalence/`; the wrapper/canonical dependency direction is inverted vs the code; `trust/trusted-base.md` names the old theorem as "the global theorem" while READMEs name `root_soundness`).

**Top recommendations.** R1: unify to a single advertised soundness endpoint with one `SoundnessTrust`/`SoundnessScope` record so the whole TCB is visible in the type; make completeness symmetric (`root_completeness` + one obligations record) and add a single `Audit.lean` audit surface. R2: make the Clean component `Spec`s the spine and retire the `Airs` record model + per-opcode bridges. R3: factor per-*shape* (~12 families) instead of per-opcode, deriving provider/lane/pin facts once from channel balance. The roadmap sequences these to keep the build green and the trust ledger monotonically shrinking. The plan extends (and partly supersedes) the existing tactical `simplification-suggestions.md`, which it cross-references.

All work is committed (commit `71d192b`) and pushed; the working tree is clean.