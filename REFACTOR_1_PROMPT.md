# Task: finish refactor Phase 2 (derive facts at the ensemble seam)

## Where you are — read this before touching anything

You are on branch `refactor-1`, and **this tree is the current source of truth**.
Your previous run was seeded from a stale lineage: its export silently reverted
two merged main PRs (#253 Mem row ranges / #254 indexed fixed columns), the
Clean-pin sync, and a README fix. That damage was repaired during integration;
your actual Phase 2 work survived and is already committed here:

- `ZiskFv/Compliance/AcceptedZiskTrace/DerivedRowFacts.lean` — your
  `opProviderRowFacts`, `staticBinarySubProviderRowFacts`, and
  `registerWriteLanes`, integrated on the current base.
- `ZiskFv/Compliance/TraceLevelExport/StepStrongAluArith.lean` — SUB provider
  path and all 28 lane derivations migrated to the seam facts.
- The plan set under `docs/refactor/` including the §4.1 correction note.

Consequences you must respect:

1. **Treat the checked-out tree as the base.** Do not re-apply anything from
   your previous sandbox state, and do not "fix" files that look different from
   what you remember — they are newer than your memory.
2. **Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`, or
   `flake.lock`.** In particular the Clean fork pin is
   `c87617d8e29386e1e9e4f98cfbfb6940c2eb63df` and must stay there. A diff that
   downgrades it to `497e4a41…` means you have regressed the tree.
3. The current tree already includes #253/#254 machinery
   (`ZiskFv/AirsClean/Mem/GeneratedTransition.lean`, `Mem/SidecarColumns.lean`,
   the reworked `AcceptedZiskTrace`, etc.). Build against it as-is.

## What is done vs. what remains of Phase 2

Done (this branch): 2.1's generic provider fact + the SUB pilot specialization,
and the `registerWriteLanes` half of 2.2, consumed inside `StepStrong*` only.
**No `equiv_*`/wrapper signature has changed yet and no baseline has shrunk.**

Your task is the remainder, per `docs/refactor/FINAL-PLAN.md` §5.2 and §9
Phase 2 (read the corrected plan, not your memory of it):

1. **Upstream check first (owed from roadmap 2.1 / review gate Q1).** Read
   current upstream `Verified-zkEVM/clean` `Air/Vm.lean` and
   `Air/OrderedChannel.lean` (and PR #398) and determine whether any of the
   provider/lane/pin derivations exist there in reusable form. Write the
   finding down in `docs/refactor/FINAL-PLAN.md` §8 (a short dated note is
   enough): either "adopted upstream lemma X for Y" or "hand-rolled seam
   retained because Z". Do not skip the note.
2. **2.2 remainder — `main_row_pins`.** Derive `MainRowPins` from the Main
   table's constraints at the seam (extend `DerivedRowFacts.lean`), same style
   as `registerWriteLanes`: consequences of `AcceptedZiskTrace` only, no new
   hypotheses.
3. **2.3 — shrink one shape's signatures.** Starting with the R-type family
   (SUB already has its pilot provider fact): remove the binders on the
   `EquivCore`/wrapper (`ZiskFv/Compliance/Wrappers/*`) theorems that are now
   derivable at the seam (`providerTable`, `providerRow`, `h_component`,
   `h_table_spec`, `h_match`, `h_lane_rd`, and any pins covered by
   `main_row_pins`), and feed the derived facts from `StepStrong*` instead.
   The exit criterion is that
   `trust/generated/baseline-wrapper-caller-burden.txt` **shrinks**. Regenerate
   it with the trust-gate tooling; never hand-edit a baseline, and a PR that
   grows any baseline is wrong by definition.
4. **2.4 — roll across the remaining shapes/families**, one family per commit,
   keeping the build green at every commit.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- Everything here is **T0**: `root_soundness` and `root_completeness` must stay
  byte-for-byte identical. `ZiskFv/Audit.lean`'s `#guard_msgs` golden tests are
  the tripwire — **you must not edit that file**; if its tests fail, your
  change altered a root statement or axiom closure and must be reworked.
- Every removed binder must be **proved** from accepted-trace facts, never
  moved into a broader premise, a strengthened validator, or a new
  caller-supplied hypothesis elsewhere.
- No new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`, or ledger/allowlist edits.
- Gates before you claim completion, all green:
  `lake build` (full), `trust/scripts/check-all.sh`,
  `trust/scripts/check-all-semantic.sh`.
- Commit in reviewable per-family chunks with real commit messages. Do not
  amend or rewrite the existing commits on this branch.
- Prepend your run summary to `ARISTOTLE_SUMMARY.md` as usual, and state
  plainly in it which of 2.2/2.3/2.4 you completed and what the caller-burden
  baseline count was before and after.
