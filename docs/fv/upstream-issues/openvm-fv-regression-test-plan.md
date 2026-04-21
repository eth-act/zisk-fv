# openvm-fv regression test against `codygunton/sail-riscv-lean` fork

**Purpose.** Verify that proposed simp-lemma additions to
`NethermindEth/sail-riscv-lean` (via `codygunton/sail-riscv-lean`
private fork) don't break Nethermind's `openvm-fv` formal verification
of OpenVM.

**Share this document with a fresh Claude Code session whose working
directory is `/home/cody/openvm-fv` (read-only symlink from zisk-fv
exists at `/home/cody/zisk-fv/openvm-fv`).**

---

## Context (for the test agent)

- `openvm-fv` is Nethermind + OpenLabs's 45-RV32IM-opcode Lean
  verification of the OpenVM zkVM. Its build pins
  `sail-riscv-lean` at `rev = "rv32d"` and imports `LeanRV32D`.
- A downstream project (`zisk-fv`) is proposing to add a new file
  `LeanRV64D/Lemmas.lean` upstream for reusable
  `currentlyEnabled` / `hartSupports` simp reductions under fixed ISA
  profile hypotheses. Rationale: `currentlyEnabled` has ~2000 call
  sites in the generated `LeanRV64D`; every downstream verifier
  duplicates the plumbing.
- **The proposed change is additive: a new file in `LeanRV64D/` only.**
  It does not modify `currentlyEnabled`, does not retag existing
  declarations `@[simp]`, does not change types. By construction no
  consumer that doesn't `import LeanRV64D.Lemmas` can observe any
  difference.
- **openvm-fv uses `LeanRV32D`, not `LeanRV64D`.** The proposed change
  is therefore invisible to openvm-fv's proofs by file layout. This
  test confirms that.

## Fork & branch under test

| Repo | URL |
|---|---|
| Private fork | https://github.com/codygunton/sail-riscv-lean |
| Branches present | `main`, `rv32d`, `ext-zca-simp-lemmas` |
| Branch with proposed change | `ext-zca-simp-lemmas` (branched off `main`, adds `LeanRV64D/Lemmas.lean` + `UPSTREAM_PROPOSAL.md`) |
| Fork fidelity caveat | `.github/workflows/` was removed on both `main` and `rv32d` due to OAuth-scope limitations on the mirror push. All Lean code, `lakefile.toml`, and `lean-toolchain` are byte-identical to upstream. |

## Test protocol

### Step 1 — Baseline build

From `/home/cody/openvm-fv`, confirm the current build is green against
upstream `NethermindEth/sail-riscv-lean@rv32d`.

```bash
cd /home/cody/openvm-fv
lake exe cache get  # populate mathlib cache if fresh
time lake build 2>&1 | tee /tmp/openvm-fv-baseline.log
git log -1 --oneline  # record openvm-fv HEAD for the report
```

Record: build status (green / red), total wall time, counts of
`warning:` and `sorry` lines in the log.

### Step 2 — Point `lakefile.toml` at the fork's `rv32d` branch

Edit `/home/cody/openvm-fv/lakefile.toml` and change the
`sail-riscv-lean` (or equivalent — the dep might be named `LeanRV` or
`sail_riscv_lean`; find it by grepping for `sail-riscv-lean`) block:

```diff
 [[require]]
 name = "LeanRV"
-git = "https://github.com/NethermindEth/sail-riscv-lean"
+git = "https://github.com/codygunton/sail-riscv-lean"
 rev = "rv32d"
```

Then:

```bash
lake update LeanRV   # or whatever dep name resolved
time lake build 2>&1 | tee /tmp/openvm-fv-forkrv32d.log
```

**Expected:** green, zero delta in warnings/sorries vs. baseline,
timing within noise. This verifies the fork's `rv32d` branch is
byte-equivalent to upstream (modulo the stripped workflows, which
aren't Lean-visible).

If this build regresses, STOP and report — something's wrong with the
fork's `rv32d` branch (e.g., the workflow-strip commit somehow picked
up spurious changes). Revert the `lakefile.toml` and report findings.

### Step 3 — Point `lakefile.toml` at the proposed-change branch

Change only the `rev`:

```diff
-rev = "rv32d"
+rev = "ext-zca-simp-lemmas"
```

Note: `ext-zca-simp-lemmas` is branched off `main` (the RV64 branch),
**not** off `rv32d`. Pointing a LeanRV32D consumer at this branch
will cause the build to fail (the rv32d sources aren't present on this
branch — only the RV64 ones).

**This is the load-bearing signal:** if openvm-fv's build errors are
exclusively about missing `LeanRV32D` modules, that confirms the
branch is RV64-only and cannot affect `rv32d`-pinning consumers even
by accident. Revert the `lakefile.toml` once confirmed.

If the build fails for any *other* reason — e.g., unexpected conflicts
with files `openvm-fv` transitively depends on — report the errors. Do
not try to fix them. The upstream proposal needs re-scoping if that
happens.

### Step 4 (optional, aspirational) — RV32D mirror

If/when a follow-up branch `ext-zca-simp-lemmas-rv32d` is created on
the fork (mirroring the proposed lemmas into the `rv32d` branch), the
test agent should re-run Step 2 against that branch and compare to
the Step 1 baseline.

For the current scaffolding commit, this branch does not exist yet.
Mark Step 4 as "not applicable at this time" in the report.

## Report format

Return a single markdown block with:

```markdown
## Test report — codygunton/sail-riscv-lean regression against openvm-fv

| Step | Branch | Status | Wall time | Warnings | Sorries | Notes |
|---|---|---|---|---|---|---|
| 1 Baseline | NethermindEth@rv32d | green / red | <s> | N | N | openvm-fv HEAD = <sha> |
| 2 Fork@rv32d | codygunton@rv32d | green / red | <s> | N | N | delta vs. baseline: ... |
| 3 Fork@ext-zca-simp-lemmas | codygunton@ext-zca-simp-lemmas | expected: build error about missing LeanRV32D | — | — | — | confirms branch invisible to RV32-pinning consumers |
| 4 RV32D mirror | — | N/A (branch not created yet) | — | — | — | — |

## Conclusion

- Regression risk to openvm-fv from the scaffolding commit: [none /
  some — describe].
- Green-light the upstream `LeanRV64D/Lemmas.lean` addition? [yes /
  yes with caveat / no — describe].
- Any recommendations for the upstream PR framing?
```

## Cleanup (mandatory — do this after reporting)

Revert `lakefile.toml` to its baseline (upstream) state:

```bash
cd /home/cody/openvm-fv
git checkout -- lakefile.toml lake-manifest.json
lake update LeanRV
```

Verify `lake build` still green against upstream before ending the
session. Do **not** commit the lakefile edits or push anything to
openvm-fv — the fork switch is a local test only.

## Non-goals (do NOT do these)

- Do not modify anything under `/home/cody/zisk-fv/` (the driver
  project).
- Do not file a PR to upstream `NethermindEth/sail-riscv-lean` from
  this test session — that's the owner's call, pending this test's
  results.
- Do not attempt to populate `LeanRV64D/Lemmas.lean` with actual
  lemmas — that's separate work, not part of the regression test.
- Do not change visibility of the private fork or otherwise alter
  `codygunton/sail-riscv-lean`.
