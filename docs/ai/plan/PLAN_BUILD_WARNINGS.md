# Resolve the in-tree `lake build` warnings

## Context

`lake build` on `main` at `08db1645` is green and emits **955 warnings**. 7 come from pinned
dependencies (Aeneas `sorry`, LeanRV64D deprecations) and we do not own them. The other **948 sit in
55 files under `ZiskFv/`** and are pure Lean 4.28 linter noise: dead `simp` arguments, no-op tactic
steps, `simpa` where `simp` suffices, unnecessary `<;>`, and unused binders. None reports a failed
goal.

Nothing enforces this. There is no `warningAsError`, and no CI job greps a build log for `warning:`.
The work is hygiene: the noise hides any *new* warning a future change introduces.

There is direct precedent. PR #216 (`8d08d05f`, merged 2026-07-01) cleared 245 warnings the same way,
by hand, touching only `ZiskFv/**` and `bin/TrustGate/Main.lean`. It merged without review comment.
The current 948 accumulated after it, mostly in witness files added since.

Outcome: `lake build` reports 0 in-tree warnings, both trust gates still pass 20/20, and no theorem
statement, validator, generated artifact, or trust marker changes.

## The design decision that makes this safe

**Edit by compiler-reported position, never by text search.**

Each warning carries an exact `file:LINE:COL`. `LINE` is 1-indexed; `COL` is a 0-indexed codepoint
offset pointing at the first character of the offending token. Verified against
`ZiskFv/AirsClean/RegisterBoundary.lean:226:51` → `ProvableType.eval_field` and `:288:40` →
`component`.

This matters because the offending idioms are copy-pasted across sibling lemmas and **about half the
sibling copies are live**. Concretely: `(try simp only [bind_ok] at h)` appears 9 times in the
`RawProgramBinding*` family — dead at `RawProgramBindingRegister.lean:313`, `:336` and
`RawProgramBindingLoadStore.lean:301`, `:317`, but doing real work at `Register.lean:237`, `:273`,
`:355` and `LoadStore.lean:352`, `:473`. Any `sed`/regex sweep breaks the live ones. Positional
editing cannot.

The same rule kills a second trap: the linters ignore `norm_num [...]` argument lists entirely.
`sdLdFreeCols` occurs 73 times in `SdLdSpinWitness.lean`, 57 flagged; the 7 unflagged ones at lines
366, 382, 399, 415, 431, 1253, 1268 are all inside `norm_num` lists, so they are *unverified*, not
known-dead. Positional editing never touches them.

## Scope

| Class | Count | PR |
|---|---|---|
| `linter.unusedSimpArgs` | 696 | 1 |
| `linter.unnecessarySimpa` | 51 | 1 |
| `linter.unnecessarySeqFocus` | 28 | 1 |
| `linter.unusedVariables` | 25 | 1 |
| `linter.unusedTactic` | 84 | 2 |
| `linter.unreachableTactic` | 63 | 2 |
| non-terminal `aesop` | 1 | 2 |
| **in scope** | **948** | |
| dependency warnings (Aeneas, LeanRV64D) | 7 | out |

Top 6 files hold 507 of the 696 dead simp arguments:
`ZiskFv/Compliance/SdLdSpinWitness.lean` (197), `ZiskFv/Regression/SignedDivOrdinaryCounterexample.lean`
(77), `ZiskFv/Compliance/DivSpinWitness/Definitions.lean` (77), `ZiskFv/Soundness.lean` (65),
`ZiskFv/Compliance/JalrSpinWitness.lean` (52), `ZiskFv/Compliance/DivSpinWitness/Constraints.lean` (39).

## Safety rules

These come from reading the gates and the prior PR. Every one is a hard rule for both PRs.

1. **Delete only. Never reflow.** `trust/scripts/check-locality.sh:19` matches *indented* lines that
   begin with `axiom`/`opaque`/`constant`/`unsafe def`/`partial def`/`@[extern`/`@[implemented_by`.
   Deletion cannot create such a line; rewrapping a long `simp` list could.
2. **If every argument of one `simp` call is flagged, leave the call untouched** and list it in the
   PR body. PR #216 produced `simp only []` and a bare `] at hacc` this way; those artifacts are
   still on main (`ZiskFv/Compliance/ConstructionDivu.lean:360`,
   `ConstructionDivuw.lean:209`, `ConstructionRemu.lean:337`, `ConstructionRemuw.lean:207`). Do not
   repeat that.
3. **Before each apply pass, re-run the mirror reference-count check.**
   `tools/mirror-roundtrip/survey.py` counts textual mentions of `ZiskFv/AirsClean` mirror
   predicates across `ZiskFv/`, `trust/`, `Tests/`, *including inside proofs*, and
   `check_mirrors.py:1518 unreachable_mirrors()` hard-fails at a count of zero. Deleting the last
   mention of such a name would break `nix run .#test` step 4/10 — which is **not** covered by
   `check-all.sh`. Checked for the current warning set: **0 of the 197 distinct dead argument names
   is a `survey.CLASSIFICATION` declaration**, so the hazard is inert today. It can reappear as the
   fixpoint loop unmasks new names, so re-check every iteration.
4. **Do not touch `ZiskFv/Compliance/RowProvenance.lean`.** `.github/workflows/proofs.yml:392` keys a
   no-prefix-fallback cache on its hash; any byte change forces a cold ~26-file Aeneas recompile. It
   carries no warnings today, so this is a guard, not a task.
5. Unused-variable fixes must rename the *binder and its uses together*. PR #216 hit this: `h_C_lb`
   in `SignedChunkLift.lean` was live only inside an `nlinarith` hint list, which the linter does not
   track.
6. No `set_option linter.… false` is added anywhere.

Confirmed non-issues, so no action is needed for them: no warning-bearing file is
`ZiskFv/Compliance.lean`, a `ZiskFv/Compliance/Dispatch/*` file, or CODEOWNERS-protected, so
`trust/scripts/check-clean-integration.py` (which greps `exact` steps) is untouched. Every trust
baseline under `trust/generated/` keys on statements or is empty, so none can shift.

## PR 1 — mechanical, script-applied (800 warnings)

Branch `chore/warnings-mechanical` off `main`.

**Step 1. Write the fixer** in the scratchpad, uncommitted. Input: a `lake build` log. For each
warning it reads `file:LINE:COL`, and:

- `unusedSimpArgs` — from `COL`, scan forward balancing `[]`/`()`/`⟨⟩` to the next top-level `,` or
  `]`, and delete that span plus one separator. Scanning beats matching the reported name, because a
  complex argument (`show (8192:Nat) = 2^13 by norm_num`, `←foo`) may be pretty-printed rather than
  echoed verbatim.
- `unnecessarySimpa` — two shapes only: `simpa using h` → `simp at h`, and `simpa [args]` → `simp
  [args]`. Anything else is deferred to PR 2.
- `unnecessarySeqFocus` — `<;>` → `;` at the reported column.
- `unusedVariables` — prefix the binder with `_`, and rename its uses in the same declaration.

Apply edits **right-to-left within a line, bottom-to-top within a file**, so earlier offsets stay
valid. Skip any call where all arguments are flagged (rule 2).

**Step 2. Iterate to fixpoint.** Removing an argument can unmask another. Loop: `lake build` →
collect → re-run the rule-3 check → apply → repeat, until the count stops falling. Expect 2–3 passes.

**Step 3. Verify** (see below), then commit and open the PR.

Sequencing note for cost: `ZiskFv/Soundness.lean` has 18 transitive dependents;
`ZiskFv/Compliance/SdLdSpinWitness.lean` has 38 and is *not* a leaf. The union of the reverse closures
of the `Compliance/` set is 374 of 732 modules, so any pass over this file set is effectively a
half-tree rebuild. Batch all edits into one pass rather than rebuilding per file.

## PR 2 — hand-verified tactic deletions (148 warnings)

Branch `chore/warnings-tactics`, stacked on PR 1.

There is **no macro amplification**: all 175 tactic-class warnings sit at 175 distinct source
positions, and the linters skip macro-generated syntax. The 21 `local macro`s in the family
(`reg_op`, `reg_program_decode`, `mext_lemmas`, `branch_program_decode`, …) produce **zero** flagged
warnings. Editing a macro body fixes nothing and risks its call sites — in particular
`RawProgramBindingControl.lean:1955-1962` inside `branch_program_decode` holds a polarity-dependent
`first` whose two rungs each serve 3 of its 6 call sites, and no linter would warn you.

So: 52 edits clear the 127 warnings inside the 10 `RawProgramBinding*` files, and ~48 more sit
outside it (`AddAddiSpinWitness.lean` 8, `JalrSpinRootSoundness.lean` 7, `AddSpinWitness.lean` 6,
`SdLdSpinRootSoundness.lean` 6, `SignedDivOrdinaryCounterexample.lean` 6, `Defects.lean` 3, and
~12 files with 1–2 each).

Work the family in this order, rebuilding the module after each file:

1. Dead `first` rungs (72 warnings, 20 lines, 18 edits). Delete the whole rung including its leading
   `|`, as PR #216 did in `ZiskFv/AirsClean/ArithTableProjections.lean`. Example:
   `RawProgramBindingImmediate.lean:293-302` has 4 rungs and only rung 2 lives.
2. Trailing `all_goals rfl` after a closing `simp only` (26 warnings, 13 edits).
3. Trailing `all_goals exfalso; scalar_tac` (6 warnings, 2 edits) — dead at
   `RawProgramBindingLoadStore.lean:133` and `:357`, **live** at `RawProgramBindingRegister.lean:205`
   and `LoadStore.lean:114`.
4. `(try simp only [bind_ok] at h)` inside `<;>` chains (4 warnings, 4 edits).
5. Remaining `<;>` and misc (19 warnings, 15 edits).

Then the single non-terminal `aesop` at
`ZiskFv/Compliance/TraceLevelExport/RawProgramBitfields.lean:909`. It is inside
`... <;> aesop <;> simp [Nat.shiftRight_eq_div_pow] at *`; `aesop` fails on some branches and the
trailing `simp` closes them. Drop `aesop` from the chain and confirm the proof still closes.

## Verification

Per PR, in order:

```bash
lake build                              # 0 errors; warning count at the expected floor
trust/scripts/check-all.sh              # expect 20/20
trust/scripts/check-all-semantic.sh     # expect 20/20 (needs oleans, so run after lake build)
python3 tools/mirror-roundtrip/check_mirrors.py   # guards rule 3; not covered by check-all.sh
```

Count the remaining warnings with the same parse used for triage — group `warning:` blocks by the
`linter.<name>` in each block's trailing `Note:` line — and state the before/after per class in the
PR body.

Expected floors: after PR 1, 148 in-tree warnings remain (the PR 2 set) plus any call skipped by
rule 2. After PR 2, 0 in-tree warnings; the 7 dependency warnings remain and are out of scope.

Both PRs must show `git diff --stat` touching only `.lean` files under `ZiskFv/`, and
`git diff` containing no `set_option`, no `axiom`/`opaque`/`sorry`, and no change to any line that is
part of a theorem statement.
