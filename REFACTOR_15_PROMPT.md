# Task: Phase 3 — complete the LIVE shared Arith provider; then the Div contract upgrade your R14 audit unblocked

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work, including your R14 blocker audit — accepted in full; this
work order is the remediation you named in `REFACTOR_14_REPORT.md`).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

Your R14 audit established: the live ensemble validates the shared
`ArithMul.componentWithArithTable` provider; `ArithMulRow` lacks the Arith AIR's
`inv_sum_all_bs` column (stage-1 col 38); `vOfDivuRow` zeroes it, so
`ArithDiv.mainComplete`'s inverse-sum equation is false on ordinary nonzero DIV/REM
rows. The remediation you named is this turn: make the ONE physical Arith AIR's full
generated local-constraint set live in the shared provider, with real witness values,
then complete the contract upgrade and wrapper discharge that R14 correctly refused.

The license is unchanged: every constraint involved is an already-audited generated
mirror (the T10/R11 cited list — nothing new, nothing dropped). The witnesses are the
constructibility proof: real AIR rows satisfy all generated constraints, so every
concrete witness row must be repairable with REAL values, never with weakened
constraints.

## Numbered work order

1. **Constructibility precheck (audit before code).** Enumerate every concrete row that
   instantiates the shared Arith provider (the Construction* modules' rows — divu/
   divuw/remu/remuw AND the mul/mulw/mulhu families — plus any spin-witness or fixture
   rows). For each, check it against each constraint the completed circuit will add
   (Div block: booleans/disjointness, boundary 9–24, inverse-sum 25, scope 26–30,
   mode 39–45, c46, W-mode 47–48). Record per-row: already-satisfied / needs a real
   value fix (say which — e.g. the actual divisor-chunk-sum inverse on active DIV rows;
   `inv_sum_all_bs = 0` is correct only where `div = div_by_zero`) / genuinely
   unsatisfiable (STOP that row and report — that would be a model finding). Commit the
   table to `REFACTOR_15_REPORT.md` before changing proof code.
2. **Complete the shared row and circuit.** Add `inv_sum_all_bs` to `ArithMulRow`
   (docstring: Arith AIR stage-1 col 38, used by `constraint_25_every_row`,
   `arith.pil:143`) with mechanical propagation (FreeCols, builders, `constVar`,
   adapters). Extend the shared complete circuit so its appended operations carry the
   FULL audited generated local-constraint set of the Arith AIR (dedupe against what
   `ArithMul.mainComplete` already appends; every `assertZero` cited: extraction fact +
   arith.pil line). `ArithDiv`'s family mirror may then re-export or alias rather than
   duplicate.
3. **Swap the live provider.** Point `arithMulProviderComponent`
   (`FullEnsemble/Balance/Classification.lean`, definitionally
   `componentWithArithTable`) and the ensemble at the completed circuit. Repair every
   item-1 row with its real values; update `vOfDivuRow` to project the now-present
   column instead of fabricating 0; update `FullSpec`/
   `arithMul_fullSpec_of_component_spec` and consumers, keeping everything green via
   `base_soundness`-style projections. No caller-supplied premise may appear anywhere
   in this — the facts flow from the live table's `constraints_hold`.
4. **The R14-blocked upgrade, now honest.** Upgrade `ArithDivTableWitness.holds` to the
   completed supply; extend `arithDivTableWitness_of_fullSpec` and its four
   `StepStrongLoadMext` call sites; add `ArithDivTableWitness.row_constraints` (+
   boundary/inverse/scope/W-mode projections as needed) mirroring the Mul method; then
   remove the 16 Div-family wrapper row-bundle obligations. Per-wrapper before/after
   counts.
5. **Final sweep.** Remaining caller-supplied Arith constraint hypotheses (target: only
   the five owner-gated `Equivalence/` compatibility binders); net line delta;
   `trust/generated/` byte-unchanged; full `lake build`, `trust/scripts/check-all.sh`
   (minus check 13), `trust/scripts/check-all-semantic.sh` all green.

Prioritization: items 2–3 landed clean and green beat a rushed item 4 — the provider
swap is the load-bearing move; a single unsatisfiable witness row stops that row's
repair, not the whole swap, unless it indicates a genuine model defect (then STOP and
report). If the budget runs short, the precheck table plus a green partial swap is a
good turn.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- **`Compliance/Defects.lean` and `Equivalence/` byte-unchanged** (defect boundary and
  public per-opcode signatures are exempt/owner-gated).
- The constraint set stays FROZEN at the audited generated list — the completed circuit
  adds exactly the cited mirrors, nothing else; witness repairs use real values only.
  A row that cannot be honestly repaired is a reported finding, never a reason to
  weaken, special-case, or drop a constraint.
- Every removed obligation DERIVED from the live supply; zero new `axiom`, `sorry`,
  `admit`, `native_decide`, `opaque`, `partial`, `@[implemented_by]`. No
  `trust/generated/` change; no baseline; no `OpEnvelope` arity change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_15_REPORT.md`):
per-item status for 1–5; the precheck table; the per-row repair list with the real
values used; per-wrapper before/after counts; net line delta; exact gate results.
