# Task: Phase 3 — upgrade the ArithDiv witness contract to mainComplete; discharge the Div wrapper obligations

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: T12 landed verbatim — the 12 mode-boolean conjuncts are
gone, `ArithMulTableWitness.row_constraints` discharges the Mul wrappers, and your
verified ArithDiv blocker note is accepted as this turn's work order).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

Your T12 audit verified: `ArithDivTableWitness` still carries `mainWithArithTable`
soundness, and the Div `FullSpec` omits C46 and the appended local constraints — so the
16 Div-side wrapper obligations cannot honestly discharge yet. The Mul side shows the
exact finished shape: witness field carries `mainComplete` soundness; the constructor
(`arithMulTableWitness_of_fullSpec`) proves the appended constraints at construction;
consumers project down via `base_soundness_of_complete_const_soundness`; and
`ArithMulTableWitness.row_constraints` hands wrappers the legacy bundle with zero caller
premises. This turn replicates that for Div. Div's appended constraints include
chunk-dependent facts (boundary, inverse-sum, W-mode) that CANNOT come from static table
membership alone — they must flow from where the witness is actually constructed, i.e.
the live provider row's `constraints_hold` in the balance/table layer.

## Numbered work order

1. **Audit the Div witness construction path.** Enumerate every site that constructs an
   `ArithDivTableWitness` (or the `FullSpec` it is built from) — expected in
   `AirsClean/ArithTableProjections.lean`, the `FullEnsemble/Balance/*` layer, and
   construction modules. For each, identify the live source that already carries the
   appended-constraint facts (`mainComplete` soundness of the selected provider row).
   Commit the map to `REFACTOR_14_REPORT.md` before changing anything.
2. **Upgrade the contract.** Change `ArithDivTableWitness.holds` to
   `ConstraintsHold.Soundness … (mainComplete …)`, extend the Div `FullSpec` (or the
   constructor inputs) so construction sites prove the appended constraints from their
   live source — never as new caller premises at public surfaces. Keep every existing
   consumer green via `base_soundness_of_complete_const_soundness` exactly as the Mul
   side does. If a construction site's live source genuinely lacks a needed fact, STOP
   that site and report it precisely — do not add a caller-supplied hypothesis.
3. **Discharge the 16 Div wrapper obligations.** Add
   `ArithDivTableWitness.row_constraints` (and boundary/inverse/scope/W-mode projection
   variants as consumers need them) mirroring the Mul method, then remove the
   caller-supplied row-constraint obligations from the Div-family forwarding wrappers
   (`Div`, `Divu`, `Divw`, `Divuw`, `Rem`, `Remu`, `Remw`, `Remuw` surfaces).
   Per-wrapper before/after obligation counts in the report.
4. **Final sweep.** Remaining caller-supplied Arith constraint hypotheses (target: only
   the five `Equivalence/`-frozen compatibility binders, which are OWNER-GATED — do not
   touch `Equivalence/`); net line delta; `trust/generated/` byte-unchanged; full
   `lake build`, `trust/scripts/check-all.sh` (minus check 13),
   `trust/scripts/check-all-semantic.sh` all green.

Prioritization: item 2 done cleanly for the witness contract beats a partial item 3 —
the contract upgrade is the enabling move and must not be rushed into caller premises.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- **`Compliance/Defects.lean` and `Equivalence/` byte-unchanged** — the DIV/REM defect
  boundary and the public per-opcode theorem signatures are exempt/owner-gated.
- The constraint set stays frozen at the T10 audited list. Strengthened contracts must
  be proved at construction from live sources; a deleted obligation must be DERIVED, not
  renamed, weakened, or moved to a different caller.
- Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`. No `trust/generated/` change; no baseline; no `OpEnvelope` arity
  change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_14_REPORT.md`):
per-item status for 1–4; the construction-site map; per-wrapper before/after obligation
counts; net line delta; exact gate results.
