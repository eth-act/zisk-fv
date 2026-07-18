# Task: Phase 3 — complete the Clean Arith mirrors; unblock and finish the Arith migration

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work: your T9 turn landed verbatim — the ArithMul/ArithDiv
Interfaces with failed Q2 gates, the bridge relocations, and the BinaryExtension
consistency move).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree; never delete
`.lake` or build artifacts; `lake exe cache get` first if cold. After installing, every
tracked file's content must exactly match the tarball. Your ~22-minute command window:
size build commands to complete within it and re-invoke; a cutoff is never a proof error.
Never commit an attached tarball.

Sandbox limitations, pre-acknowledged: no branch history; no `zisk` submodule → defer
exactly trust check 13. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`,
`flake.lock`, or `ZiskFv/Audit.lean`.

## Context

Your T9 Q2 audits were verified and accepted: the Clean ArithMul/ArithDiv circuits are
incomplete mirrors. Every missing constraint is a named-form mirror of a GENERATED
extraction fact that already exists (the legacy models cite them: e.g.
`main_mul_div_disjoint` ↔ `constraint_2_every_row`, the six mode booleans ↔
`constraint_40–45_every_row`, `bus_res1` ↔ `constraint_46_every_row`; PIL sources under
`zisk/state-machines/arith/pil/arith.pil` are cited in `Airs/Arith/{Mul,Div}.lean`
docstrings). This turn completes the Clean mirrors — adding exactly those generated
constraints, never more — and then finishes the migration your Q2 gates correctly
blocked. Your committed consumer map in `REFACTOR_10_REPORT.md` remains valid.

## Numbered work order

1. **Complete the Clean ArithMul circuit.** Add the missing operations to the ArithMul
   Clean circuit/`Constraints` as `assertZero`s mirroring exactly:
   `constraint_2_every_row` (main_mul/main_div disjointness), `constraint_40–45_every_row`
   (m32/na/nb/nr/np/sext booleans), and `constraint_46_every_row` (`bus_res1` defining equality).
   For each: a docstring citing the extraction fact name AND the arith.pil line (copy
   from the legacy docstrings). Extend `Spec`/`FullSpec` and the soundness derivation;
   extend the row builders (`arithMulRowOf` etc.) so completeness-side constructions
   still hold. Byte-for-byte semantic equality with the legacy predicate — never
   stronger, never weaker.
2. **Complete the Clean ArithDiv circuit.** Same discipline for the ArithDiv audit's
   missing list: mode booleans + disjointness, W-mode high-lane-zero, zero-divisor and
   overflow boundary constraints, scope/disjointness constraints, `constraint_46_every_row`, and
   the inverse-sum zero-divisor constraint — which requires first adding the missing
   witness column (legacy `inv_sum_all_bs`) to `ArithDivRow`/free columns. Every
   addition cites its extraction fact + PIL line. If any audited-missing constraint has
   NO verifiable generated counterpart, do NOT add it — record it precisely in the
   report and leave that part of the legacy model in place.
3. **Re-run both Q2 audits** and update the two `Interface.lean` docstring tables:
   every row previously **missing** must become exact (with the new supply named) or
   carry the item-2 no-counterpart note. The updated audits gate items 4–5.
4. **Migrate the consumers** per your committed `REFACTOR_10_REPORT.md` map (mul, div,
   carry-chain/bus-res, balance/table, exports/wrappers/constructions), committing per
   green group. Retained semantics move into the Clean families as moves, not rewrites.
   Restate record-model hypotheses to Clean-`Spec` facts; Sail-space conclusions and
   `OpEnvelope` arities untouched; zero new caller obligations.
5. **Delete the legacy surfaces** — `Airs/Arith/Mul.lean`, `Div.lean`, `CarryChain.lean`,
   `CarryChainCompleteness.lean`, `BusRes1.lean` — as each reaches reference count 0;
   import updates in the same commit.
6. **Final sweep.** Reference counts before/after; deleted-file list; net line delta;
   `trust/generated/` byte-unchanged; full `lake build`, `trust/scripts/check-all.sh`
   (minus check 13), `trust/scripts/check-all-semantic.sh` all green.

Prioritization: ArithMul completed end-to-end (items 1, 3, 4-mul, 5-Mul) beats both
families half-done. Within ArithDiv, the boundary/inverse-sum work is the deepest —
schedule it after the mechanical booleans.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified
blocker note. A clean build or a committed chunk is a checkpoint, not a stop condition:
after finishing an item, proceed immediately to the next. Committing and reporting with
items silently unattempted is a failed turn. If an item is blocked, skip it, document the
precise blocker (file, theorem, error), and continue. Commit after each green item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` untouched.
- **Mirror-exactness is the license for every added constraint**: each one must cite a
  generated extraction fact (verify the fact exists in the extraction package in your
  build) and the arith.pil source. No constraint without both. This is what makes the
  strengthening constructible — real traces already satisfy the generated constraints.
- **The DIV/REM defect boundary survives unchanged**: `ArithDivDynamicWitnessShape`,
  `h_known_bugs` exclusions, and `Compliance/Defects.lean` semantics stay byte-stable
  except for mechanical retargeting of legacy references during item 4 — and any such
  retargeting must preserve statement meaning exactly. If completing a boundary
  constraint would alter what the defect gate excludes, stop that constraint and report.
- Every restated hypothesis proved from the Clean supply — never weakened, broadened, or
  pushed to callers. Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`,
  `partial`, `@[implemented_by]`. No `trust/generated/` change; no baseline; no
  `OpEnvelope` arity change.
- Work in new commits on top of the provided state; never rewrite or revert it.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` (mirror in `REFACTOR_11_REPORT.md`):
per-item status for 1–6; the updated Q2 tables; per-constraint citation list (extraction
fact + PIL line) for every circuit addition; reference counts before/after; deleted
files; net line delta; exact gate results.
