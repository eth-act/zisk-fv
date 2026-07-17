# Task: Phase 3 pilot completion — rewire BinaryAdd consumers, delete the bridge

## Situation

**The tree delivered with this prompt is the authoritative source of truth** (it integrates
all of your prior accepted work, including your `AirsClean/BinaryAdd/Interface.lean`, which
the operator verified locally: the module and its full import closure build green).

Install it NON-DESTRUCTIVELY: extract the tarball OVER your existing tree. Do NOT delete
`.lake` or any build artifacts — Lake is content-addressed, so unchanged files keep their
cache and only real deltas rebuild. If your build is cold anyway, run `lake exe cache get`
first (mathlib artifacts). After installing, every tracked file's content must exactly
match the tarball.

Your command window is ~22 minutes and build progress persists across invocations: size
every build command to complete within it (per-module or per-directory slices for
deep-import work), and simply re-invoke; never treat a window cutoff as a proof error.

Sandbox limitations, pre-acknowledged: no git branch history; no `zisk` submodule, so
trust check 13 cannot run for you — defer exactly that check, every other gate is
mandatory. Do not touch `lakefile.toml`, `lake-manifest.json`, `flake.nix`, `flake.lock`,
or `ZiskFv/Audit.lean`.

## Context

Your previous turn wrote `Interface.lean` and found (mid-task report) that the four legacy
`Valid_BinaryAdd` predicates correspond to the four Clean assertions up to notation. The
turn was cancelled before the consumer rewiring; the tree you receive contains the
verified interface, still outside the root import graph because its
`BinaryAdd.opBusMessage` intentionally collides with `Bridge.lean`'s until the bridge is
deleted. This turn completes the pilot: items 3–6 of the previous work order.

## Numbered work order

1. **Write the Q2 correspondence report.** Commit the per-constraint correspondence table
   (legacy predicate ↔ Clean assertion, plus where the extra Clean range lookups and
   op-bus push live on the legacy side) as a comment block in `Interface.lean`'s module
   docstring, and reproduce it in your run summary. If completing the table exposes any
   real divergence: stop the deletion items immediately and report it precisely.
2. **Rewire the BinaryAdd-family consumers** of `Valid_BinaryAdd`/`Bridge.lean`
   (EquivCore bridge lemmas, the `add_via_binaryadd` route, construction/StepStrong
   feeds) onto `Interface.lean`'s API (`ComponentSpecFacts`,
   `binary_add_chunks_eq_bv_add*`, the op-bus projection). You MAY restate EquivCore
   hypotheses from record-model facts to Clean-`Spec` facts; the Sail-space
   `execute = bus_effect` conclusion shapes and promise discipline must be preserved; no
   hypothesis weakened or added. No `OpEnvelope` constructor-arity changes.
3. **Delete `ZiskFv/AirsClean/BinaryAdd/Bridge.lean`** once consumer-free, and add
   `import ZiskFv.AirsClean.BinaryAdd.Interface` to `ZiskFv.lean` in the same commit —
   this resolves the intentional `opBusMessage` collision atomically.
4. **Delete `Valid_BinaryAdd`** (definition + its `Airs/` constraint predicates) if and
   only if consumer-free after items 2–3; otherwise report the remaining consumer list
   verbatim.
5. **Final sweep.** `Valid_BinaryAdd` consumer count before/after; bridge status;
   `trust/generated/` byte-for-byte unchanged; full `lake build`,
   `trust/scripts/check-all.sh` (minus check 13), `trust/scripts/check-all-semantic.sh`
   all green.

## Completion contract

The turn is complete when every numbered item is either done or carries a verified blocker
note. A clean build or a committed chunk is a checkpoint, not a stop condition: after
finishing an item, proceed immediately to the next. Committing and reporting with items
silently unattempted is a failed turn. If an item is blocked, skip it, document the precise
blocker (file, theorem, error), and continue with the next item.

## Hard constraints (in addition to `AGENTS.md`, which fully applies)

- T0 at the roots: `root_soundness` and `root_completeness` byte-for-byte identical;
  `ZiskFv/Audit.lean` — you may add exactly the one import line to `ZiskFv.lean` named in
  item 3, nothing else in that file; `Audit.lean` itself untouched.
- Item 1's outcome gates items 3–4: no deletion is sound unless the constraint sets agree
  exactly.
- Every rewired hypothesis must be proved from the Clean `Spec`/accepted-trace supply —
  never weakened, moved to a broader premise, or replaced by a new caller obligation.
  Zero new `axiom`, `sorry`, `admit`, `native_decide`, `opaque`, `partial`,
  `@[implemented_by]`. No file under `trust/generated/` may change; no baseline created.
- Work in new commits on top of the provided state; never rewrite or revert it. Commit
  after each green item so cancellations lose nothing.

## Reporting contract

Prepend your run summary to `ARISTOTLE_SUMMARY.md` with: the per-item status table for
items 1–5; the Q2 correspondence table; the consumer count before/after with any
remaining-consumer list; and exact gate results.
