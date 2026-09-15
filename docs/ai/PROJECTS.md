# Projects

Index of active plans. One section per plan; a section titled `Foo` maps to
`docs/ai/plan/PLAN_FOO.md`. Inactive plans move to `docs/ai/plan/archive/` and to the
Archived section at the bottom.

## Extraction Fidelity

Plan: `docs/ai/plan/PLAN_EXTRACTION_FIDELITY.md`. A 52-round adversarial mutation sweep
(`docs/adversarial-mutation-sweep.md`, branch `adversarial-mutation-sweep`, commit `019eec25`)
broke one ZisK constraint at a time, re-extracted, and rebuilt: 24 of 35 valid mutations were
caught and 11 were missed, which measures **167 of 355 extracted constraints as unchecked against
the model** — almost all of them the stage-2 bus tuples, since `root_soundness` is stated over a
hand-written transcription that only the row-algebra layer welds. The route is to generate the
model's `Row.lean` / `Constraints.lean` from the pilout with `pil-extract clean-component`, which
already exists, already emits 6 of 10 AIRs, and is wired into no pipeline, falling back to
hand-written `ValidatedLink` ties only where the emitter cannot reach. Tracked at umbrella #368
with children #369-#376; 16 workstreams ordered smallest to largest, except that the
mutation-sweep harness and exposure ledger (#369) land first because they are the measuring
instrument.

## Build Warnings

Plan: `docs/ai/plan/PLAN_BUILD_WARNINGS.md`. `lake build` on `main` at `08db1645` emitted 955
warnings, 948 of them Lean 4.28 linter noise in 55 files under `ZiskFv/`. Two stacked PRs cleared
them: #361 applied the four script-fixable classes positionally (948 -> 137) and #362 deleted the
dead tactic steps by hand (137 -> 1). The one survivor is a linter false positive at
`ZiskFv/AirsClean/MemAlign/Circuit.lean:258`; keeping the count at 1 is now #364.

## InputsAgreeCore 360

Plan: `docs/ai/plan/PLAN_INPUTSAGREECORE_360.md`. Removes the `InputsAgreeCore` premise from
`root_soundness` by discharging it rather than restating it, tracked at #360.

## Project Closeout

Plan: `docs/ai/plan/PLAN_PROJECT_CLOSEOUT.md`. The mvp-milestone closeout under the owner ruling
of 2026-07-13, "go for completeness — no punting"; supersedes `PLAN_FANOUT_CLOSEOUT.md`. Large and
long-running; read its own status section rather than this entry.

## Archived

See `docs/ai/plan/archive/` for superseded and completed plans, including
`PLAN_S3_LOOKUP_WIRING.md` — the plan that built the `ValidatedLink` machinery the Extraction
Fidelity work consumes — and the earlier `PROJECTS.md` index.
