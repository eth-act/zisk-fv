# 03 — Root theorem API redesign

Goal: an auditor should be able to open **one file**, read the soundness
statement and the completeness statement, and from their *types alone* enumerate
the entire trusted premise set and every in-scope exclusion — without chasing
into `OpEnvelope` fields, `Promises` bundles, or trust `.txt` ledgers.

The Lean below is **illustrative sketch**, not compiled code. It uses existing
names where known and marks new names as `-- NEW`.

## 3.1 Principle: the statement is the audit surface

Three rules for both roots:

1. **One endpoint per axis.** Exactly one advertised `root_soundness` and one
   `root_completeness`. Any other top-level theorem (notably the current
   `zisk_riscv_compliant_program_bus`) is renamed to make it clearly internal
   (e.g. `perArm_channel_balance`) and documented as "consumed by
   `root_soundness`, not a public endpoint".
2. **Every trusted premise is a named binder of the endpoint.** No *trust* may
   hide inside a value the proof constructs internally. **Correction (verified):**
   `aeneasBridgeTrust` and `memoryTimelineConstructionEvidence` are *not* such
   hidden trust. They are hypotheses of the *internal* theorem
   `zisk_riscv_compliant_program_bus`, and the `StepStrong*` trace-export steps
   **discharge** them when constructing each `OpEnvelope` arm (e.g.
   `StepStrongAluArith.lean:223` proves `env.aeneasBridgeTrust` from derived
   accepted-trace row facts; `memoryTimelineConstructionEvidence` is `trivial` on
   non-load arms and `bootSeed`-derived on load arms). The frozen
   `#print axioms root_soundness` in `ZiskFv/Audit.lean` confirms no unproven
   premise hides there. So do **not** lift them into `root_soundness` binders —
   that would re-introduce discharged premises and *weaken* the theorem. This
   rule therefore only requires bundling the trust binders `root_soundness`
   *already* has (`inputsAgree`, `bootSeed`).
3. **Every scope exclusion is a named binder too.** The defect carve-out
   (`hAvoidKnownBugs`/`RowOutsideDefectRegion`) and any out-of-scope predicate
   must appear in the type, keyed to `trust/defects.md`.

## 3.2 A single trust-surface record

Collect the trusted premises into one record so the TCB is one type. This is the
central API move for explicitness.

```lean
-- NEW, e.g. ZiskFv/Compliance/TrustSurface.lean
namespace ZiskFv.Compliance

/-- The complete external-trust surface of `root_soundness`, in one place.
    Anything an auditor must *believe* (not *check*) lives here. Each field is
    cross-referenced to `trust/trusted-base.md`. -/
structure SoundnessTrust (numInstructions : Nat)
    (zisk : AcceptedZiskTrace numInstructions)
    (sail : SailTrace numInstructions)
    (step : ∀ i, ZiskStep zisk i) : Prop where
  /-- single cross-segment initial-memory seed (#115/#119). -/
  bootSeed           : BootSegmentMemorySeed zisk sail step
  /-- ZisK inputs = Sail model inputs at each step. -/
  inputsAgree        : ∀ i, InputsAgree zisk sail i (step i)
  -- NOTE: `channelsBalanced` is NOT a field here — it is already carried inside
  -- `AcceptedZiskTrace` (the logUp/permutation proof-system trust). And there is
  -- deliberately NO `aeneasBridge` field: the Aeneas row-lowering facts are
  -- *discharged* for `root_soundness` (see §3.1 rule 2), not trusted, so adding
  -- them here would re-introduce a proven premise and weaken the theorem.

/-- The complete *scope* surface: what the theorem does NOT claim. -/
structure SoundnessScope (numInstructions : Nat)
    (zisk : AcceptedZiskTrace numInstructions)
    (step : ∀ i, ZiskStep zisk i) : Prop where
  /-- excludes the enumerated forge defects in `trust/defects.md`. -/
  outsideDefects : ∀ i, RowOutsideDefectRegion zisk i (step i)

end ZiskFv.Compliance
```

Then the endpoint reads:

```lean
-- ZiskFv/Soundness.lean  (redesigned)
theorem root_soundness
    {numInstructions : Nat}
    (zisk : AcceptedZiskTrace numInstructions)
    (sail : SailTrace numInstructions)
    (step : ∀ i, ZiskStep zisk i)
    (decode : ∀ i, ProgramDecode zisk i (step i))
    (trust : SoundnessTrust numInstructions zisk sail step)   -- ← all trust, one binder
    (scope : SoundnessScope numInstructions zisk step) :       -- ← all exclusions, one binder
    ∀ i, StepSound zisk sail i (step i)
```

Benefits:
- The entire TCB is `SoundnessTrust`'s fields (`bootSeed`, `inputsAgree`), the
  proof-system trust already inside `AcceptedZiskTrace` (`channels_balanced`),
  plus the two extraction assumptions named in `trusted-base.md` (Sail→Lean,
  ZisK→Lean). A short list, enumerable from one `structure` and one type.
- This is a pure re-package of *existing* binders (T1). It does **not** make
  `aeneasBridge` or a memory-timeline residual a trusted premise — those are
  proven for `root_soundness`, so they stay discharged, not lifted.
- `#print axioms root_soundness` remains the machine check; the human check is now
  "read `SoundnessTrust` and `SoundnessScope`".
- Adding/removing a trust item is a one-line record edit that shows up in every
  downstream `git diff` — exactly what the existing trust-gate baselines want to
  police, but now enforced by the type rather than by `.txt` files.

## 3.3 Demote the old global theorem to an internal per-arm lemma

`zisk_riscv_compliant_program_bus` is not a second public claim; it is the
per-arm engine. Rename and relocate:

```lean
-- internal, e.g. namespace ZiskFv.Compliance.Internal
theorem perArm_channel_balance
    (env : OpEnvelope state m r_main)
    (trust : OpEnvelope.LocalTrust env)     -- bridge + memory-construction, bundled
    (scope : Defects.NoKnownDefect env) :
    env.channelBalanceConclusion
```

with `env.channelBalanceConclusion` a **dependent match** (see D3 in `02`)
returning the single real `= state_effect_via_channels …` for that arm, instead
of a 12-way `True`-padded conjunction:

```lean
def OpEnvelope.channelBalanceConclusion : OpEnvelope state m r_main → Prop
  | .add   d => execute_instruction (.RTYPE (…, rop.ADD)) state = state_effect_via_channels … state
  | .beq   d => …
  | …
```

`root_soundness`'s `StepStrong*` steps then call `perArm_channel_balance`, and
the `trust`/`scope` those steps need are *projected from* the top-level `trust :
SoundnessTrust` and `scope : SoundnessScope` — so nothing new is trusted at the
per-step layer. README/AGENTS/`trusted-base.md` all point at `root_soundness`;
`perArm_channel_balance` is documented as internal.

## 3.4 `root_completeness`: give it the same shape

Today completeness is `ZiskFv/Completeness.lean`:
`skeletal_root_completeness` (conditional on five `OutstandingZiskPredicates`
obligations) plus `sail_executable_within_supported_decode_shape` (proven). The
skeleton design — ingredients (`OutstandingZiskPredicates`) vs relations (the
five obligations) vs the goal (`EventualCompleteness`) — is already the *most
readable part of the codebase* and should be the template for soundness, not the
other way round.

Two API changes to finish the symmetry:

1. **Rename `skeletal_root_completeness → root_completeness`** and keep the five
   obligations as one record (mirroring `SoundnessTrust`):

   ```lean
   -- NEW: the completeness analogue of SoundnessTrust
   structure ZiskCompletenessObligations (z : OutstandingZiskPredicates) : Prop where
     decoderAcceptsInShape : z.decoderAcceptsInShape
     loweringTotal         : z.loweringTotal
     rowTotal              : z.rowTotal
     opcodeTotal           : z.opcodeTotal
     soundnessContract     : z.soundnessContract

   theorem root_completeness
       (state : SailState) (sailIsa : IsaExtensionsEnabled state)
       (z : OutstandingZiskPredicates)
       (obligations : ZiskCompletenessObligations z) :
       EventualCompleteness state z
   ```

   Now soundness and completeness are visibly dual: each has a state/trace
   object, a single "what we assume" record, and a one-line conclusion.

2. **State the honest ⇒ obligations discharge as its own theorem** so the reader
   sees where the obligations are meant to come from (the Aeneas workspace,
   tracked in the issues cited in `Completeness.lean`). Until that bridge lands,
   `root_completeness` stays conditional on `ZiskCompletenessObligations` — which
   is honest and, with the record, obvious from the type.

Keep the unconditional, proven `sail_executable_within_supported_decode_shape`
exactly as is (it is the one real completeness content in-build), but present it
under the `root_completeness` file so the two live together.

## 3.5 One audit file

Create a single `ZiskFv/Audit.lean` (or a `docs/AUDIT.md` generated from it) that
imports and *re-states nothing new* but gathers, in reading order:

- `root_soundness` with its `SoundnessTrust` / `SoundnessScope`;
- `root_completeness` with its `ZiskCompletenessObligations`;
- `sail_executable_within_supported_decode_shape` (proven);
- a `#print axioms root_soundness` / `#print axioms root_completeness` block (as
  `#guard_msgs` if you want it gate-checked);
- pointers to `trust/trusted-base.md` and `trust/defects.md`.

This file *is* the audit surface. Everything else is implementation.

## 3.6 What this fixes, mapped to the request

| Request | This section |
| --- | --- |
| "maximum explicitness and readability" of top theorems | 3.2 (trust record), 3.4 (completeness symmetry), 3.5 (one audit file) |
| single, honest TCB | 3.2 (trust visible as binders), 3.3 (no second public claim) |
| soundness ≈ completeness in shape | 3.4 |
| don't launder trust | every premise is a binder; `perArm` projects from the top trust, adds nothing |
