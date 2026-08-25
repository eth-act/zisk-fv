# 02 — Clean idioms, and how the project uses them

North star: upstream `Verified-zkEVM/clean` conventions. The project pins a fork
(`codygunton/clean`) whose only intentional divergence is documented in
`docs/clean-fork-divergences.md` (the additive `Air.Flat.Component.transition`
field for Main's cross-row PC handshake); everything else should match upstream.

## 2.1 The upstream idioms (what "idiomatic Clean" means)

### Circuit definition
- **`ProvableType` / `ProvableStruct`.** Row/IO types are `structure`s deriving
  `ProvableStruct`, so Clean can `eval` them from an environment and treat them
  as `Var`s. (`Clean/Circuit/Provable.lean`.)
- **`main : Var Input F → Circuit F Output`.** The circuit is a monadic
  do-block emitting `assertZero`, `lookup`, and channel `push`/`pull`
  operations. (`Clean/Circuit/Basic.lean`, `Operations.lean`.)
- **`ElaboratedCircuit`.** Bundles `main` with `localLength`, `output`, and the
  channel metadata (`channelsWithRequirements`, `exposedChannels`,
  `channelsLawful`). The `circuit_norm` simp set is designed to unfold these.

### Circuit correctness (the black-box contract)
- **`FormalCircuit`** = `ElaboratedCircuit` + `Assumptions`, `Spec`, and proofs
  of `Soundness` (`assumptions ∧ constraints → spec`) and `Completeness`
  (`assumptions → constraints`). Soundness + completeness together mean the
  circuit behaves like a function with `Assumptions` as precondition and `Spec`
  as postcondition.
- **`GeneralFormalCircuit`** for mixed assertion/function circuits: decouples the
  soundness statement (`Assumptions`/`Spec`) from the completeness statement
  (`ProverAssumptions`/`ProverSpec`). This is the right tool when a circuit
  *enforces* a range as a side effect (soundness shouldn't assume it, but
  completeness needs it).
- **`FormalAssertion`** for pure assertions (unit output, weaker completeness).
- **`DeterministicFormalCircuit`** adds output uniqueness.
- Proof ergonomics: **`circuit_proof_start`**, then `simp only [circuit_norm, …]`
  unfolding sub-gadgets until only the math remains, closing with
  `omega`/`ring`/`simp_all`. Add local simp lemmas to `@[circuit_norm]`, **not**
  `@[simp]`. (`doc/proving-guide.md`, `doc/conventions.md`.)

### AIR / ensemble layer (`Clean/Air`)
- **`Air.Flat.Component`** — a one-row AIR component backed by a
  `GeneralFormalCircuit`. No adjacent-row constraints; cross-row/-component
  structure is expressed *only* through **channels**.
- **`Air.Flat.Table` / `Tables`** — concrete rows + prover data.
- **`Air.Flat.Ensemble` / `EnsembleWitness`** — components + channels + verifier
  circuit; `Statement` is the raw relation "∃ witness whose constraints hold and
  whose channels balance".
- **`FormalEnsemble`** — an ensemble bundled with `Assumptions`/`Spec` and an
  `ensemble.Soundness` proof.
- **Two ensemble-soundness arguments are provided for you:**
  - `OrderedChannels.lean` (`SoundEnsemble`, `PartialBalancedChannels`) for
    lookup-like channels with a strict push-before-pull hierarchy;
  - `Vm.lean` for VM-like components that both push and pull one distinguished
    state channel per row — the "guarantees-to-requirements reversal" that is
    exactly the zkVM state-channel pattern.
- **`Balance.lean`** — the channel multiset theory (`BalancedInteractions`,
  `RawChannel.Consistent/Normal`) underneath all of it.

The intended shape of a Clean zkVM proof is therefore: write each AIR as a
`GeneralFormalCircuit` → wrap as `Air.Flat.Component` → assemble a
`FormalEnsemble` → obtain global soundness from `SoundEnsemble` /
`Vm` soundness, so that the *per-table specs are derived from constraints +
channel balance*, and the top-level statement quantifies over an
`EnsembleWitness`.

## 2.2 What the project does idiomatically (keep this)

- **Per-component circuits are genuine `GeneralFormalCircuit`s.**
  `AirsClean/BinaryAdd/Circuit.lean` defines `binaryAddElaborated :
  ElaboratedCircuit`, then `circuit : GeneralFormalCircuit FGL BinaryAddRow unit`
  with `Assumptions := True`, a real `Spec` (`ComponentSpecFacts`),
  `ProverAssumptions` describing honest rows, and `soundness`/`completeness`
  proved via `circuit_proof_start`. The row is a `ProvableStruct`
  (`BinaryAdd/Row.lean`). The constraints are `assertZero`/`lookup` + an
  `OpBusChannel.push`. This is textbook Clean.
- **The full circuit is a `FormalEnsemble`.**
  `AirsClean/FullEnsemble.fullRv64imEnsemble : FormalEnsemble FGL unit`, built
  from a `fullRv64imSoundEnsemble` whose `SoundEnsemble` finished-channel
  structure yields `TableSoundness`. `witness_spec_of_constraints` derives
  `w.Spec` from `w.Constraints` + `w.BalancedChannels` via
  `Ensemble.tableSoundness_of_soundChannels`. This is exactly the intended
  ordered-channel soundness path.
- **The top soundness object is an `EnsembleWitness`.** `AcceptedZiskTrace`
  bundles the ensemble witness with `constraints_hold` and `channels_balanced`,
  and *derives* per-AIR specs rather than assuming them. Good.
- **`@[circuit_norm]` discipline** is followed in the components; the
  `circuit_proof_start` opening move is used in ~13 files.

The fork's one divergence (`Component.transition`) is well-documented, minimal,
additive, and correctly flagged as an upstream-PR candidate. No objection.

## 2.3 Where usage diverges from idiomatic Clean (fix this)

### D1 — A second, non-Clean circuit model is the actual spine
`Airs/` defines `Valid_<AIR>` records — `Valid_Main`, `Valid_Binary`,
`Valid_BinaryAdd`, `Valid_ArithMul`, `Valid_ArithDiv`, `Valid_Mem`,
`Valid_MemAlign*`, `Valid_BinaryExtension` — with column accessors `ℕ → FGL` and
hand-written per-AIR constraint predicates. `Valid_Main` is referenced by **299
files**. The entire equivalence/compliance stack (`EquivCore`, `Equivalence`,
`Compliance/*`) is written against these records. The idiomatic Clean components
(`AirsClean/`) are then bridged *into* the records per opcode
(`AirsClean/<Op>/Bridge.lean`: `rowAt : Valid_<AIR> → r → <Op>Row`,
`spec_of_valid`, `spec_via_component`). So Clean is a *tributary feeding a
hand-rolled model*, not the model itself. Idiomatically the `GeneralFormalCircuit`
`Spec` should *be* the interface the equivalence proofs consume; the `Valid_<AIR>`
record and its bridge should not exist (or should be a mechanically-derived view
of a `Table`/environment, used only where a `ℕ → FGL` column view is genuinely
more convenient).

### D2 — Clean's ensemble soundness is bypassed by a bespoke per-arm dispatch
Although `FormalEnsemble`/`SoundEnsemble`/`TableSoundness` are used to get
`witness.Spec`, the step from "per-table spec holds" to "this Sail transition is
matched" is *not* routed through Clean's soundness lift. Instead it goes through
the `OpEnvelope` 63-arm inductive whose per-arm `exec_eq` conclusion is a 12-way
`True`-padded conjunction, discharged by ten `Dispatch/*` family theorems. Counts
that corroborate the bypass: `Vm.Soundness` used in **0** files, `OrderedChannel`
in **0**, `soundness_of_tableSoundness_and_specConsistency` in **0**,
`isGeneralFormalCircuit` in **0**. The VM state-channel is precisely the pattern
`Clean/Air/Vm.lean` exists to discharge; not using it means the cross-row/register
state-consistency argument is re-derived by hand in the `Compliance` layer.
(Confirm case-by-case before removing anything — some of this may be genuinely
outside what `Vm.lean` currently covers, e.g. the Main PC handshake that motivated
the fork's `transition` field.)

### D3 — The `True`-padded conjunction dispatch is un-idiomatic and un-auditable
`OpEnvelope.exec_eq := aeneasBridgeTrust ∧ memoryTimelineConstructionEvidence ∧
exec_eq_branch ∧ … ∧ exec_eq_remaining`, where each `exec_eq_<family>` is `True`
except for the matching arm, is an awkward encoding of a case split. The docstring
even calls `OpEnvelope` a "sum type (63 arms)" while the *conclusion* is a
conjunction. A plain dependent case-analysis (`match env with | .add … => …`)
returning the single relevant statement is both idiomatic and readable, and it is
what an auditor expects.

### D4 — Caller-supplied "promises" instead of derived facts
The canonical `equiv_<OP>` (e.g. `Equivalence/Add.lean`) carries a large surface
of hypotheses: `providerTable`, `providerRow`, `h_component`, `h_table_spec`,
`h_match`, `h_input_r1_row`, `h_input_r2_row`, `h_lane_rd`, `promises`, `pins`.
Many of these are *facts that hold of any accepted trace* (the provider row is in
a table whose component is the Binary static-lookup component; the op-bus entry
matches; the lanes match). In idiomatic Clean these are *consequences* of
`w.Constraints ∧ w.BalancedChannels` obtained once, generically, from the
ensemble — not per-opcode caller obligations. The `trust/forbidden-param-shapes.txt`
+ `baseline-*-caller-burden.txt` ledger machinery is a home-grown guard whose job
would largely vanish if these facts were derived at the ensemble seam. The
project's own `AGENTS.md` states the target ("Prefer deriving facts from existing
validators, generated rows, or proved lemmas over adding parameters"); D4 is where
it is most violated.

### D5 — Minor stylistic drift
- `import Mathlib` (the whole of Mathlib) at the head of hot per-opcode files
  such as `EquivCore/Add.lean` inflates build times; upstream Clean imports
  narrowly. Worth narrowing on the heaviest files.
- Mixed constructor naming in `OpEnvelope` (`.and_op`/`.or_op`/`.xor_op` vs
  plain `.add`/`.sub`) — pick one convention (noted in
  `simplification-suggestions.md` too).

## 2.4 Idiomatic-Clean scorecard

| Concern | Idiomatic? | Where |
| --- | --- | --- |
| Row types as `ProvableStruct` | ✅ | `AirsClean/*/Row.lean` |
| Circuits as `GeneralFormalCircuit` | ✅ | `AirsClean/*/Circuit.lean` |
| `circuit_norm` / `circuit_proof_start` | ✅ | components |
| Ensemble as `FormalEnsemble` + `SoundEnsemble` | ✅ | `AirsClean/FullEnsemble.lean` |
| Top object is an `EnsembleWitness` | ✅ | `Compliance/AcceptedZiskTrace.lean` |
| Fork divergence documented & minimal | ✅ | `docs/clean-fork-divergences.md` |
| Second (non-Clean) circuit model | ❌ D1 | `Airs/` + `*/Bridge.lean` |
| Global soundness via Clean's lift | ⚠️ partial/bypassed D2 | `Compliance/OpEnvelope`, `Dispatch/` |
| Case split via dependent match | ❌ D3 | `Compliance.lean` `exec_eq` |
| Facts derived, not caller-supplied | ❌ D4 | `Equivalence/*`, `Compliance/Wrappers/*` |
| Narrow imports | ⚠️ D5 | `EquivCore/*` |
