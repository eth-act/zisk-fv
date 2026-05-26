# Integrate Clean `Air.Flat.Component` as the verification's circuit foundation

> **Canonical plan + live handoff document for the zisk-fv "Clean
> integration" epic.** An agent or contributor picking this up: read the
> **"Status and corrections"** section first — it states the current
> state and the *immediate next action*. The governing constraint is the
> **"Axiom policy"** section (user-set: retire every retire-able axiom by
> proof; the only sanctioned new axioms are the ~10 completeness axioms).
> Last updated 2026-05-21.

## Context

zisk-fv proves each RV64IM opcode's ZisK circuit equivalent to the RISC-V
Sail spec. A multi-phase "Clean integration" epic was undertaken to make
the circuit side rest on the **Clean DSL's `Air.Flat.Component` /
`Air.Flat.Ensemble`** machinery — the idiomatic model for AIR circuits and
their channel interactions.

**That integration was never landed.** Investigation established: the Clean
Component layer at `ZiskFv/AirsClean/` is **orphan** — nothing imports it,
the global theorem `zisk_riscv_compliant_program_bus` does not depend on it,
no proof references a `Clean.*` construct. The live verification still rests
on a **hand-rolled `bus_effect` operational model** plus **104 trust
axioms**. The prior plan defined "done" as a structural *marker*
(`ZiskFv/Circuit.lean` deleted) that was reachable without the substance;
the marker was hit, the goal was missed.

This plan **finishes the job**: every ZisK AIR becomes a genuine Clean
`Air.Flat.Component`; they assemble into one `Air.Flat.Ensemble`; Clean's
proven channel-balance and ensemble-soundness theorems discharge the
bus/range/lookup trust axioms; the hand-rolled bus layer is deleted; the 63
per-opcode theorems and the global theorem re-root on the ensemble.

This is a **large multi-phase epic**, but it is an **incremental refactor of
the current complete, green proof — not a rewrite, and no from-scratch
mathematics** (see decision D-REFACTOR). Phase C0 is a hard **GO/NO-GO**
de-risk gate — if its spikes hit a wall the plan is revised before the bulk
work begins.

## End state

- All 10 ZisK AIRs are real Clean `Air.Flat.Component`s (a `GeneralFormalCircuit`
  with discharged `soundness` **and** `completeness`), assembled into one
  `Air.Flat.Ensemble`.
- The global theorem and the 63 per-opcode `equiv_<OP>` theorems derive
  from the ensemble's `Soundness`; the ensemble's `Statement` (constraints
  hold + channels balanced) is the honest top-level hypothesis, and is
  proven **inhabitable** for real ZisK traces (constructibility — see the
  anti-marker discipline).
- `tools/pil-extract` emits the Clean Component circuits; `Constraints.lean`
  / `Row.lean` are generated, faithful-by-construction.
- The hand-rolled bus layer is deleted: `ZiskFv/Airs/{Bus,OperationBus,MemoryBus}/`,
  `BusShape*`, the `Valid_<AIR>` records, the per-AIR circuit theorems and
  `*Ranges` axiom files. `bus_effect`'s Sail-state-effect core is retained
  (it is the irreducible Sail bridge); only the permutation/matching
  machinery around it goes.
- **Trust surface — two classes, accounted separately.** *Soundness-critical
  axioms:* **~104 → ~57.** Retired: the bus-protocol, range, and lookup-table
  classes (~47). Irreducible and retained: ~52 `transpile_<OP>` (a contract
  about ZisK's Rust transpiler — Clean cannot touch it) and ~5 Sail-spec
  axioms (`SailSpec/Auxiliaries.lean`, `ZiskCircuit/MemModel.lean`). **~57 is
  the accepted soundness-critical floor.** *Plus a new, separate
  completeness class:* **~10 axioms, one per AIR** (see D-COMPLETE) — these
  ARE in `#print axioms` of the global theorem, but they are
  completeness-direction: a falsehood in one cannot make a wrong execution
  verify. Total closure ~67, cleanly split; the meaningful number is the
  ~57 soundness-critical.
- Net lines-of-code: a decrease is expected (the hand-rolled `Airs/` bus
  layer is ~14.6k LoC; Clean is a dependency, not counted). **Per the
  user, net-LoC is a heuristic checked once at the end, not a per-phase
  gate.**

## Axiom policy (user-set — the governing success metric)

**This records a decision owned by the user. It governs the epic and
overrides any phase-local convenience. Future agents: treat it as a
fixed constraint — do not re-litigate it, do not drift from it.**

The purpose of the epic is to **retire as many trust axioms as
possible**:

- **Every axiom in the "~47 in scope" set** — the op-bus, memory-bus,
  range-bus, lookup-table, Binary-pin and Arith-table classes — **is
  retired by *proof*** (Clean channel-balance, `StaticTable`
  `contains_iff`, or adapted Component soundness). None may be
  re-stated, renamed, corrected-in-place, or consolidated into a fresh
  axiom. A "corrected axiom" or a "19→1 consolidated axiom" is still a
  **new axiom — NOT permitted.** If a phase appears to need a new
  soundness / lookup / table axiom, that is a signal it is taking a
  shortcut: re-scope it to discharge the fact by proof.
- **The ~57 `transpile_<OP>` + Sail-spec axioms are genuinely
  irreducible** and are retained; the epic neither adds nor removes
  them. "As many as possible" means everything except these.
- **The one sanctioned exception — the ~10 completeness axioms
  (D-COMPLETE).** The user has **explicitly greenlit** filling each
  Component's mandatory `completeness` field with a declared axiom
  rather than proving it. **The user's rationale:** the epic's *first
  goal is parity* — with (a) the pre-epic zisk-fv verification and
  (b) openvm-fv's verification of OpenVM — and **neither establishes
  completeness**. Completeness is out of scope for the parity bar; a
  declared completeness axiom is the *intended design*, not an agent
  shortcut. An agent or reviewer meeting a `<air>_circuit_completeness`
  axiom must treat it as sanctioned and must NOT flag it as trust
  inflation.
  **The sanction has a hard limit:** it permits leaving completeness
  *unproven* — it is **not** a licence to state it *falsely*. Each
  `<air>_circuit_completeness` axiom must be a faithfully-stated, true
  proposition. An over-strong or false completeness axiom is the
  `arith_table_op_*` defect (see "Status and corrections") repeated —
  unsound, and not sanctioned. (Proving completeness, beyond parity,
  is a possible future follow-on — not in scope here.)

**Success metric:** the soundness-critical axiom count falls (~104 →
~57); the only count that rises is the separate, user-sanctioned
completeness class (+~10); nothing else is added.

## What the investigation established (ground truth)

**Clean library (`build/clean-lean/Clean/`) — mature, fully proven, zero
`sorry` on the critical path:**
- `Air/Balance.lean` — `consistent_of_normal` (PROVEN: a `Normal` channel +
  balanced interactions + per-interaction requirements ⟹ guarantees). Typed
  `Channel`s are `Normal` by construction. This is what replaces the
  permutation axioms.
- `Air/FlatComponent.lean` — `Component F` wraps a `GeneralFormalCircuit F
  Input Output`. `Component.weakSoundness` / `Table.weakSoundness` (PROVEN):
  `Assumptions → Constraints → Guarantees → Spec`.
- `Air/FlatEnsemble.lean` — `Ensemble` = list of heterogeneous `Component`s
  + shared `channels`. `soundness_of_tableSoundness_and_specConsistency`
  (PROVEN): per-table soundness composes to ensemble soundness.
  `BalancedChannels` is a hypothesis of the proof-system `Statement`, not an
  axiom. `merge`/`addTable` build ensembles incrementally.
- `Circuit/Lookup.lean` — `StaticTable` (explicit rows `Fin length → Row F`
  + a `contains_iff` proof) is the proven mechanism for static ROM tables.
  ZisK's tables (BinaryTable, BinaryExtensionTable, the 74-row ArithTable)
  are static → this is the path.
- `Air/Vm.lean` (`addVm`, `SoundVmChannel`) — the mechanism for cross-row
  state handshakes (a component that pulls **and** pushes one channel —
  Main's PC handshake, MemAlign's register chain). **Not** `OrderedChannel`
  (that is for ordered *lookup* channels where pushers strictly precede
  pullers).

**`GeneralFormalCircuit` (`Clean/Circuit/Basic.lean:415`)** bundles
`Assumptions`, `Spec`, `soundness` **and** `completeness` (line 428 — a
mandatory field; `ProverAssumptions`/`ProverSpec` default to `True`, so
completeness is "constraints satisfiable from honest witnesses").

**Current 92-axiom trust state** (`trust/baseline-axioms.txt`):
- ~52 `transpile_<OP>` (`ZiskFv/Trusted/Transpiler.lean`) — **irreducible**.
- ~5 Sail-spec (`SailSpec/Auxiliaries.lean` ×4, `ZiskCircuit/MemModel.lean`
  ×1) — **irreducible**.
- the remaining reducible scope is concentrated in operation-bus balance
  (`op_bus_permutation_sound`), memory-bus emission/align bridges,
  range-bus soundness (2), Binary/BinaryExtension table consumer
  well-formedness (2), and Arith range/table dynamic facts;
- the recently retired Binary bitwise axioms
  (`binary_per_byte_lookup_witness`,
  `binary_b_op_or_sext_eq_op_general`) are no longer in the live baseline.

**Current `AirsClean/<AIR>/` state** (10 AIRs): each has a real `Row`
`ProvableStruct`; `Constraints.lean`'s `main` emits **only** `assertZero`
F-constraints (faithful to extraction) and **no** channel/lookup
interactions; `Spec` is real for BinaryAdd/ArithMul/ArithDiv/MemAlignByte/
MemAlignReadByte and **vacuous or skeleton** for Binary/BinaryExtension/
Mem/MemAlign/Main (`BinaryExtension`'s `Spec` is literally `True`);
`Soundness` is a real proof for the first 5 and a skeleton for the rest;
**no AIR is packaged as a `GeneralFormalCircuit`/`Component`** — even
BinaryAdd's `soundness` is a bespoke `theorem` taking the constraints as
explicit hypotheses, not connected to `main`. The `Bridge.lean` files are
orphan.

**Three mis-scopings corrected by investigation** (these defeated the naïve
plan):
1. The in-scope axioms `op_bus_permutation_sound` and `range_bus_sound` are
   **shared across many AIRs** — they retire only when the **last** consumer
   is migrated, at family-terminal phases, never per-AIR.
2. `completeness` is a **mandatory `GeneralFormalCircuit` field** the
   pre-Clean verification never established (it is soundness-only).
   Resolved by **axiomatizing** it — a declared, non-security-critical
   trust class, not a proof (D-COMPLETE).
3. **Re-rooting the 63 `equiv_<OP>` on the ensemble is the hardest part and
   carries a vacuity trap**: `Ensemble.Soundness` concludes `Spec
   publicInput`; `equiv_<OP>` concludes a raw equality. Bridging needs an
   ensemble `Spec` entailing the equalities and a **constructible**
   `EnsembleWitness` from real trace data. If the witness is not
   constructible every re-rooted theorem is vacuously true and the build
   stays green (silent failure).

## The anti-marker discipline (READ THIS — it is the spine of the plan)

The prior plan failed because "done" was a *marker*. Every gate in this
plan is **substantive and measurable**, never a marker:

- **A Component is real only when it is on the global theorem's dependency
  graph.** "`xComponent` elaborates" is a marker. The substance:
  `#print axioms zisk_riscv_compliant_program_bus` (or the per-opcode
  `equiv_<OP>`) provably routes through `xComponent`. A Component not
  reachable from the global theorem is not part of the verification.
- **No vacuous `Spec`.** `Spec := True`, or a `Spec` that merely
  re-states an assumption, proves nothing. Every AIR's `Spec` must be the
  genuine algebraic relation it computes, and **each `Spec` clause is cited
  to a specific PIL constraint line** (constructibility audit, CLAUDE.md
  anti-laundering #4). New `def`s are `@[reducible]` so the V2 gate's
  `whnfR` can see through them.
- **Axiom retirements are named and proven on the global theorem.** A phase
  may claim "retires axiom A" only when (a) A is named in
  `trust/baseline-axioms.txt`, (b) the phase migrates A's last consumer,
  (c) `#print axioms zisk_riscv_compliant_program_bus` no longer lists A,
  (d) `trust/.shrinkage-floor` is decremented by exactly the count retired
  in the same PR. **Most phases retire zero axioms — and label themselves
  honestly so.** Retiring an *intermediate* lemma's axiom, or renaming an
  axiom, does not count.
- **The re-root is not done until the ensemble `Statement` is provably
  inhabited.** A `Statement → Spec` theorem with an unsatisfiable
  `Statement` is vacuous. CZ carries an explicit constructibility lemma:
  a real ZisK trace yields an `EnsembleWitness` satisfying
  `Constraints ∧ BalancedChannels`. A green `lake build` is **not**
  evidence here — vacuity is invisible to the build; a reviewer must
  confirm constructibility.
- **The trust gate (`check-all.sh` + `check-all-semantic.sh`) is green at
  every phase boundary.** Each phase ends with a working tree.

## Pre-resolved decisions

- **D-REFACTOR — this epic is an incremental refactor of a complete, green
  proof, not a rewrite.** The verification builds and the trust gate passes
  *today*; it must do so at every phase boundary. There is **no from-scratch
  mathematics**. Each AIR's Component `soundness` is discharged by *adapting
  the AIR's existing correctness proof* — the per-opcode `EquivCore/` proofs,
  the algebraic content in `Airs/<X>/` and `ZiskCircuit/`, and (for 5 AIRs)
  the already-real `AirsClean/<X>/Soundness.lean` — reshaped into the
  `GeneralFormalCircuit.soundness` signature. A skeleton
  `AirsClean/<X>/Soundness.lean` is an *unfinished port*, not an unknown
  proof; its source material exists. Per AIR: the Component is introduced
  *alongside* the still-working `Valid_<X>` record, that AIR's consumers are
  rewired to it, and only then is `Valid_<X>` deleted — green build
  throughout, except when a known-false trust-ledger entry is being
  corrected. Existing proof content moves and gets wrapped; it is never
  duplicated or discarded (this is also what keeps the net-LoC heuristic
  honest). There is **no from-scratch AIR algebra proof work**: local
  `soundness` is adapted from existing proofs. Lookup/bus retirements are
  only claimed when their membership/balance boundary is honestly represented:
  either by a Clean ensemble theorem already on the global dependency graph
  or by a documented shared temporary lookup/permutation axiom. `StaticTable`
  proves table-content consequences after membership; it does not itself
  prove a trace row performed a sound lookup. `completeness`
  is **axiomatized, not proved** (D-COMPLETE) — the project does not claim
  completeness today, and an honest declared axiom beats spending effort
  proving a property outside the verification's claim.
- **D-EXT — `pil-extract` emits the Clean Component circuits.** Per the
  user. The extractor is extended to emit, per AIR, the `Row` `ProvableStruct`
  and the `main : Circuit FGL Unit` do-block (F-constraints **and** channel/
  lookup interactions). `Constraints.lean`/`Row.lean` become generated,
  faithful-by-construction — this is itself the primary defense against the
  vacuity/over-strong-circuit trap. The extension is **staged**: C0 extends
  the extractor for the BinaryAdd shape (op-bus emission); each later phase
  extends it for its AIR's new interaction kind (range lookups, ROM lookups,
  memory bus, cross-row) as that phase's first step. The extractor is never
  extended for a shape before C0/that phase has validated it on one AIR.
  The channel/lookup emissions — which the extractor currently *skips* (they
  mix F and ExtF) — are cross-checked field-for-field against the existing
  hand-rolled `opBus_row_<X>` / memory-bus emission defs, which are the
  faithful reference, **before** those hand-rolled defs are deleted.
- **D-LOC — net-LoC is an end-of-epic heuristic check**, not a per-phase
  gate. Each phase records its LoC delta; the cumulative is reckoned once at
  CZ (expected ≤ 0; if not, investigate).
- **D-COMPLETE — the `completeness` field of every Component is
  AXIOMATIZED, not proved.** Clean's `GeneralFormalCircuit` makes
  `completeness` a mandatory field; zisk-fv is a soundness-only verification
  and does not claim completeness (the pre-Clean code never proved it
  either — it is, at most, a "constructibility sketch" review obligation).
  Each AIR's `completeness` field is filled by a per-AIR axiom
  `<air>_circuit_completeness : GeneralFormalCircuit.Completeness FGL …`.
  These ~10 axioms form a **new, declared, non-security-critical trust
  class** — their own allowlisted file (e.g. `ZiskFv/AirsClean/Completeness.lean`),
  a `docs/fv/trusted-base.md` entry stating "completeness-direction; the
  verification's soundness does not depend on these", and `.shrinkage-floor`
  raised to account for them. They DO appear in `#print axioms` of the
  global theorem (the `Component` value carries the field) — that visibility
  is the point: an honest declared axiom over a vacuous `ProverAssumptions
  := False` proof that would hide the non-proof. C0 declares the BinaryAdd
  completeness axiom; it does not prove completeness.
  **Provenance — this is the user's decision, not an agent's.** The user
  greenlit axiomatizing `completeness` because the epic's first goal is
  *parity* with the pre-epic verification and with openvm-fv — neither
  establishes completeness (see "Axiom policy"). It is the sole sanctioned
  new-axiom class; every other axiom is retired by proof. The sanction
  covers leaving completeness *unproven*, not stating it falsely — the
  axiom must be a faithfully-stated, true proposition.
- **D-CROSSROW — cross-row constraints use `Air/Vm.lean`'s `addVm`**, not
  `OrderedChannel`. `OrderedChannel` is reserved for ordered lookup tables.
- **D-ROM — static ROM tables use `StaticTable`** with an explicit row
  enumeration and a proven `contains_iff`. **Resolved:** C0e built a
  `StaticTable` spike, and the real 74-row ArithTable `StaticTable`
  (`AirsClean/ArithTable.lean`) has a tractable `contains_iff` — the
  `decide`-scaling risk does not materialize. The former fallback (a
  `arith_table_content` axiom) is **withdrawn**: a new axiom is not
  permitted (see "Axiom policy"); the `StaticTable` is the path.
- **D-SHARED — shared axioms retire at family-terminal phases.** No
  per-AIR phase claims a shared-axiom retirement.
- **D-STOP — C0 is GO/NO-GO.** If any C0 spike hits a wall, **stop and
  bring the user options** before C1.
- **D-BRANCH — work continues on `phase-E-baseline-from-F7`** (or a fresh
  branch off it); the F7 base is intact. No wall-time estimates anywhere —
  complexity descriptors only.

## Phase C0 — De-risk pilot (BinaryAdd vertical slice + spikes) — GO/NO-GO

C0 converts BinaryAdd's loose pieces into a **wired, used** Clean `Component`
in a minimal `Ensemble`, generated by an extended `pil-extract`, and spikes
the three things BinaryAdd alone does not exercise. C0 proves — by building
them — that the hard sub-problems are tractable.

**Steps:**
1. **Extend `pil-extract` for BinaryAdd.** Teach the extractor to emit a
   Clean Component circuit for the BinaryAdd AIR: the `Row` struct + a `main`
   that emits the 4 `assertZero`s **and** the op-bus interaction. The op-bus
   emission is reconstructed from `binary_add.pil` + the hand-rolled
   `opBus_row_BinaryAdd` (`Airs/OperationBus/OperationBus.lean`), and
   cross-checked field-for-field against it.
2. **Define the op-bus `Channel`** (`AirsClean/Channels/OpBus.lean`, new):
   `OpBusMessage` as a fresh `ProvableStruct` (the 12 op-bus value slots —
   `OperationBusEntry` is not a `ProvableType`), and `OpBusChannel : Channel
   FGL OpBusMessage`. Typed channels are `Normal` ⟹ `Consistent` for free.
3. **Construct `binaryAddComponent : Air.Flat.Component FGL`** from a
   `GeneralFormalCircuit FGL BinaryAddRow unit`. Discharge `soundness` by
   `circuit_proof_start` (exposes the 4 `assertZero`s as hypotheses) +
   the existing 229-line `Soundness.lean` proof, now folded into the
   `soundness` field. Fill `completeness` with the per-AIR axiom
   `binaryAdd_circuit_completeness` (D-COMPLETE) — declared, not proved.
4. **Assemble a minimal `Ensemble`** — BinaryAdd Component + a deliberately
   trivial consumer Component sharing `OpBusChannel` (not the real Main).
   Template: Clean's `FibonacciWithChannels.lean`.
5. **Re-root ADD/ADDI** (`EquivCore/Bridge/BinaryAdd.lean`'s `add_discharge`):
   source BinaryAdd's algebraic facts from `Component.weakSoundness` instead
   of the hand-rolled carry lemmas. The op-bus existential stays on the
   shared `op_bus_permutation_sound` axiom for now (retired family-terminal).
6. **Spike Z-ROM** (`AirsClean/_Spike/`): build a `StaticTable` for the real
   BinaryTable ROM and prove `contains_iff`. Measures the `decide`-scaling
   risk; ArithTable (74 rows) is the harder case, noted for C3/C4.
7. **Spike Z-VM** (`AirsClean/_Spike/`): a toy two-row state handshake via
   `addVm`, proving the cross-row mechanism composes for a small table.
8. **Spike Z-ROOT** (within step 5): confirm ADD can be re-rooted on the
   minimal ensemble with a **constructible** witness — i.e. the minimal
   ensemble's `Statement` is provably inhabited for an ADD trace. This
   spikes mis-scoping #3 in miniature.

**GO requires ALL of:** (a) `binaryAddComponent` elaborates with zero
`sorry`; `soundness` is proved; `completeness` is the declared axiom
`binaryAdd_circuit_completeness` (the *only* new axiom — accounted in the
completeness class, D-COMPLETE); (b) `main` provably emits exactly the
op-bus interaction matching `opBus_row_BinaryAdd` field-for-field; (c) the
minimal ensemble's `FormalEnsemble`/soundness elaborates with zero `sorry`;
(d) `equiv_ADD`/`equiv_ADDI` still typecheck and their `#print axioms` no
longer reaches the hand-rolled BinaryAdd carry lemmas; (e)
`AirsClean/BinaryAdd/` is reachable from the global theorem's dependency
graph; (f) both spikes Z-ROM and Z-VM build; (g) Z-ROOT shows the ADD
re-root has a constructible witness; (h) trust gate green. **C0 retires no
*soundness* axiom — and says so** (BinaryAdd has no private soundness axiom;
per D-SHARED the first soundness retirement is family-terminal); it *adds*
one completeness axiom.

**NO-GO (stop, bring the user options):** `contains_iff` not provable /
`decide` blows up on BinaryTable; the op-bus `Channel` cannot faithfully
represent the emission; the ADD re-root needs a non-constructible witness;
`circuit_proof_start` does not compose with Goldilocks `FGL`.
(Completeness is no longer a NO-GO risk — it is axiomatized.)

## C0 de-risk findings (propagated to all later phases)

C0's spikes surfaced facts that re-shape the per-AIR contract — recorded
here once; every later phase relies on them.

- **F-1 — `circuit_proof_start` composes with Goldilocks `FGL`** (C0a
  discharged BinaryAdd `soundness` with it; `#print axioms` clean). Risk
  R-8's original form is **resolved**.
- **F-2 — the assembly API composes; ensembles are non-vacuous** (C0c took
  the minimal ensemble through `toFormal` to a `FormalEnsemble`).
  `AssumptionsConsistency` discharges only because each Component carries
  `Assumptions := True` (F-4).
- **F-3 — consuming a Component's `soundness` raw-`whnf`-explodes; the
  crack is `circuit_norm`-normalization.** Applying `circuit.soundness` /
  `Component.weakSoundness` as a term forces Lean to raw-`whnf` the
  circuit's `operations` do-block — non-terminating (confirmed: timeout at
  1,000,000 heartbeats; making `main` `@[irreducible]` to block it instead
  breaks `ElaboratedCircuit`'s autoparam `rfl` defaults — a pincer).
  **Working idiom — used by every D-6 rewiring and the CZ re-root:**
  ```
  have h := <circuit>.soundness
  simp only [GeneralFormalCircuit.Soundness, <circuit>, <elaborated>,
    circuit_norm] at h     -- circuit_norm reduces `operations` in
                           -- controlled steps; raw whnf does not
  -- h : ∀ env input_var input, evaluated-row = input
  --        → <constraints> → Spec input ∧ <requirements>
  ```
  then apply `h` with a constant-expression row built from the caller's
  values. Captured as `AirsClean/BinaryAdd/Circuit.lean :: spec_via_component`
  — the template every later AIR's consumer-rewiring lemma copies. (Lead:
  Clean's own `Keccak.Permutation` hit the same timeout class and worked
  around it with `simp only`.)
- **F-4 — a Component's `Assumptions` is `True`.** Column range bounds come
  from `range_bus_sound` *inside* `soundness`, not declared as
  `Assumptions`; this keeps both ensemble `AssumptionsConsistency` and the
  re-root non-vacuous. D-2's "`Assumptions` minimal" ⇒ "`Assumptions := True`".

## Status and corrections (current — 2026-05-25)

The live branch is in the post-C3/C4, post-C5/C6, C7-derived terminal
integration arc. The authoritative detailed checklist is
[`docs/fv/clean-integration-status.md`](clean-integration-status.md). This
master plan now treats that file as the running checklist; this section
records the corrected high-level structure.

Execution has already passed the old local AIR milestones for ArithMul,
ArithDiv/Rem, BinaryExtension, and Binary under the current defect and trust
policy. The current trust baseline is **92 axioms**, and both V1 and V2 trust
gates pass. The most recent Binary-family step retired
`binary_per_byte_lookup_witness` and `binary_b_op_or_sext_eq_op_general`
entirely by threading lookup-aware static Binary provider rows into the six
canonical bitwise arms `AND/OR/XOR/ANDI/ORI/XORI`.

The key correction from C7 is that the rest of the epic must be planned by
**terminal trust retirements**, not by broad local AIR names. "C7" was too
large: it mixed balance, provider-row extraction, static lookup membership,
row-native opcode bridges, canonical dispatch, and trust-ledger cleanup. The
new phase structure splits those apart by family and by the named axioms
they are meant to retire.

### Correctness-first trust policy

The current arithmetic-table finding changes how this plan treats a green
build. A green `lake build` is meaningful only relative to a meaningful
trust ledger. Keeping the build green by preserving false or over-specific
axioms is not progress; replacing them with one honest trust boundary is.

For lookup tables, the intended architecture has three separate layers:

1. **Static table content** — the table is translated into Lean and
   finite-row membership proves the table's row facts. For ArithTable this
   is `AirsClean/ArithTable.lean` plus the faithful projection lemmas in
   `AirsClean/ArithTableProjections.lean`.
2. **Trace-to-lookup emission** — the AIR row emits the advertised lookup
   tuple, e.g. Arith's 15-column `arith_table_assumes` row. Clean can state
   and manipulate this cleanly via `lookup (Table.fromStatic ...)`.
3. **Lookup/permutation soundness** — the PLONK/logUp-style argument says
   the consumer lookup multiset is supplied by the provider/static-table
   multiset, except with the usual negligible soundness error. This
   cryptographic argument is still outside Lean unless separately
   formalized. Clean does not prove that polynomial argument from first
   principles; it proves semantic consequences once channel balance /
   lookup soundness is assumed or established in an ensemble statement.

Therefore the allowed temporary trust shape for C3/C4 is:

```lean
-- schematic, not the exact final type
arith_table_lookup_sound :
  every Arith row's emitted arith_table_assumes tuple is in ArithTable
```

or the equivalent Clean-ensemble statement requiring balanced channels.
This axiom is acceptable only if it is **shared**, **row/table-level**,
and documented as the lookup/permutation boundary. It must not mention
opcode-specific conclusions such as `MUL → na = 0`, `MULW → sext = 0`,
or `MULH → np = na XOR nb`.

The bad pattern is now explicitly banned:

- Do not introduce or preserve per-opcode table-fact axioms that bundle
  lookup membership with row-content consequences.
- Do not use `op = ...` alone as a substitute for lookup membership.
- Do not hide lookup membership inside a theorem-specific promise binder.
- Do not treat `lake build` as a correctness marker while known-false
  soundness axioms remain in the global theorem closure.

The near-term objective is to complete **T1 Binary-family terminal cleanup**:
finish the row-native routes for remaining Binary/BinaryExtension consumers,
then retire `op_bus_permutation_sound`, `bin_table_consumer_wf`, and
`bin_ext_table_consumer_wf` exactly when the global closure no longer uses
them. After T1, the same pattern is applied to BinaryAdd, control-flow,
memory, Arith, range-bus, and finally the full ensemble re-root.

### Done and verified
- **C0, C1 (MemAlignByte), C2 (MemAlignReadByte)** — done, independently
  verified (`lake build` green; V1 + V2 trust gates pass; the Components
  are load-bearing on `zisk_riscv_compliant_program_bus`). On branch
  **`clean-air-integration`** (pushed to `eth-act/zisk-fv`, HEAD `b390eeb`).
- The carry-chain Components for **C3 (ArithMul)** and **C4 (ArithDiv)**,
  and the faithful 74-row ArithTable `StaticTable`
  (`ZiskFv/AirsClean/ArithTable.lean`, cross-checked 0-mismatch against
  `arith_table_data.rs`), are built.
- **C3/C4-a structural lookup setup** is implemented: full 15-column
  `arithTableRow` projections, lookup-aware `mainWithArithTable`
  entry points, split `ArithTableSpec` / `FullSpec`, and bridge helpers
  `full_spec_of_carry_chain_and_arith_table`. This stage intentionally
  retires zero axioms.

### The arith-table soundness defect (the C3/C4 completion fixes it)
The 19 `arith_table_op_*` axioms in `ZiskFv/Airs/Arith/Ranges.lean` were
all introduced by **one commit — `14d4bff`, PR #26, 2026-05-14** (recent
agent work, not long-standing trust). A programmatic cross-check against
the 74-row ROM first found **4 are provably false** — each pins a ROM
column to a value the ROM ranges over:

| False axiom | False claim | ROM reality |
|---|---|---|
| `arith_table_op_mul_mode_pin` | `na=nb=np=0`, op 180 | `na/nb/np ∈ {0,1}` |
| `arith_table_op_mulw_mode_pin` | `sext=0`, op 182 | `sext ∈ {0,1}` |
| `arith_table_op_div_rem_unsigned_w_mode_pin` | `sext=0`, op 188/189 | `sext ∈ {0,1}` |
| `arith_table_op_div_rem_signed_w_mode_pin` | `sext=0`, op 190/191 | `sext ∈ {0,1}` |

The Clean projection implementation found two additional corrections:
`arith_table_op_mulh_mode_pin` and `arith_table_op_mulhsu_mode_pin`
also over-claim if read as pure ROM projections, because their `np =
na XOR nb` conclusion does not hold for all `op = 181` / `op = 179`
ROM rows. The table does support weaker facts (`nr=sext=m32=div=0`,
boolean `na`/`nb`/`np`, and `nb=0` for MULHSU), now proved in
`AirsClean/ArithTableProjections.lean` as `mulh_basic_mode_pin` and
`mulhsu_basic_mode_pin`. It also confirmed that W-mode `sext = 0`
must not be recreated as a static-ROM projection: the ROM contains
matching W rows with `sext = 1`.

Current projection inventory in `AirsClean/ArithTableProjections.lean`
proves the faithful ROM-data half for:
`mul_basic_mode_pin`, `mul_main_selector_pin`, `mulhu_mode_pin`,
`mulhu_main_selector_pin`, `mulh_basic_mode_pin`,
`mulh_main_selector_pin`, `mulhsu_basic_mode_pin`,
`mulhsu_main_selector_pin`, `mulw_basic_mode_pin`,
`mulw_main_selector_pin`, `div_rem_signed_mode_pin`,
`div_rem_unsigned_mode_pin`, `div_rem_main_selector_pin`,
`div_rem_unsigned_main_selector_pin`,
`div_rem_unsigned_w_basic_mode_pin`,
`div_rem_signed_w_basic_mode_pin`, and `div_rem_w_main_selector_pin`.
All require `ArithTableSpec (rowAt v r)`. The first shared-boundary
rewiring is now live for signed DIV/REM, unsigned DIVU/REMU, and MULHU:
their mode/selector facts flow through `arith_{mul,div}_table_lookup_sound`
plus these finite-table projection lemmas instead of opcode-shaped table
axioms.

For **C3/ArithMul**, the local lookup bridge is now also present:
`ArithMul/Bridge.lean` defines `constVar` and proves
`arith_table_spec_of_lookup_aware_const_soundness`, and the MUL-family
projection lemmas have `_of_lookup_aware_soundness` variants. These
variants compose the lookup-aware Clean circuit's `ConstraintsHold.Soundness`
directly with the faithful ROM projections for the concrete
`rowAt v r`. They intentionally prove only the true static-table facts;
they do not recreate the old false `np_xor` or W-mode `sext = 0`
conclusions.

The same file now also contains formal counterexample lemmas
(`Counterexamples.*_not_static`) for the known false static readings:
MULH/MULHSU `np_xor` is not a ROM-column fact, and W-mode `sext = 0`
is refuted by concrete ROM rows for MULW, DIVUW, and DIVW.

The practical issue is **not** that the static table is unusable. The
issue is that several old `arith_table_op_*` axioms bundled three
different kinds of claims under one name:

| Claim kind | Example | Can static ROM prove it? | C3/C4-b action |
|---|---|---:|---|
| Faithful ROM column facts | `main_mul`, `main_div`, `m32`, `div`, many `na/nb/np` boolean or zero pins | Yes, once `ArithTableSpec (rowAt v r)` is sourced | Replace with projection lemmas |
| Over-strong static claims | MULH/MULHSU `np = na XOR nb`; W-mode `sext = 0` | No; counterexample rows exist in the ROM | Do not project; repair consumers using real dynamic constraints or sign-agnostic arithmetic |
| Dynamic non-ROM facts | signed DIV/REM remainder `d`-sign/bounds and DIVW operand side conditions | No; these come from `assumes_operation` / Binary-side lookup | Leave deferred until Binary / lookup ensemble work |

A false axiom makes its consumers vacuous — `equiv_MUL`, `equiv_MULW`,
`equiv_DIVW/REMW/DIVUW/REMUW` are vacuous for the excluded operand
cases. **The verification is, as it stands, unsound.** The C3/C4
completion must delete the over-claiming axioms and reprove their
consumers using only faithful ROM facts plus separately justified
dynamic constraints.

### Shared Arith prerequisite — completed before C3/C4 split

The old combined "C3/C4" checklist is retired. C3 now means **ArithMul
only**; C4 means **ArithDiv/Rem only**. Shared setup remains a prerequisite,
not a mixed active phase.

Shared prerequisite state:
- 🪓 The 74-row `ArithTable` is translated into Lean and checked against
  `arith_table_data.rs`.
- 🪓 ArithMul and ArithDiv expose the full 15-column
  `arith_table_assumes` row in PIL order.
- 🪓 Lookup-aware Clean entry points and `ArithTableSpec` /
  `FullSpec := Spec ∧ ArithTableSpec` bridge helpers exist.
- 🪓 The shared lookup/permutation boundaries exist:
  `arith_mul_table_lookup_sound` and `arith_div_table_lookup_sound`.
- 🪓 Faithful finite-table projection lemmas exist in
  `AirsClean/ArithTableProjections.lean`.
- 🪓 The defect-aware public theorem
  `zisk_riscv_compliant_program_bus_except_known_defects` avoids the
  old Arith proof closure by routing currently blocked Arith arms through
  `h_known_bugs : Defects.NoKnownDefect env`.

Progress after this point is measured by shrinking
`Defects.UsesOpcodeSpecificArithTableAxiom`. An opcode is not marked
complete merely because the defect-aware theorem excludes it; it is complete
only when its own wrapper is repaired and its constructor is removed from
that predicate.

Retirement rule after the purge phase: do not delete an `arith_table_op_*`
axiom merely because the defect-aware theorem hides it. Delete it only after
all direct consumers are reproved against true ROM facts or separately
justified dynamic facts.

### C3.2-P — controlled ArithTable axiom purge (complete)

This phase temporarily changed the development invariant for the arithmetic
table cleanup only. It is now closed: the false opcode-shaped table
assumptions are removed from the active proof surface, and the ordinary
zero-sorry invariant is restored. The remaining signed-MUL limitations are
known-defect exclusions, not proof holes.

- 🪓 **C3.2-P1 — classify the arithmetic-table facts.**
  `docs/fv/arith-table-axiom-audit.md` is the source of truth for whether
  each old fact is a true finite-table projection, false as stated, or a
  dynamic/protocol-boundary fact.
- 🪓 **C3.2-P2 — purge false opcode-shaped facts from active closures.**
  Remove or neutralize direct use of known-false static conclusions:
  `np_xor` for `MULH`/`MULHSU`, all-zero sign witnesses for exceptional
  `MUL` table rows, and W-mode `sext = 0`.
  Done: `MULH`, `MULHSU`, `MUL`, `MULW`, `DIVUW`, `REMUW`, `DIVW`, and
  `REMW` no longer call the false opcode-shaped mode-pin axioms from their
  active wrappers. Remaining signed-MUL gaps are explicit known-defect
  exclusions.
- 🪓 **C3.2-P3 — replace true static facts with Clean projections.**
  Use `arith_{mul,div}_table_lookup_sound` plus finite-table projection
  theorems from `AirsClean/ArithTableProjections.lean`; add missing
  projection theorems where the audit says `derivable-via-lookup`.
  Done: the true static mode/selector facts consumed by the active wrappers
  now route through Clean projection theorems. The remaining candidates that
  looked like missing projections were reclassified in the audit because they
  mention concrete witness chunks or dynamic arithmetic facts outside the
  15-field ArithTable lookup tuple.
- 🪓 **C3.2-P4 — classify every non-static break.**
  Each remaining obligation must become either a dynamic row/range/bus proof
  target or a documented defect if a satisfying bad witness exists.
  Done: `arith-table-axiom-audit.md` records the signed-MUL residual as
  `arithMulSignedWitnessSoundness` and records the non-pure-table
  sign/operand/bound facts as dynamic proof targets. The W-contract holes
  were discharged in C3.5/C4.3/C4.4.
- 🪓 **C3.2-P5 — restore normal invariants.**
  Restore `lake build`, `trust/scripts/check-all.sh`, and
  `nix develop --command trust/scripts/check-all-semantic.sh`, then return to
  strict C3.2. Completed for the purge: all W-contract repairs are complete;
  those wrappers no longer need the false `sext = 0` premise. The false
  opcode-shaped ArithTable axiom declarations for `MUL`, `MULH`, `MULHSU`,
  `MULW`, unsigned-W DIV/REM, and signed-W DIV/REM have been deleted from
  `Ranges.lean`. The remaining signed-MUL limitations are not proof holes:
  they are explicit known-defect exclusions under
  `arithMulSignedWitnessSoundness`.

The shared lookup/permutation assumptions
`arith_mul_table_lookup_sound` and `arith_div_table_lookup_sound` stay in
scope; they are the accepted protocol boundary, not the fiasco being purged.

### C3 — ArithMul checklist (active after C2.5)

C3 owns only these constructors:
`mulhu`, `mulh`, `mulhsu`, `mul`, `mulw`.

- 🪓 **C3.1 — unblock `MULHU`.**
  Confirm `equiv_MULHU` depends only on shared ArithTable lookup membership
  plus faithful projections for its table facts. Remove `.mulhu` from
  `UsesOpcodeSpecificArithTableAxiom`; update the defect ledger/status.
  Completed: `equiv_MULHU`'s axiom closure is
  `arith_mul_table_lookup_sound`, `arithMul_circuit_completeness`,
  `range_bus_sound`, `main_external_arith_emission_bundle`, and
  `transpile_MULHU`; no opcode-shaped ArithTable axiom remains.
- 🪓 **C3.2 — defect-qualify `MULH`.**
  Stop using static-ROM `np = na XOR nb`; keep the faithful
  `mulh_basic_mode_pin` facts; delete the old
  `arith_table_op_mulh_mode_pin`; remove `.mulh` from
  `UsesOpcodeSpecificArithTableAxiom`. Completed for this branch:
  `equiv_MULH` now carries the explicit false premise
  `h_no_signed_mul_witness_defect : False`, derived at the global theorem
  from `h_known_bugs`. This is intentionally vacuous for `MULH` envelopes
  and marks the confirmed circuit bug. Executable repro evidence confirms
  stock ZisK accepts and verifies a malicious proof for `MULH(-1,1)=0`.
- 🪓 **C3.3 — defect-qualify `MULHSU`.**
  Same shape as `MULH`, but signed/unsigned high-half. Completed for this
  branch: `equiv_MULHSU` uses faithful static pins, no false
  opcode-shaped ArithTable axiom, and the explicit false
  `h_no_signed_mul_witness_defect : False` premise derived from
  `h_known_bugs`. Executable repro evidence confirms stock ZisK accepts and
  verifies a malicious proof for `MULHSU(-1,1)=0`.
- 🪓 **C3.4 — repair low-half `MUL` ArithTable trust shape.**
  Keep the ordinary `np = na XOR nb` branch already wired through
  `h_rd_val_mdrs_mul_low_chunked`. Finish the exceptional opposite-sign
  `np = 0` branches without `arith_table_op_mul_mode_pin`.
  Completed for trust-shape: `arith_table_op_mul_mode_pin` has been deleted
  and `.mul` is removed from `UsesOpcodeSpecificArithTableAxiom`. The
  exceptional branch remains blocked only by
  `arithMulSignedWitnessSoundness`. Executable repro evidence now confirms
  the low-MUL malicious shape reaches proof verification in pre-fix ZisK
  (`0142ab5d7`), and the same demo branch confirms the corresponding
  high-half `MULH` and `MULHSU` shapes.
- 🪓 **C3.5 — repair and unblock `MULW`.**
  Stop using static-ROM `sext = 0`; use real W-mode sign-extension /
  operand evidence. Remove `arith_table_op_mulw_mode_pin` from the proof
  closure and remove `.mulw`.
  Completed: `equiv_MULW` consumes `arith_table_op_mulw_basic_mode_pin`
  only for true static pins, uses `h_sext_choice` for result
  sign-extension, derives operand high-chunk zeroes from the operation bus
  and `transpile_MULW`, and `.mulw` is no longer in
  `UsesOpcodeSpecificArithTableAxiom`.

**C3 done criteria (current branch):**
- no ArithMul-family constructor remains in
  `UsesOpcodeSpecificArithTableAxiom`;
- no ArithMul proof closure depends on a false/static-overstrong
  `arith_table_op_*` axiom;
- `MUL`, `MULH`, and `MULHSU` are allowed to be proved only under the
  explicit false `arithMulSignedWitnessSoundness` exclusion; this is the
  visible theorem-interface marker that the current circuit is buggy;
- `docs/fv/defects.md` distinguishes ArithTable trust-shape retirement from
  the signed-MUL witness soundness defect.

Future upstream-fix work is not part of C3 completion in this branch. When
the circuit rejects the malicious signed-MUL witness family, remove the
false premise, shrink `Defects.MaliciousSignedMulWitnessShape`, and prove
`MUL`, `MULH`, and `MULHSU` non-vacuously from the fixed constraints.

### C4 — ArithDiv/Rem checklist

C4 owns only these constructors:
`divu`, `remu`, `div`, `rem`, `divuw`, `remuw`, `divw`, `remw`.

- 🪓 **C4.1 — unblock `DIVU` and `REMU`.**
  Confirm both wrappers use `arith_div_table_lookup_sound` plus faithful
  unsigned non-W projections. Remove `.divu` and `.remu` from
  `UsesOpcodeSpecificArithTableAxiom`.
  Completed: both closures contain `arith_div_table_lookup_sound`,
  `arithDiv_circuit_completeness`, `arith_div_remainder_bound_unsigned`,
  `range_bus_sound`, `main_external_arith_emission_bundle`, and their
  transpiler axiom; no opcode-shaped ArithTable axiom remains.
- 🪓 **C4.2 — unblock non-W signed `DIV` and `REM`.**
  Keep genuinely dynamic sign/remainder facts classified as Binary-side /
  `assumes_operation` facts, not static ArithTable facts. Confirm no false
  static ArithTable shortcut remains; remove `.div` and `.rem`.
  Completed: `equiv_DIV` and `equiv_REM` still consume
  `arith_table_op_div_rem_signed_d_sign_pin`, signed dividend/divisor MSB
  pins, and the signed remainder-bound fact, but those are classified as
  dynamic C6-deferred row/range/bus facts rather than false static
  ArithTable projections. `.div` and `.rem` are no longer in
  `UsesOpcodeSpecificArithTableAxiom`.
- 🪓 **C4.3 — repair and unblock unsigned W-mode `DIVUW` and `REMUW`.**
  Stop using static-ROM `sext = 0`; use real W-mode sign-extension /
  operand evidence. Remove `.divuw` and `.remuw`.
  Completed: `equiv_DIVUW` and `equiv_REMUW` no longer consume
  `arith_table_op_div_rem_unsigned_w_mode_pin` or `sorryAx`. Their closures
  consume the dynamic `arith_table_op_divw_operand_pin` and
  `arith_div_remainder_bound_unsigned_w` facts, plus
  `arith_div_table_lookup_sound`, `arithDiv_circuit_completeness`,
  `range_bus_sound`, `main_external_arith_emission_bundle`, and the relevant
  transpiler axiom. `.divuw` and `.remuw` are no longer in
  `UsesOpcodeSpecificArithTableAxiom`.
- 🪓 **C4.4 — repair and unblock signed W-mode `DIVW` and `REMW`.**
  Stop using static-ROM `sext = 0`; keep genuinely dynamic remainder /
  operand facts deferred to Binary lookup migration. Remove `.divw` and
  `.remw`.
  Completed: `equiv_DIVW` and `equiv_REMW` no longer consume
  `arith_table_op_div_rem_signed_w_mode_pin` or `sorryAx`. Their closures
  consume the dynamic `arith_table_op_div_rem_signed_w_d_sign_pin`,
  `arith_table_op_divw_operand_pin`, and
  `arith_div_remainder_bound_signed_w` facts, plus shared lookup/Clean/range
  boundaries and the relevant transpiler axiom. `.divw` and `.remw` are no
  longer in `UsesOpcodeSpecificArithTableAxiom`.

**C4 done criteria:**
- no Div/Rem-family constructor remains in
  `UsesOpcodeSpecificArithTableAxiom`;
- remaining Div/Rem trust items, if any, are documented dynamic
  Binary-side facts deferred to C6, not ArithTable trust-shape defects;
- no Div/Rem proof closure depends on false W-mode `sext = 0`
  static-table claims.

### C2.5 — defect framework setup (done)

C2.5 is the completed guardrail that makes the split checklists meaningful:
`Defects.NoKnownDefect` is a theorem-side hypothesis, and currently blocked
signed-MUL constructors are visible in
`Defects.MaliciousSignedMulWitnessShape`. `UsesOpcodeSpecificArithTableAxiom`
is empty after C3/C4; the remaining signed-MUL exclusions are circuit-defect
markers, not ArithTable trust-shape markers. The defect-aware theorem proves
those blocked constructors by contradiction from `h_known_bugs`, so the
public `*_except_known_defects` theorem avoids advertising false signed-MUL
coverage.

### C3/C4 implementation rules

- Do not mix C3 and C4 in one checklist item.
- Execute C3 first unless a C3 proof is blocked; if switching to C4, record
  the blocker in `clean-integration-status.md`.
- For each opcode unblocked:
  1. inspect the opcode wrapper closure;
  2. remove exactly that constructor from
     `UsesOpcodeSpecificArithTableAxiom`;
  3. update `docs/fv/defects.md` and `clean-integration-status.md`;
  4. run verification before marking the item done.
- Dynamic Div/Rem facts (`arith_table_op_div_rem_signed_d_sign_pin`,
  `arith_table_op_div_rem_signed_w_d_sign_pin`,
  `arith_table_op_divw_operand_pin`, and `arith_div_remainder_bound`) are
  C6-deferred Binary-side facts, not C3/C4 ArithTable static facts.

**Axiom policy for C3/C4:** no new opcode-specific table axioms. A single
shared temporary ArithTable lookup/permutation axiom is permitted if it
replaces the known-bad per-op table facts and is documented as the same
out-of-scope PLONK/logUp soundness boundary already accepted for other
bus/lookup classes. This is a correction to the previous "zero new
soundness axioms" rule: the final target is fewer and truer assumptions,
not the accidental preservation of a green build under false assumptions.

After C3/C4: **C5** (BinaryExtension), **C6** (Binary), then the
family-terminal phases — see "Phase sequence". The deferred dynamic
Binary-side facts retire at/after C6 with the `assumes_operation` lookup
migration.

## Universal per-AIR migration contract (every C-phase after C0)

Each phase = "apply this contract to AIR X". A phase is complete only when
every deliverable **and** verification passes.

**Deliverables:**
- **D-1 Extractor + regenerate.** Extend `pil-extract` for X's interaction
  kinds if not already covered; regenerate `build/extraction/Extraction/<X>.lean`
  (X's `Row` + `main` with constraints + channel/lookup ops). Channel
  emissions cross-checked against the hand-rolled `opBus_row_<X>` /
  memory-bus defs before those are deleted.
- **D-2 `Spec` + `Assumptions`.** `Spec` is the genuine algebraic relation
  X computes — **non-vacuous, every clause cited to a PIL line**.
  `Assumptions` minimal (prefer ranges to come from X's own lookup
  interactions, not from soundness assumptions).
- **D-3 `GeneralFormalCircuit`** with `soundness` and `completeness`
  discharged. `soundness` is **adapted from X's existing correctness proof**
  (D-REFACTOR), reshaped to the `GeneralFormalCircuit.soundness` signature —
  reuse, not rewrite. For BinaryAdd/ArithMul/ArithDiv/MemAlignByte/
  MemAlignReadByte the proof already exists in `AirsClean/<X>/Soundness.lean`
  in nearly the right shape; for Binary/BinaryExtension/Mem/MemAlign/Main the
  source material is the per-opcode `EquivCore/` proofs + `Airs/<X>/`, and
  finishing the port is real *reshaping* work of varying weight (light where
  the AIR's `Spec` ≈ its constraints — Binary, Mem; heavier for
  BinaryExtension, whose `Spec` is `True` today and must be lifted to the AIR
  level, and Main). `completeness` is **filled by the per-AIR axiom
  `<air>_circuit_completeness`** (D-COMPLETE) — declared, not proved; no
  completeness proof work in any phase.
- **D-4 `Component`** `xComponent : Component FGL`.
- **D-5 Ensemble integration.** Add X's Component to the accumulating
  ensemble via `addTable` (lookup-style channels) or `addVm` (state-handshake
  channels); discharge the assembly obligations.
- **D-6 Consumer rewiring.** Every opcode whose proof consumes X via
  `Valid_X` + hand-rolled bus rows is rewired to source X's facts from
  `Component.weakSoundness` / the ensemble. Component soundness is consumed
  via the **F-3 `circuit_norm`-normalization idiom** — a per-AIR
  `spec_via_component`-style lemma — never raw term application (which
  `whnf`-explodes). The `equiv_<OP>` for X's opcodes still typecheck; their
  conclusion shape is unchanged.
- **D-7 Hand-rolled deletion** — the **last** action of the phase, after
  D-6 and a green build: delete X's `Valid_X` record, X's circuit theorems,
  X's `*Ranges` file, X's `EquivCore/Bridge/X.lean` if fully subsumed.
  Shared infrastructure (`Airs/{Bus,OperationBus,MemoryBus}/`) is **not**
  deleted per-AIR — only at CZ.

**Verification gates (the anti-marker checks):**
- **V-1** `lake build` green; `check-all.sh` + `check-all-semantic.sh` pass.
- **V-2** `#print axioms xComponent` — zero `sorry`; the only new axiom is
  X's declared `<air>_circuit_completeness` (D-COMPLETE); zero new
  *soundness* axioms, except the explicitly named C3/C4 shared ArithTable
  lookup/permutation boundary if it replaces the known-bad opcode-specific
  table facts.
- **V-3** `Spec` reviewed: non-vacuous, clauses PIL-cited, `@[reducible]`.
- **V-4** `xComponent` is reachable from `zisk_riscv_compliant_program_bus`'s
  dependency graph (anti-orphan — the substance check).
- **V-5** `trust/baseline-equiv-axiom-deps.txt` diff: every opcode that
  consumed X has its *soundness*-axiom closure shrink or hold; the one
  permitted addition is X's `<air>_circuit_completeness` axiom.
- **V-6** Axiom-retirement claim, if any, is named and proven per the
  anti-marker discipline (`#print axioms` on the global theorem;
  `.shrinkage-floor` decremented). Most phases: "retires 0 axioms" — stated.
- **V-7** Phase LoC delta recorded in the running ledger.

## Phase sequence

The old C0-CZ names remain useful as historical labels, but current work is
tracked by terminal phases T1-T7. Each terminal phase follows the Binary
lesson: prove concrete Clean provider rows, prove row-native opcode bridges,
thread canonical dispatch, then retire named trust-ledger entries only after
`#print axioms`/V2 closure proves they are gone.

| Phase | Family / action | Primary opcodes or providers | Retires when complete |
|---|---|---|---|
| **T1** | Binary-family terminal op-bus/table cleanup | `SUB`, `SLT`, `SLTU`, `SLTI`, `SLTIU`, shifts, W-shifts, Binary/BinaryExtension tables | `op_bus_permutation_sound` if last consumer, `bin_table_consumer_wf`, `bin_ext_table_consumer_wf` |
| **T2** | BinaryAdd/simple add family | `ADD`, `ADDI`, classify `ADDW/SUBW/ADDIW` ownership | BinaryAdd-specific row/bus/range trust that disappears from canonical closure |
| **T3** | Control-flow/no-memory family | branches, `JAL`, `JALR`, `LUI`, `AUIPC`, `FENCE` | Main/control-flow bus-shape or emission trust, if no longer live |
| **T4** | Memory-family terminal phase | loads/stores, Mem, MemAlign*, MemAlign ROM | memory-bus lookup/emission axioms, MemAlign permutation/ROM axioms |
| **T5** | Arith-family terminal phase | `MUL*`, `DIV*`, `REM*`, ArithTable | Arith lookup/table/range facts not protected by explicit known defects |
| **T6** | Range-bus terminal phase | byte and signed range facts across families | `range_bus_sound`, `signed_range_bus_sound` |
| **T7** | Final ensemble re-root/deletion pass | full RV64IM-supported ensemble | residual hand-rolled bus/permutation/range/lookup scaffolding |

### T1 detail — current active phase

- 🪓 T1.1 Clean balance projects active Main op-bus rows to concrete
  Binary-family provider rows.
- 🪓 T1.2 lookup-aware Binary provider rows carry direct static
  BinaryTable lookup facts.
- 🪓 T1.3 canonical bitwise arms
  `AND/OR/XOR/ANDI/ORI/XORI` consume static-provider rows.
- 🪓 T1.4 retired `binary_per_byte_lookup_witness` and
  `binary_b_op_or_sext_eq_op_general`.
- 🪓 T1.5 migrate remaining Binary table consumers:
  `SUB`, `SLT`, `SLTU`, `SLTI`, `SLTIU`.
- 🪓 T1.6 migrate BinaryExtension/shift-family table consumers.
- 🪓 T1.7 retire `op_bus_permutation_sound` if no global consumer remains;
  otherwise record the exact remaining consumer family.
- 🪓 T1.8 retire `bin_table_consumer_wf` and
  `bin_ext_table_consumer_wf`, or record their exact remaining consumers.

### T2 detail — BinaryAdd/simple add

- ☐ T2.1 expose/load-bearing BinaryAdd component row facts with the same
  singleton-channel extractor pattern used in T1, including evaluated Clean
  op-bus message bridges back to legacy `matches_entry`.
- ☐ T2.2 prove row-native `ADD`/`ADDI` write-value bridges over concrete
  Clean BinaryAdd rows; do not introduce output-value promise hypotheses.
- ☐ T2.3 thread canonical `ADD`/`ADDI` wrappers, `OpEnvelope`, and dispatch
  through the Clean row route.
- 🪓 T2.4 classify `ADDW/SUBW/ADDIW` by actual provider/table dependency and
  reuse T1's lookup-aware Binary route where needed.
- 🪓 T2.5 regenerate trust ledgers and record/retire exact remaining
  `op_bus_permutation_sound` and `bin_table_consumer_wf` consumers by
  global/V2 closure.

### T3 detail — control-flow/no-memory

- ☐ T3.1 classify branch, jump, U-type, and `FENCE` channel use.
- ☐ T3.2 expose Main/control-flow row facts from Clean Main rather than
  hand-rolled Main pin bundles where possible.
- ☐ T3.3 thread branch opcodes through row-native Main/control-flow routes.
- ☐ T3.4 thread `JAL/JALR/LUI/AUIPC` through row-native routes while
  preserving register-write/memory-bus shape.
- ☐ T3.5 keep `FENCE` under `h_known_bugs` until the documented ZisK FENCE
  support defect is resolved.
- ☐ T3.6 regenerate trust ledgers and record exact remaining Main/control-flow
  bus-shape or op-bus consumers.

### T4 detail — memory

- ☐ T4.1 assemble Main/Mem/MemAlignByte/MemAlignReadByte/MemAlign/static ROM
  providers.
- ☐ T4.2 prove Clean balance gives concrete memory provider rows matching
  active Main memory interactions.
- ☐ T4.3 signed-load spike: prove the `LB` chain from memory provider row
  bytes to lookup-aware BinaryExtension sign-extension row to Sail result.
- ☐ T4.4 prove row-native load routes for
  `LD/LB/LH/LW/LBU/LHU/LWU`.
- ☐ T4.5 prove row-native store routes for `SB/SH/SW/SD`.
- ☐ T4.6 replace signed-load `LB/LH/LW` uses of
  `bin_ext_table_consumer_wf` with exact lookup-aware BinaryExtension
  provider-row facts, tied to the same Main load result as the memory
  provider row.
- ☐ T4.7 retire `lookup_consumer_matches_provider_load` and the
  `main_*_emission_bundle` memory axioms when canonical closures lose them.
- ☐ T4.8 retire MemAlign permutation/ROM axioms only after direct ROM
  membership proves the same provider-row facts.

### T5 detail — arith

- ☐ T5.1 build lookup-aware ArithMul/ArithDiv component routes that emit the
  same ArithTable rows used by opcode proofs.
- ☐ T5.2 build exact 74-row static ArithTable provider projections.
- ☐ T5.3 prove row-native non-defective `MUL/MULHU/MULW` facts from the same
  Arith provider rows that balance the Main channel interaction, without
  opcode-shaped ArithTable axioms.
- ☐ T5.4 keep signed-MUL defects explicit through `h_known_bugs` until the
  circuit/witness issue is fixed upstream.
- ☐ T5.5 prove row-native non-defective `DIV/REM` facts and keep documented
  dynamic defects explicit.
- ☐ T5.6 retire remaining Arith lookup/table/range axioms from global
  closure, or record exact remaining consumers when a defect/later family
  keeps one live.

### T6/T7 detail — range and final ensemble

- ☐ T6.1 enumerate last consumers of `range_bus_sound` and
  `signed_range_bus_sound`.
- ☐ T6.2 replace each with row/static-table/local component facts from the
  relevant family, tied to the same concrete provider rows used by the
  channel/matches proof.
- ☐ T6.3 retire both range-bus axioms once global closure loses them.
- ☐ T7.1 define the full Clean ensemble statement for supported RV64IM.
- ☐ T7.2 prove constructibility modulo explicit `h_known_bugs`.
- ☐ T7.3 re-root canonical theorem closures on the ensemble statement without
  reintroducing row-local promise hypotheses under new names.
- ☐ T7.4 delete dead hand-rolled bus/permutation/range/lookup scaffolding.
- ☐ T7.5 update docs and trust ledgers so the remaining trust splits into
  irreducible transpiler/Sail axioms, sanctioned completeness axioms, and
  explicit known-defect hypotheses.

**Final re-root warning.** The re-root remains invalid until the ensemble
`Statement` is constructible for real traces. A theorem of shape
`Statement -> Spec` with an unsatisfiable `Statement` is vacuous; T7 must
include the constructibility proof, not just a green `lake build`.

## Risk register

| # | Risk | Mitigation |
|---|---|---|
| R-1 | "Axiom retired" used as a marker (rename/intermediate-lemma). | V-6: named axiom, gone from the **global theorem**'s `#print axioms`, `.shrinkage-floor` decremented same-PR. |
| R-2 | Orphan-Component trap (the exact prior failure). | V-4: Component must be reachable from `zisk_riscv_compliant_program_bus`. |
| R-3 | A phase deletes shared/hand-rolled code an unmigrated opcode still imports. | D-7 is the **last** phase action, after D-6 + green build. Shared `Airs/{Bus,OperationBus,MemoryBus}/` only deleted at CZ. |
| R-4 | The ~10 completeness axioms (D-COMPLETE) are mistaken for a soundness regression, or smell like laundering. | **They are user-sanctioned — see "Axiom policy".** A *declared, ledgered, non-security-critical* class — own allowlisted file, `trusted-base.md` entry, separate count. Soundness does not depend on them. An open axiom is the honest choice vs a vacuous `ProverAssumptions := False` proof. The sanction covers leaving completeness *unproven*, NOT stating it falsely — each completeness axiom must be a faithfully-stated, true proposition. |
| R-5 | Re-root vacuity: unsatisfiable ensemble `Statement` ⟹ silently-vacuous theorems. | C0 Z-ROOT spikes it for ADD; CZ carries an explicit constructibility lemma; reviewer confirms (build cannot). |
| R-6 | ~~`decide`/`native_decide` blows up on the 74-row ArithTable `StaticTable`~~ — **resolved.** | C0e built the `StaticTable` spike and the real 74-row ArithTable `StaticTable` (`AirsClean/ArithTable.lean`) with a tractable `contains_iff`. The former `arith_table_content` fallback axiom is withdrawn (D-ROM) — a new axiom is not permitted (Axiom policy). |
| R-7 | The skeleton `AirsClean/<X>/Soundness.lean` files (C5/C6/C8/C9/C11) must be completed. | **Not from-scratch** (D-REFACTOR): the source proofs exist (per-opcode `EquivCore/`, `Airs/<X>/`); the work is *reshaping* them into AIR-level Component soundness. Effort varies — BinaryExtension and Main are heaviest. Ordered into the interior so the BinaryAdd pattern is proven first. |
| R-8 | ~~`circuit_proof_start` does not compose with `FGL`~~ — **resolved** (finding F-1). Live form: consuming a Component's / the ensemble's `soundness` raw-`whnf`-explodes on the circuit `operations`. | Finding F-3: the `circuit_norm`-normalization idiom (`spec_via_component` template). Cracked for the per-Component case in C0d. The CZ ensemble-level re-root must re-confirm the idiom holds against `Ensemble.Soundness` — Clean's `FibonacciWithChannels` consumes ensemble soundness, so it is expected to; if not, surface it (D-STOP applies to CZ too). |
| R-9 | Transitional coexistence — global theorem must stay green while AIRs are half-migrated. | Per-opcode theorems are independent; conclusion shape stays stable; shared axioms persist until family-terminal; trust gate green every phase **only after known-false axioms are quarantined or replaced by honest shared boundaries**. Green under a known-false trust ledger is not a completion marker. |
| R-11 | Per-op lookup facts get reintroduced under new names. | C3/C4 axiom policy: table lookup soundness is represented once, at row/table or ensemble-channel level. Opcode-specific facts must be theorems from `ArithTableSpec` plus finite-table projections. |
| R-10 | The extractor extension for cross-row/lookup shapes is itself hard. | Staged per D-EXT — extractor extended one interaction-kind at a time, each validated on one AIR before reuse. |

## Verification

**Per phase:** `nix develop --command lake build`; `trust/scripts/check-all.sh`;
`nix develop --command trust/scripts/check-all-semantic.sh`; the V-1…V-7
gates above; commit + tag (`phase-C<N>-<air>-clean-component`).

**End of epic (CZ):**
- `nix run .#test` green.
- `#print axioms zisk_riscv_compliant_program_bus` lists ~67: ~57
  soundness-critical (all in `Trusted/Transpiler.lean` or the Sail-spec
  files — the bus/range/lookup axioms are gone) plus ~10
  `<air>_circuit_completeness` axioms (the declared non-security-critical
  class). `trust/.shrinkage-floor` and `docs/fv/trusted-base.md` updated to
  reflect both classes, kept visibly separate.
- Every `AirsClean/<AIR>/` Component is reachable from the global theorem;
  no `AirsClean/` file is orphan.
- The ensemble `Statement` constructibility lemma is proven and reviewed.
- `grep -rn 'bus_effect' ZiskFv/` shows only the retained Sail-bridge core;
  `Airs/{Bus,OperationBus,MemoryBus}/` and `BusShape*` are deleted.
- Net-LoC reckoned (expected ≤ 0).
- `CLAUDE.md`, `docs/fv/*`, agent memory updated.

## Critical files

**Clean library (reference, untouched):** `build/clean-lean/Clean/Air/{Balance,FlatComponent,FlatEnsemble,Vm}.lean`, `Clean/Circuit/{Lookup,LookupCircuit,Channel}.lean`.

**Extractor:** `tools/pil-extract/src/main.rs` (extended per D-EXT); `build/extraction/Extraction/<AIR>.lean` (regenerated output).

**Per-AIR (×10):** `ZiskFv/AirsClean/<AIR>/{Row,Constraints,Spec,Soundness,Circuit}.lean`; the new `AirsClean/Channels/` channel + ensemble files.

**Hand-rolled layer (progressively deleted):** `ZiskFv/Airs/{Bus,OperationBus,MemoryBus}/`, `ZiskFv/Airs/BusShape*`, the `Valid_<AIR>` records and `*Ranges` files under `Airs/{Arith,Binary,Main}/` and `Airs/Mem*`.

**Re-root (CZ):** `ZiskFv/Channels/StateEffect.lean`, `ZiskFv/SailSpec/BusEffect.lean` (Sail-bridge core retained), `ZiskFv/Compliance.lean`, `ZiskFv/EquivCore/` per-opcode proofs + `EquivCore/Bridge/`.

**Trust:** `trust/baseline-axioms.txt`, `trust/.shrinkage-floor`, `trust/baseline-equiv-axiom-deps.txt`, `trust/scripts/check-all*.sh`.
