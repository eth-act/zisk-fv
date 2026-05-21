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

**The 104 axioms** (`trust/baseline-axioms.txt`):
- ~52 `transpile_<OP>` (`ZiskFv/Trusted/Transpiler.lean`) — **irreducible**.
- ~5 Sail-spec (`SailSpec/Auxiliaries.lean` ×4, `ZiskCircuit/MemModel.lean`
  ×1) — **irreducible**.
- ~47 in scope: `op_bus_permutation_sound` (1), memory-bus emission (~9,
  `MemoryBus/MemBridge.lean`+`MemAlignBridge.lean`), range-bus (2,
  `Channels/RangeBusSoundness.lean`), lookup-table (2, `Tables/`), Binary
  per-AIR pins (~6), `Arith/Ranges.lean` arith-table/msb pins (~27 — ROM
  content + circuit-fact pins, discharged via `StaticTable` + the Arith
  Components' soundness, not via balance).

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
  throughout. Existing proof content moves and gets wrapped; it is never
  duplicated or discarded (this is also what keeps the net-LoC heuristic
  honest). There is **no new soundness-direction proof work**: `soundness`
  is adapted from existing proofs, and the retired axioms are wired in from
  Clean's already-proven `Balance`/`StaticTable` theorems. `completeness`
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

## Status and corrections (current — 2026-05-21)

Execution has reached C4, and an investigation has refined the
arith-table scope. **This section is the live current state and the
entry point for whoever continues the epic.**

### Done and verified
- **C0, C1 (MemAlignByte), C2 (MemAlignReadByte)** — done, independently
  verified (`lake build` green; V1 + V2 trust gates pass; the Components
  are load-bearing on `zisk_riscv_compliant_program_bus`). On branch
  **`clean-air-integration`** (pushed to `eth-act/zisk-fv`, HEAD `b390eeb`).
- The carry-chain Components for **C3 (ArithMul)** and **C4 (ArithDiv)**,
  and the faithful 74-row ArithTable `StaticTable`
  (`ZiskFv/AirsClean/ArithTable.lean`, cross-checked 0-mismatch against
  `arith_table_data.rs`), are built and merged on branch
  **`arith-batch-complete`** — the base for the next step.

### The arith-table soundness defect (the C3/C4 completion fixes it)
The 19 `arith_table_op_*` axioms in `ZiskFv/Airs/Arith/Ranges.lean` were
all introduced by **one commit — `14d4bff`, PR #26, 2026-05-14** (recent
agent work, not long-standing trust). A programmatic cross-check against
the 74-row ROM found **4 are provably false** — each pins a ROM column
to a value the ROM ranges over:

| False axiom | False claim | ROM reality |
|---|---|---|
| `arith_table_op_mul_mode_pin` | `na=nb=np=0`, op 180 | `na/nb/np ∈ {0,1}` |
| `arith_table_op_mulw_mode_pin` | `sext=0`, op 182 | `sext ∈ {0,1}` |
| `arith_table_op_div_rem_unsigned_w_mode_pin` | `sext=0`, op 188/189 | `sext ∈ {0,1}` |
| `arith_table_op_div_rem_signed_w_mode_pin` | `sext=0`, op 190/191 | `sext ∈ {0,1}` |

A false axiom makes its consumers vacuous — `equiv_MUL`, `equiv_MULW`,
`equiv_DIVW/REMW/DIVUW/REMUW` are vacuous for the excluded operand
cases. **The verification is, as it stands, unsound.** The C3/C4
completion deletes these 4 and reproves the 6 opcodes soundly.

### C3/C4 scope — 16 retired now, 3 deferred (user-confirmed 2026-05-21)
An investigation cross-checked all 19 `arith_table_op_*` axioms against
the ROM. Of the 19:

- **16 are retired by the C3/C4 completion** (the immediate next step):
  - **12 are true ROM facts**, derived from `arithTable`'s
    `StaticTable.contains_iff` by a 74-row case split + the `op` literal:
    the 11 mode/selector pins `arith_table_op_{mul_main_selector,
    mulhu_mode, mulhu_main_selector, mulh_mode, mulh_main_selector,
    mulhsu_mode, mulhsu_main_selector, div_rem_signed_mode,
    div_rem_main_selector, div_rem_unsigned_mode,
    div_rem_unsigned_main_selector}_pin`, plus `mulw_operand_pin` (its
    `a/b`-chunk facts derive from the `m32`-gated circuit `assertZero`s).
  - **4 are the false axioms** above — *deleted*, with `equiv_MUL` et al.
    reproven soundly against the true ROM facts.
  - "Retired" means **genuinely deleted, by proof** — removed from
    `Ranges.lean`, gone from `#print axioms`. Net: `baseline-axioms.txt`
    −16, `.shrinkage-floor` 109 → 93, **zero new axioms** — and the
    unsoundness is fixed.

- **3 are deferred** (genuinely cannot retire in C3/C4) —
  `arith_table_op_div_rem_signed_d_sign_pin`,
  `arith_table_op_div_rem_signed_w_d_sign_pin`,
  `arith_table_op_divw_operand_pin`. They assert facts about the
  **remainder `d`-chunks**, which are *not columns of the 15-slot arith
  ROM*; they follow from the `assumes_operation` Euclidean-bound lookup
  (`arith.pil:274`, `0 ≤ |d| < |b|`) — a *dynamic op-bus lookup into the
  Binary AIR*, not a static ROM, whose soundness is the separate
  `arith_div_remainder_bound` axiom family (`Ranges.lean:692-773`).
  These 3 are **true, faithful axioms — not the unsoundness.** They
  cannot retire until the Binary AIR is a Component (C6) and the
  `assumes_operation` lookup is migrated; they retire then, by deletion,
  alongside the `arith_div_remainder_bound` family. C3/C4 leaves them in
  place, untouched.

### Immediate next action — complete C3/C4 (the 16-axiom scope)
Branch from `arith-batch-complete`. For **both** the ArithMul and
ArithDiv Components:
1. Extend the Component `main` to emit the `arith_table_assumes` ROM
   lookup against the 74-row ArithTable `StaticTable`
   (`AirsClean/ArithTable.lean`) — alongside the carry-chain
   `assertZero`s already present.
2. Extend the Component `soundness` to consume `StaticTable.contains_iff`
   — so the per-op mode/sign-witness column values are *derived inside
   `soundness`* from ROM membership. Mechanism: `StaticTable.toTable`
   (`Clean/Circuit/Lookup.lean:141`) sets `Soundness := table.Spec`,
   exposed in `soundness` via the `lookup` case of
   `ConstraintsHold.Soundness` (`Operations.lean:694`) — no axiom.
3. Delete the **16** retireable `arith_table_op_*` axioms from
   `Airs/Arith/Ranges.lean`; rewire consumers to the Component
   soundness / the `StaticTable`.
4. Reprove `equiv_MUL/MULW/DIVW/REMW/DIVUW/REMUW` soundly — the 4 false
   axioms are gone, so the proofs must not rely on the false facts (MUL's
   low 64 bits are sign-agnostic — the sound proof needs no `na=0`).
5. Leave the **3** deferred axioms in place, untouched.
6. Verify: `lake build` green; V1 + V2 gates pass; `#print axioms
   zisk_riscv_compliant_program_bus` lists none of the 16; `.shrinkage-floor`
   109 → 93; zero new axioms; `equiv_MUL` et al. non-vacuous (their
   `#print axioms` routes through the Arith Component, not ex-falso).

**Hard constraint (Axiom policy):** zero new axioms — not a "corrected"
axiom, not a consolidated `arith_table_consumer_wf`. If the
de-axiomatization genuinely cannot be done without a new axiom, STOP and
surface it; do not add one, do not `sorry`, do not leave a proof vacuous.

After C3/C4: **C5** (BinaryExtension), **C6** (Binary), then the
family-terminal phases — see "Phase sequence". The 3 deferred axioms
retire at/after C6 with the `assumes_operation` lookup migration.

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
  *soundness* axioms.
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

C0 already pins BinaryAdd. Remaining order — real-soundness AIRs first
(lower proof risk; exercise `StaticTable` on the real ArithTable early),
skeleton AIRs in the interior, cross-row AIRs late, Main last, family-
terminal phases where the shared axioms genuinely retire:

| Phase | AIR / action | Soundness today | New interaction kind for the extractor | Retires |
|---|---|---|---|---|
| **C0** | BinaryAdd pilot + 3 spikes | real | op-bus emission + Component skeleton | 0 (GO/NO-GO) |
| C1 | MemAlignByte | real | memory-bus + ROM lookup | its ROM-content axiom, if isolated |
| C2 | MemAlignReadByte | real | (covered) | 0 |
| C3 | ArithMul *(completion in progress — see Status)* | real | ArithTable (74-row) `StaticTable` lookup | MUL-family `arith_table_op_*` — its share of the 16 retired via the `StaticTable` lookup; see Status for the 16-now / 3-deferred split |
| C4 | ArithDiv *(completion in progress — see Status)* | real | ArithTable `StaticTable` lookup + signed-carry | DIV/REM-family `arith_table_op_*` — its share of the 16 retired via the `StaticTable` lookup; see Status for the 16-now / 3-deferred split |
| C5 | BinaryExtension | **skeleton, `Spec:=True`** | byte lookup | 0 — `Spec` lifted to AIR level + soundness **adapted from the existing shift-opcode `EquivCore/` proofs**; heaviest reshaping |
| C6 | Binary | **skeleton** | per-byte lookup | 0 — soundness **adapted from the existing Binary-opcode proofs** (`Spec` ≈ constraints — light) |
| **C7** | terminal-A: assemble the op-bus + Binary-family ensemble | — | — | **`op_bus_permutation_sound`, `bin_table_consumer_wf`, `bin_ext_table_consumer_wf`** |
| C8 | Mem | **skeleton** | memory bus (`addVm`) | 0 |
| C9 | MemAlign | **skeleton, cross-row** | register chain (`addVm`) | 0 |
| **C10** | terminal-B: assemble the memory ensemble | — | — | **the ~9 memory-bus axioms** |
| C11 | Main | **skeleton, cross-row PC** | PC handshake (`addVm`) | 0 |
| **CZ** | terminal-C: re-root + finish | — | — | **`range_bus_sound`, `signed_range_bus_sound`**; delete residual hand-rolled bus layer |

**C7/C11 ordering note.** `op_bus_permutation_sound`'s consumer is the Main
row (C11), but its providers are the Binary family (C5/C6). A balanced
op-bus needs both. C7 assembles the provider side with the ensemble
`verifier` slot standing in for the aggregate consumer (the
`FibonacciWithChannels` pattern); C11 refines the verifier with real Main.
**The op-bus retirement is a named deliverable pinned to whichever of
C7/C11 first makes `#print axioms` drop it** — the V-6 gate enforces it is
not claimed early.

**CZ — re-root + finish.** (1) Define the ZisK `PublicIO` and an ensemble
`Spec` that entails the 63 per-opcode equalities. (2) Re-root the 63
`equiv_<OP>` and `zisk_riscv_compliant_program_bus` on `Ensemble.Soundness`
— consuming it via the **F-3 `circuit_norm`-normalization idiom** (raw term
application of ensemble soundness will `whnf`-explode the same way bare
Component soundness does; normalize first). (3) **Constructibility
deliverable:** prove the ensemble `Statement` is
inhabited for real ZisK traces (an `EnsembleWitness` from the existing
`Valid_Main` + provider witnesses + bus rows). (4) Retire `range_bus_sound`/
`signed_range_bus_sound` (last range consumers now migrated). (5) Delete the
residual hand-rolled bus layer (`Airs/{Bus,OperationBus,MemoryBus}/`,
`BusShape*`). (6) End-of-epic reckoning: net-LoC, final axiom count
(~57 soundness-critical + ~10 completeness = ~67, cleanly split),
no-orphan, docs, agent memory.

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
| R-9 | Transitional coexistence — global theorem must stay green while AIRs are half-migrated. | Per-opcode theorems are independent; conclusion shape stays stable; shared axioms persist until family-terminal; trust gate green every phase. |
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
