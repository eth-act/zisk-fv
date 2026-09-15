# RESEARCH_76_DESIGN — route decision + Fold-B design for issue #76

**Provenance.** Route probe (workflow `wz8mdh1kk`, raw:
[`_raw/76-route-probe.json`](_raw/76-route-probe.json)); conservation/anti-laundering
analysis (agent `af14e75c`); and a **red-team of the written plan** (agent
`a5722e77`, 2026-06-17) that corrected the Fold-B framing — **its corrections are
incorporated below.** Evidence base:
[`RESEARCH_76_GAP_MAPS.md`](RESEARCH_76_GAP_MAPS.md). Consumed by the plan spine
[`../plan/PLAN_ENDGAME_P4_MEMORY.md`](../plan/PLAN_ENDGAME_P4_MEMORY.md).

> The two design-generation workflow stages failed twice (the nested `prBreakdown`
> StructuredOutput schema is the consistent failure point; flat-output probe/reader/
> critic agents all succeeded). The route probe + conservation analysis + red-team ARE
> the design inputs; the PR breakdown is synthesized from them.

## Route decision

| Route | Mechanism | Verdict |
|---|---|---|
| **X** — #103 seam / `addChannel` | add `SeamContChannel`; balance forces the seam via `boot_chain_derived_generalN` | **OUT OF SCOPE / vacuous-as-banked.** route-b emits per-row ungated → balances only for one-row-per-segment traces. Making it real = the deep SEGMENT_LAST-gated refactor (new MemRow selector col, ~145 Balance projections, airval↔column bridge, discharge `SegmentLastRowTie` from Spec). Consuming the conditional `h_tie` into `equiv_<OP>` is forbidden relocation. → the cross-segment **follow-on**, not the #76 core. |
| **Y** — native LogUp / permutation | consume the existing `permutation_every_row` / im_direct balance | **DEAD END.** The boundary equality needs the multiset-equality⇒tuple-equality (inverse-sum LogUp soundness / Schwartz-Zippel over `std_alpha`/`std_gamma`) — a grand-product argument the project does not prove. `permutation_every_row` is *carried but never consumed semantically* on main. #103 chose `addChannel` **specifically** to avoid this, and that choice was necessary. |
| **Z** — within-segment + named residual | choose the existential witness per-segment; prove the within-segment (byte-local) agreement; name the residual | **CHOSEN — but genuine ONLY if it proves the corrected store-side Fold B** (below). Otherwise it is laundering. |

## The conservation law (the crux — read before trusting any "reduction")

`stateBytesAtPrefix_of_memoryPrefixStateAlignment` (`Construction.lean:33-51`)
produces the only Sail↔circuit fact loads consume from exactly two seed inputs:
`h_alignment` and `facts.initialAgreement` (∀-address, `MemTrace.lean:106`). The
propagation engine `replayAgreement_after_memoryBusRows` (`MemTrace.lean:1247`) **only
transports agreement forward — it manufactures none.** Therefore the Sail↔circuit
memory connection is a **conserved quantity**: it must be supplied at the seed, and the
choice of `initialState` only *repartitions* it.

Two corollaries that kill naive versions of Route Z:
- **`initialState := {state with mem := circuit-initial-memory}`** ⇒ `initialAgreement`
  trivial (rfl), but `h_alignment` becomes an *unprovable* full-state identity.
- **"Wire the already-derived `prefixReadSound`"** ⇒ buys **nothing**. The FullWitness
  builders (`Balance.lean:9070-9320`) already derive `prefixReadSound` and already take
  the Sail-side fact (`h_stateBytesAtPrefix`) as the *undischarged parameter*.
  `prefixReadSound` was never the residual.

## Fold B — the genuine new work (THE #76 core) — CORRECTED per red-team

A first framing ("induct per-opcode `EventReplayStep` → whole-state
`MemoryPrefixStateAlignment`") is a **non-sequitur**. Corrected:

- **P0 (type mismatch).** `MemoryPrefixStateAlignment initialState state priorRows :=
  state = stateAfterMemoryBusRows initialState priorRows` (`Construction.lean:28`) is a
  **whole-SailState** identity that *freezes regs/PC at `initialState`* (the fold
  touches only `.mem`, `MemTrace.lean:760`). `EventReplayStep` /
  `replayAgreement_of_prefixReplayStepsFrom` (`MemTrace.lean:122/154`) yield a
  **memory-MAP** `ReplayMemoryAgreement`, not a SailState identity — so the fold does
  not produce the whole-state alignment for a real mid-segment load. Forcing it via
  `initialState := {state with mem := rolled-back}` makes `initialAgreement` *false*
  for real programs (state.mem carries the whole image, not zeros+one-carry).
  **FIX: re-scope the obligation's alignment conjunct from whole-state
  `MemoryPrefixStateAlignment` to the byte-local `ReplayMemoryAgreementOnBytes state
  (replayMemoryAfterBusRows initialMemory priorRows) entry.ptr.toNat`
  (= `stateBytesAtPrefix` directly).** The whole-state strength is *gratuitous* —
  `stateBytesAtPrefix_of_memoryPrefixStateAlignment` already discards all but the 8
  bytes. This is a reviewable WEAKENING of the residual def to exactly what the consumer
  needs (it hides nothing) — but it edits `OpEnvelope.lean`'s deliberately-phrased
  `LoadMemoryTimelineConstructionEvidence` and touches the trust gate
  (`baseline-global-theorem-binders.txt`, `forbidden-param-shapes`), so flag it for
  CODEOWNER review.

- **P2 (loads CONSUME, don't PRODUCE).** A load's read-value correctness is *exactly*
  what #76 must derive; `equiv_<load>` drops `bus_effect.1` (the read-agreement) and
  concludes `execute = bus_effect.2`, consuming correctness from
  `promises.memory_timeline.memoryTraceAgreement`. So **loads cannot seed the fold.**
  The genuine producer is the **store side**: `bus_effect.2` for a store is `{state
  with mem := inserts}` (`BusEffect.lean:96`), so `equiv_<store>` genuinely exposes
  "Sail store effect = circuit write." The corrected fold is a **store-side
  induction**: per-STORE `EventReplayStep` (from `equiv_<store>`), loads + non-memory
  ops as `.mem`-invariance, assembled into byte-local `stateBytesAtPrefix` at the read
  address. (At a first-access-this-segment read address the byte routes to the seed
  `initialAgreement` instead.)

- **P1 (trace coherence — a likely NEW residual).** Building `EventReplayStep (stateAt
  i)(stateAt i+1) event_i` needs `stateAt (i+1) = execute step_i (stateAt i)`.
  `ProgramBinding` (`AcceptedTrace.lean:62`) has **no coherence field**, and single-step
  equivs prove only what executing step i *produces*, not that it equals the
  independent `stateAt (i+1)`. So Fold B rests on a **trace-coherence premise** not
  currently available. Its status (derivable / already-assumed elsewhere / a new named
  residual of the seg-0-boot class) is a **PR-76.0 deliverable** and may enlarge the
  honest residual.

**Net corrected #76 core:** re-scope to byte-local + per-STORE `EventReplayStep` from
`equiv_<store>` + the store-fold to `stateBytesAtPrefix` + `.mem`-invariance steps,
under an explicit trace-coherence premise. Still genuinely unbuilt (zero producers of
the replay-step machinery exist outside the 4 def files), still the trust-reducing
content — but **store-driven and with a richer residual** than the first framing.

## Scope choice: per-segment (P, = #76) vs whole-trace (W, = deep)

- **Choice W (whole-trace):** `initialAgreement` collapses to seg-0 boot only (smallest
  residual) BUT `prefixReadSound` must hold whole-trace → deep cross-segment circuit
  assembly (Route X). **Not #76.**
- **Choice P (per-segment, = #76):** `prefixReadSound` per-segment already derived
  (firstSegment / previousSegmentInitialMemory families, `Balance.lean:8348-8766`).
  Fold B over this segment's steps; residual = per-segment seed `initialAgreement`
  (byte-local at the read addresses) + trace coherence.

## The honest end-state and surviving residual (NON-OVERCLAIM)

After #76 (Choice P + corrected store-side Fold B + byte-local re-scope), the memory
premise reduces from the construction existential to a **named residual** with up to
four parts:
- **(a) seg-0 boot binding** — Sail boot memory (at the touched bytes) = circuit
  `firstSegment` initial memory. Program/trace binding, **irreducible external trust**.
- **(b) seg-k cross-segment seed correctness** — Sail segment-start memory (at the
  carried bytes) = the `previous_segment_*`-seeded circuit initial memory. The deep
  **Route-X / #103 follow-on**.
- **(c) trace coherence** — `stateAt (i+1) = execute step_i (stateAt i)` (P1). Status
  TBD by PR-76.0; likely a named Sail-execution binding (same class as (a)).
- **(d) loads/non-memory `.mem`-invariance** — should be cheaply *derivable* from each
  opcode's Sail spec; if any opcode resists, it is a small named residual.

**#76 is NOT premise-free and never will be from this work alone.** The reduction is
real (the within-segment store-driven Sail-side timeline) but **partial**, and the
residual is richer than a single boot fact.

## Anti-laundering invariants (any violated ⇒ #76 failed, even if green)

1. **Fold B GENUINE & store-driven.** `stateBytesAtPrefix` must be *derived* from
   per-STORE `EventReplayStep`s (themselves from `equiv_<store>`), never re-posited; do
   not seed it from a load's promise (circular).
2. **Do not count `prefixReadSound` wiring as reduction** (already done; not the residual).
3. **Measure the residual.** PR-76.0 outputs the exact residual binder shape and the
   `baseline-hypothesis-count.txt` delta; baselines must NET SHRINK. Same-size residual
   ⇒ STOP, it is laundering.
4. **Non-vacuity on a realistic instance** — a multi-row multi-segment store-then-read
   prefix where `state := binding.stateAt i` is OPAQUE (not let-bound to the replay RHS)
   and regs/PC(`state`) ≠ regs/PC(`initialState`). Never the one-row / `rfl` floor.
5. **The byte-local re-scope is a reviewable obligation weakening** — flag for CODEOWNER;
   it must not hide a hypothesis (the consumer provably needs only the byte-local form).
6. No `SegmentLastRowTie` `h_tie` relocation into `equiv_<OP>`; no new non-`@[reducible]`
   def hiding a hypothesis; no new project axiom. Phrasing: **"0 PROJECT (`ZiskFv.*`)
   axioms; Sail-translation + Lean-kernel axioms present as documented external trust"**
   — never "0 axioms".

## Synthesized PR staging (detail in the plan spine)

- **PR-76.0 — Make-or-break spike (GO/NO-GO).** Corrected store-side Fold B for ONE
  realistic store-then-read same-address segment, with `state` OPAQUE and regs/PC ≠
  `initialState`; construct the (byte-local re-scoped) evidence with residual = seed
  `initialAgreement` (+ trace coherence). Output: green construction, the EXACT residual
  shape, the hypothesis-count delta, AND the determination of trace-coherence status.
  NO-GO if green is only reachable via `rfl`/frozen `initialState`.
- **PR-76.1 — Per-STORE `EventReplayStep`** (SB/SH/SW/SD from `equiv_<store>`) +
  `.mem`-invariance for loads + non-memory opcodes.
- **PR-76.2 — The store-fold** → byte-local `stateBytesAtPrefix` for an arbitrary load,
  under the seed + trace-coherence residual.
- **PR-76.3 — Re-scope the obligation + wire the 7 loads + reduce the global signature**
  (and the `exec_eq` conjunct — P4, the public theorem type changes); refresh baselines
  (net removal); add the realistic positive witness.
- **PR-76.4 — Stores' own residual (Spike #2):** author `MemoryBusRowsPrefixStoreSound`;
  collapse SB/SH/SW `h_m*`. (The store `EventReplayStep`s from PR-76.1 feed this.)
- **PR-76.5 — Cross-segment seed correctness (deep follow-on, likely its own issue):**
  discharge seg-k `initialAgreement` via Route X (SEGMENT_LAST refactor + land #103).
  Seg-0 boot + trace coherence stay irreducible.

## Global-theorem signature progression (campaign end-state)

What discharging the memory premise does to `zisk_riscv_compliant_program_bus`, and why
two things behave oppositely.

| Milestone | Memory hypothesis |
|---|---|
| Today | `h_memory_construction : env.memoryTimelineConstructionEvidence` (the whole construction existential) |
| After #76 core | `h_mem_residual` ≈ seg-0 boot ∧ seg-k cross-segment seed ∧ trace coherence (strictly smaller) |
| After PR-76.5 (deep follow-on) | `h_mem_boot` ≈ seg-0 boot ∧ trace coherence |
| Irreducible floor | a **program-boot memory binding**: the loaded image = the circuit's committed initial memory |

**Why the memory premise can never vanish (conservation).** The replay machinery only
*transports* memory agreement forward — it never *creates* it (`replayAgreement_after_memoryBusRows`,
`MemTrace.lean:1247`). The fact "the circuit's committed memory = what the program
loaded/computed" must be injected at the seed. #76 derives the part internal to the
trace; what remains is statements *about the program/trace*, not about `Valid_Mem`:
(a) the boot image binding (same trust class as `aeneasBridgeTrust`), and (b) the
cross-segment seed (whose only mechanism is ZisK's permutation, needing unproven
grand-product soundness). No Lean proof from the circuit constraints produces these.

**Why `env` CAN vanish (it is scaffolding, not trust).** `env : OpEnvelope` only
*packages* per-opcode structural facts that are themselves *derivable* from a committed
trace (the `construction_<op>_sound` theorems do exactly this, 30/63 today). Removing it
is the explicit goal of P5 (trace-level export) + P6 (OpEnvelope retirement, issue #61).

**Honest campaign end-state:** roughly
`compliant (committedTrace) (h_balanced) (h_aeneas) (h_mem_boot) (h_known_bugs)` — **no
`env`**, but still the genuine external-trust inputs (proof-system balance, Aeneas
bridge, program-boot memory binding, known-defect freedom). It does NOT become an
unconditional theorem.
