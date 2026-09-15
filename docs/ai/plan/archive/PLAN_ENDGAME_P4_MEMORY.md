# PLAN — Resolve #76 (the memory-timeline argument)

**Slug:** `Endgame P4 Memory` · **Issue:** eth-act/zisk-fv#76 · **Rewritten:**
2026-06-17 (supersedes `PLAN_ENDGAME_P4_MEMORY.archive-2026-06-16.md`). **Status:**
planned, not started. Incorporates a route probe, a conservation analysis, and a
red-team that corrected the core (Fold B is store-driven + byte-local, not whole-state).

This is the **navigable spine**. Depth lives in two anchored evidence artifacts:
- Gap map: [`../research/RESEARCH_76_GAP_MAPS.md`](../research/RESEARCH_76_GAP_MAPS.md)
- Route decision + conservation + corrected Fold-B design:
  [`../research/RESEARCH_76_DESIGN.md`](../research/RESEARCH_76_DESIGN.md)
- Raw: `../research/_raw/{76-understand-maps,76-route-probe}.json`

---

## TL;DR

#76 discharges `h_memory_construction : env.memoryTimelineConstructionEvidence`
(binder #5 AND `exec_eq` conjunct #2 of `zisk_riscv_compliant_program_bus`,
`Compliance.lean:78/98`), which is `True` for 56 arms and
`LoadMemoryTimelineConstructionEvidence state bus.e1` for the **7 loads**. The genuine
trust-reducing work is a **store-driven "Fold B"**: re-scope the obligation to the
byte-local agreement it actually consumes, then prove that byte-local agreement by
induction over the prefix's **stores** (each store's memory effect comes from its own
`equiv_<store>`), with loads + non-memory ops as `.mem`-invariance. This **reduces** the
premise to a named residual; it does **not** make the theorem premise-free.

**Lead with the make-or-break spike (PR-76.0). Do not start the sequence until it
returns GO with `state` opaque, regs/PC ≠ `initialState`, and a measured strictly-
smaller residual.** A `rfl`/frozen-`initialState` "green" is the laundering trap.

---

## §1 The obligation (→ [GAP_MAPS#obligation](../research/RESEARCH_76_GAP_MAPS.md#obligation))

```
LoadMemoryTimelineConstructionEvidence state entry :=
  ∃ initialState rows (_facts : GeneratedMemReplayFacts initialState rows) priorRows laterRows,
    rows = priorRows ++ entry :: laterRows ∧ MemoryPrefixStateAlignment initialState state priorRows
```
Ingredients: traceSplit `[✓ derived]`, selectedRead `[✓ derived]`, `prefixReadSound`
`[✓ derived PR#65 — NOT the residual; wiring it buys nothing]`, alignment `[✗ THE gap]`.
**The alignment conjunct is over-strong** — see §3. Consumed by 3 dispatchers
(ldsd/misc/remaining) via pure forwarding.

## §2 Route decision (→ [DESIGN#route-decision](../research/RESEARCH_76_DESIGN.md#route-decision))

- **X** (seam/`addChannel` deep refactor): out of scope / vacuous-as-banked → the
  cross-segment **follow-on** (PR-76.5).
- **Y** (native LogUp/permutation): **dead end** (needs unproven grand-product
  soundness; why #103 used `addChannel`).
- **Z** (within-segment + named residual): **CHOSEN — genuine only via the corrected
  store-driven Fold B.**

## §3 Conservation law + corrected Fold B (→ [DESIGN#fold-b](../research/RESEARCH_76_DESIGN.md#fold-b--the-genuine-new-work-the-76-core--corrected-per-red-team))

The Sail↔circuit memory connection is **conserved** (the replay engine only
*transports* agreement). Three corrections to the naive framing:
- **P0** — `MemoryPrefixStateAlignment` is a *whole-SailState* identity (freezes regs/PC);
  the fold yields only a memory-*map* `ReplayMemoryAgreement`. **Re-scope** the alignment
  conjunct to byte-local `ReplayMemoryAgreementOnBytes … entry.ptr` (= `stateBytesAtPrefix`),
  which is all the consumer needs (a reviewable obligation-weakening; CODEOWNER flag).
- **P2** — loads **consume** read-correctness (`equiv_<load>` drops `bus_effect.1`); they
  cannot seed the fold. The producer is the **store side** (`bus_effect.2` carries the
  write). Fold B = store-driven induction; loads/non-memory = `.mem`-invariance.
- **P1** — the fold needs `stateAt (i+1) = execute step_i (stateAt i)`; `ProgramBinding`
  has no such field → a **trace-coherence premise** (likely a new named residual).

---

## §4 PR staging — CHECKLIST (keep current every progress step)

- [ ] **PR-76.0 — Make-or-break spike (GO/NO-GO).** See §5. Gates all below.
- [ ] **PR-76.1 — Per-STORE `EventReplayStep` + `.mem`-invariance.** SB/SH/SW/SD: derive
      `EventReplayStep (stateAt i) (stateAt i+1) writeEvent_i` from `equiv_<store>`
      (`bus_effect.2 = {state with mem := inserts}`, reconciled with width-gated
      `replayStoreEvent` and the nextPC `writeReg`). Loads + non-memory opcodes: the
      `.mem`-invariance step from each opcode's Sail spec. Files: new
      `ZiskFv/ZiskCircuit/MemTimeline/EventStep/*.lean`. Consumes a trace-coherence
      input (PR-76.0 decides its provenance). No new project axioms.
- [ ] **PR-76.2 — The store-fold.** Assemble consecutive `EventReplayStep`s into
      `PrefixReplayStepsFrom` → byte-local `stateBytesAtPrefix` at `entry.ptr` for an
      arbitrary load (first-access-this-segment bytes route to the seed residual),
      parameterized by the seed + trace-coherence residual. Files:
      `ZiskFv/ZiskCircuit/MemTimeline/{Ordering,Linkage,Construction}.lean`.
- [ ] **PR-76.3 — Re-scope obligation + wire 7 loads + reduce global signature.**
      Re-scope `LoadMemoryTimelineConstructionEvidence` to the byte-local conjunct
      (`OpEnvelope.lean:2346`; CODEOWNER review). Add
      `Construction{Ld,Lbu,Lhu,Lwu,Lb,Lh,Lw}.lean` (ITYPE template + memory-bus
      provider; register in `bin/TrustGate/Main.lean:245`); rewire
      `Dispatch/{LDSD,Misc,Remaining}.lean`. Reduce `h_memory_construction` **and the
      `exec_eq` conjunct** (`Compliance.lean:78/98/110/112/113`) — the public theorem
      *type* changes (P4). Refresh baselines NET REMOVAL: `baseline-{hypothesis-count,
      caller-burden,global-theorem-binders,equiv-axiom-deps}.txt`. Add the realistic
      positive witness; keep the two-address vacuity regression.
- [ ] **PR-76.4 — Stores' own residual (Spike #2).** Author `MemoryBusRowsPrefixStoreSound`
      (absent everywhere); collapse SB/SH/SW `h_m*` (SB:`h_m1..7`, SH:`h_m2..7`,
      SW:`h_m4..7`; SD none). Reuses the store `EventReplayStep`s from PR-76.1; does NOT
      touch `LoadPromises`. May run parallel to 76.2/76.3.
- [ ] **PR-76.5 — Cross-segment seed correctness (deep follow-on; likely own issue).**
      Discharge seg-k `initialAgreement` via Route X (SEGMENT_LAST-gated emission
      refactor + land `p4-103-landing`), or keep as a named residual. Seg-0 boot +
      trace coherence stay irreducible. Where #103 finally merges.

## §5 The make-or-break gate (PR-76.0)

De-risk before any build. For **one** load (LD) on a **realistic** store-then-read
same-address segment, prove the per-STORE `EventReplayStep` + the store-fold and
**construct** the (byte-local re-scoped) evidence with residual = seed `initialAgreement`
(+ trace coherence) only. **Gate conditions (all required — these defeat the laundering
shape the existing witnesses exhibit):**
1. `state` is **opaque** (`binding.stateAt i`, variable-bound) — NOT let-bound to
   `stateAfterMemoryBusRows …`.
2. regs/PC(`state`) ≠ regs/PC(`initialState`) — the prefix includes a register-mutating
   step, forcing the non-frozen case.
3. the store's `EventReplayStep` is discharged from `equiv_<store>`, not a hand-built
   `{state with mem}`.
4. `#print axioms` shows no new `ZiskFv.*` axiom; the residual is a **named hypothesis**
   about `initialState`/coherence, not a definitional `rfl`.
5. **a measured hypothesis-count delta** proving the residual is *strictly smaller* than
   the original existential.
6. **a written determination of trace-coherence status** (derivable / already-assumed /
   new named residual).

**NO-GO** if green is only reachable via `rfl`/frozen `initialState`, or the residual is
the same size. Then Route Z is laundering for #76 — stop and escalate (deep Route-X
refactor, or accept the premise as standing external trust).

## §6 Honest end-state (→ [DESIGN#the-honest-end-state](../research/RESEARCH_76_DESIGN.md#the-honest-end-state-and-surviving-residual-non-overclaim))

After PR-76.3 the global theorem takes a **named residual** (up to four parts) instead
of the construction existential:
- **(a) seg-0 boot binding** — irreducible external trust (beside `aeneasBridgeTrust`).
- **(b) seg-k cross-segment seed correctness** — the deep follow-on (PR-76.5).
- **(c) trace coherence** — `stateAt` is the Sail execution sequence (P1); likely a
  named binding of class (a).
- **(d) loads/non-memory `.mem`-invariance** — should be cheaply derivable; a small
  residual only if some opcode resists.

**Never write "premise-free."** #76 discharges the *within-segment store-driven Sail-side
timeline*; the residual is real, named, and richer than a single boot fact. Phrasing:
**"0 PROJECT (`ZiskFv.*`) axioms; Sail-translation + Lean-kernel axioms present as
documented external trust."**

## §7 Anti-laundering invariants (any violated ⇒ #76 failed, even if green)

1. Fold B GENUINE & store-driven — `stateBytesAtPrefix` *derived* from per-STORE
   `EventReplayStep`s, never re-posited; never seeded from a load's promise (circular).
2. Do not count `prefixReadSound` wiring as reduction.
3. Measure the residual (PR-76.0); baselines must NET SHRINK; same-size ⇒ STOP.
4. Non-vacuity on a realistic store-then-read with `state` opaque + regs/PC ≠
   `initialState`; never the one-row / `rfl` floor.
5. The byte-local re-scope is a reviewable obligation-weakening — CODEOWNER flag; it must
   not hide a hypothesis (consumer provably needs only the byte-local form).
6. No `SegmentLastRowTie` `h_tie` relocation into `equiv_<OP>`; no new non-`@[reducible]`
   def hiding a hypothesis; no new project axiom. Loads/stores are on
   `trust/structural-unpacking-exceptions.txt` — #76's diff must be net REMOVAL on top.

## §8 Risks

- **R1 (make-or-break):** the per-STORE `EventReplayStep` reconciliation
  (`bus_effect.2` 8-insert vs width-gated `replayStoreEvent`, plus the nextPC `writeReg`)
  may be fiddly → PR-76.0 resolves before commitment.
- **R2 (trace coherence):** if (c) is a large new residual, #76's net reduction shrinks
  → PR-76.0 must quantify it; if it dominates, rescope or escalate.
- **R3 (residual size / vacuity):** the `rfl`/frozen trap → §5 gate conditions 1–5.
- **R4 (re-scope review):** editing `OpEnvelope.lean`'s deliberately-phrased residual +
  the trust gate needs CODEOWNER sign-off → call it out in the PR-76.3 description.
- **R5 (cross-segment creep):** keep PR-76.5's deep refactor out of the core; do not
  merge `p4-103-landing` as-is.
- **R6 (drift):** docs elsewhere say "4 dispatch arms / h_memory_timeline / 28-of-63 /
  L5 DONE" — all stale; see [GAP_MAPS#corpus](../research/RESEARCH_76_GAP_MAPS.md#corpus).

## §9 What changed vs the archived plan

The archived 2026-06-16 plan framed #76 as Spike #1 (cross-segment whole-trace assembly,
gated on #103) + Spike #2 (stores) + salvage import. This rewrite: (a) the cross-segment
seam is the *follow-on*, not the core; (b) the core is a **store-driven Fold B**
(per-store `EventReplayStep` induction to byte-local agreement) — which the old plan did
not identify, and which a red-team corrected from a wrong whole-state framing; (c)
"wiring `prefixReadSound`" is a non-reduction; (d) salvage import would regress (reuse
main); (e) the honest deliverable is a **partial** discharge to a richer named residual
(boot + cross-segment seed + trace coherence + invariance), not a premise-free theorem.
