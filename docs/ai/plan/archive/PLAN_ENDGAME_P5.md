# PLAN — P5: deriving `env` (trace-level export theorem)

**Slug:** `Endgame P5` · **Issues:** eth-act/zisk-fv#61 (umbrella, step 5) + #74
(instantiation witness) · **Written:** 2026-06-17 · **Status:** planned, not started.

Navigable spine. Depth: [`../research/RESEARCH_DERIVE_ENV.md`](../research/RESEARCH_DERIVE_ENV.md)
(scope sweep) + [`../research/RESEARCH_76_DESIGN.md#global-theorem-signature-progression-campaign-end-state`](../research/RESEARCH_76_DESIGN.md)
(end-state). Raw: `../research/_raw/derive-env-scope.json`.

## TL;DR

"Deriving env" = removing the `env : OpEnvelope` binder from the global theorem by
deriving it from a committed `AcceptedTrace`. It is a **plumbing/quantification gap, not
a derivation gap**: the per-step env-free derivation already exists
(`construction_<op>_sound`, 30/63, bypasses env), decode already exists (`op i.val`), and
the two conclusion forms are `rfl`-equal. The work is the **assembly layer**: a
trace-level `∀ i, exec_eq_at trace binding i` theorem that case-splits on the decoded op
and dispatches each arm to its construction. **env is scaffolding and CAN go; the theorem
does NOT become unconditional** (it keeps proof-system balance, Aeneas bridge, memory
residual, NoKnownDefect, + exec/next-PC residuals).

## ⚠ The scope decision (resolve FIRST — see §1)

- **A — full env-free theorem:** blocked on P4=63/63 + #76 (store RMW) + XCAP/#100
  (next-PC) + `bus_effect` retirement. Far downstream; nothing buildable now.
- **B — scoped skeleton, now:** trace-level `∀ i` theorem over the 30 sound arms; 33
  missing + next-PC + exec-artifacts + store-RMW as explicit named residuals; + decode
  function + a non-vacuous multi-row witness. **The only thing buildable today.**

Recommendation: **B now** (it proves env-elimination end-to-end and collapses the
caller-burden ledger), with A as the milestone reached as P4/#76/#100 land — *provided* B
is a genuine reduction (not relocation) and is witnessed non-vacuously.

## §1 Scope (→ [DERIVE_ENV#scope](../research/RESEARCH_DERIVE_ENV.md#scope))

The full theorem (A) needs all 63 arms + bucket-(c) elimination + next-PC. The skeleton
(B) ships at 30 with the rest as named residuals. P5 must NOT silently pick B and call
#61 done — B is legitimate only if it net-shrinks the trust surface and is non-vacuous.

## §2 Mechanism (→ [DERIVE_ENV#halves](../research/RESEARCH_DERIVE_ENV.md#halves))

LEFT (env→exec_eq dispatchers, 63 arms) and RIGHT (trace→conclusion constructions, 30
arms) are bridged by quantification only — `state_effect_via_channels = bus_effect.2` by
`rfl`. Decode = `mainOfTable(trace.program, binding.mainTable).op i.val`. The assembly is
structurally the dispatchers' `cases env` rewritten as a `match on op i.val` over the
trace.

## §3 Orthogonality (→ [DERIVE_ENV#orthogonality](../research/RESEARCH_DERIVE_ENV.md#orthogonality))

env-elimination is **independent of `bus_effect` retirement**: constructions are already
env-free yet still carry the exec-bus artifacts. P5 does NOT wait on the phantom-bus
cleanup; the artifacts ride along as named residuals (P6 follow-on retires them).

## §4 PR staging — CHECKLIST (Option B; keep current)

- [ ] **PR-P5.0 — Confirm the rfl-reuse + decode primitive.** Verify a dispatcher arm's
      `state_effect_via_channels ⟨ops.exec_row,…⟩` unfolds to the construction's
      `(bus_effect …).2` (so no bridge lemma is needed). Define `decodedOp trace binding
      i := (mainOfTable trace.program binding.mainTable).op i.val` + flag projections.
      Pure projection; no new trust.
- [ ] **PR-P5.1 — `exec_eq_at` + the skeleton theorem.** Define `exec_eq_at trace
      binding i : Prop` (case on `decodedOp` → canonical per-op equation; placeholder
      `TraceArmResidual` for the 33). State `zisk_compliant_trace (trace)(binding)
      (h_aeneas)(h_mem)(h_known_bugs)(h_exec_resid)(h_nextpc)(h_arm_resid) : ∀ i,
      exec_eq_at trace binding i`; prove by `intro i; split`; dispatch the 30 to
      `construction_<op>_sound`, supplying each construction's residual binders from the
      per-step premises; discharge the 33 from `h_arm_resid`.
- [ ] **PR-P5.2 — Trace coherence as a named premise.** Add `stepCoherent : ∀ i,
      binding.stateAt i.succ = execute (decoded step i) (binding.stateAt i)` (the P1
      residual shared with #76) to `ProgramBinding` or a sibling premise, so per-step
      Sail-read binders are sourced not re-posited. Mark it a named boot-class external
      residual, not an axiom.
- [ ] **PR-P5.2c — Gap (c) / Route C: faithful `exec_row` population (XCAP #100 payoff).**
      Here the env builder sets `exec_row[1].pc := mainOfTable(…).pc (i+1)` (the real next-row
      pc), gated by `stepCoherent` — making `exec_row[1].pc = pc(i+1)` definitional. Combined
      with the #100 seam (`pc(i+1)=nextpc(row i)`) + the column↔Sail bridge, this DISCHARGES
      `h_nextPC_matches` for all 30 sound arms (sequential `pc+4`). Plan + route rationale:
      [`../research/RESEARCH_GAP_C.md`](../research/RESEARCH_GAP_C.md); cross-ref
      `PLAN_ENDGAME_XCAP.md` PR-X100.1c. (Discharges the next-PC *fact*; the exec_row *shape*
      = bucket-c2 → P6/Route B.)
- [ ] **PR-P5.3 — Non-vacuity witness.** Instantiate `zisk_compliant_trace` on a
      realistic multi-row AcceptedTrace (≥2 sound opcodes, `stateAt` opaque) — extends
      `global_theorem_instantiation_add.lean` beyond the zero-row case (#74). Proves the
      env-free statement is inhabited and the 30-arm dispatch is not degenerate.
- [ ] **PR-P5.4 — Gate re-rooting + ledger collapse.** Add a TrustGate subcommand +
      `baseline-trace-level-binders.txt` for the new public statement; reconciliation
      note mapping the retired env-binder/63-equiv surface to the new aggregate; demand a
      MEASURED net reduction (caller-burden ledger collapses to one derived predicate).
      Plan-governed re-baseline.
- [ ] **PR-P5.5 — Refinement hooks (as dependencies land).** As each blocker clears,
      promote arms out of `h_arm_resid`: #76→loads/stores; M-ext extractors→M; XCAP/#100→
      branches/JAL/JALR + next-PC; defect retirements→FENCE/signed-M. Each is a net
      residual REMOVAL.

## §5 Honest end-state (→ [DERIVE_ENV#signature](../research/RESEARCH_DERIVE_ENV.md#signature))

`zisk_compliant_trace (trace)(binding)(h_aeneas)(h_mem)(h_known_bugs)(h_exec_resid)
(h_nextpc)[(h_arm_resid)] : ∀ i, exec_eq_at trace binding i`. **No `env`.** Surviving
trust: proof-system balance (inside `trace`), Aeneas bridge, #76 memory residual, known
defects, exec-artifact residual (until `bus_effect` retired), next-PC (until XCAP/#100),
+ the 33-arm residual (B only, shrinks as P4 completes). NOT unconditional.

## §6 Anti-laundering invariants (→ [DERIVE_ENV#anti](../research/RESEARCH_DERIVE_ENV.md#anti))

1. Net-shrink the trust surface (ledger collapse), don't relocate env binders.
2. Non-vacuity witness on a realistic multi-row trace; `stateAt` opaque; never the
   one-row/`rfl` floor.
3. The 33 named residuals must be REAL undischarged premises, not `True`-fallthroughs.
4. bucket-(c) not promoted to premises (c1→#76; c2 named-as-artifact until retired).
5. "0 PROJECT (`ZiskFv.*`) axioms; Sail + kernel as documented external trust" — never
   "0 axioms"; never "premise-free".

## §7 Dependencies & risks

- **Full theorem (A) is deeply gated:** P4=63/63, #76 (→#103), XCAP/#100, bus_effect
  retirement. P5-B is independent of all but inherits them as named residuals.
- **Trace coherence (P1)** is an unresolved likely-new residual shared with #76 — PR-P5.2
  / #76 PR-76.0 should resolve its trust class together.
- **Laundering risk** is the main hazard (relocation vs reduction) → PR-P5.4 measured
  net reduction + PR-P5.3 witness.
- **Drift:** audit doc says `memoryTimelineEvidence` (P3-renamed to
  `memoryTimelineConstructionEvidence`); roadmap says 28 (actual 30) — reconcile in P5.
- **P6 (OpEnvelope deletion + bus_effect retirement)** is the follow-on, blocked on P5 +
  full construction coverage; file at P5 completion.
