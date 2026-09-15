# RESEARCH — deriving `env` (P5 trace-level export / issue #61)

**Provenance.** 5-reader scope sweep (workflow `wl9qdnnuv`, 2026-06-17) over
`origin/main` (a5679e5b, P4=30). Raw: [`_raw/derive-env-scope.json`](_raw/derive-env-scope.json).
Consumed by [`../plan/PLAN_ENDGAME_P5.md`](../plan/PLAN_ENDGAME_P5.md). Builds on the
campaign end-state in [`RESEARCH_76_DESIGN.md`](RESEARCH_76_DESIGN.md#global-theorem-signature-progression-campaign-end-state).

## Index
- [§S. The gap in one picture](#s)
- [§1. The two halves + the decode that already exists](#halves)
- [§2. The bucket audit (already done)](#buckets)
- [§3. The orthogonality finding (env vs bus_effect)](#orthogonality)
- [§4. The scope fork: A (full, blocked) vs B (scoped skeleton, now)](#scope)
- [§5. The honest trace-level signature](#signature)
- [§6. Anti-laundering + vacuity for P5](#anti)

---

<a id="s"></a>
## §S. The gap in one picture

Today: `zisk_riscv_compliant_program_bus (env : OpEnvelope state m r_main)(h_bridge :
env.aeneasBridgeTrust)(h_memory_construction : env.memoryTimelineConstructionEvidence)
(h_known_bugs : Defects.NoKnownDefect env) : env.exec_eq` (`Compliance.lean:95`).
"Deriving env" = removing the `env` binder by deriving it from a committed `AcceptedTrace`.

**It is a plumbing/quantification gap, not a derivation gap.** The per-step env-free
derivation **already exists**: `construction_<op>_sound` (30/63) goes
`(trace, binding, i, residuals) → execute = (bus_effect …).2` on `binding.stateAt i`,
**bypassing `OpEnvelope` entirely** (it never builds an env). The conclusion is
`rfl`-equal to the dispatchers' `state_effect_via_channels` form (`StateEffect.lean:91`),
and decode is just `mainOfTable(trace.program, binding.mainTable).op i.val` (= the
`h_main_op` binder every construction already takes). So the assembly is: a trace-level
`∀ i, exec_eq_at trace binding i` theorem that case-splits on `op i.val` and, per arm,
calls the matching `construction_<op>_sound`. **No P5/P6 plan exists yet.**

---

<a id="halves"></a>
## §1. The two halves + the decode

- **LEFT (env → exec_eq):** the global theorem + 10 per-family dispatchers
  (`Dispatch/*.lean`), all 63 arms, each `cases env; exact equiv_<OP> …`. **Takes an
  env, not a trace.**
- **RIGHT (trace → conclusion):** 30 `construction_<op>_sound`
  (`Compliance/Construction*.lean`, registered `bin/TrustGate/Main.lean:245`). **Takes a
  trace, bypasses env.**
- **The missing assembly = the bridge.** Because `state_effect_via_channels = bus_effect.2`
  by `rfl`, RIGHT's output already *is* LEFT's `exec_eq_<family>` arm — no semantic
  adapter needed, only quantification over steps.
- **Decode already exists, trivially.** `op i.val` read from the committed Main+ROM row
  (no Sail bit-decoder); "which arm fires at step i" = a finite case-split on the 63
  `OP_<NAME>` literals (+ `is_external_op/m32/store_pc` flags for sub-variants). The
  `exists_<fam>_provider_row_matches_<op>_from_binding` wrappers already turn
  `binding + h_main_op` into the op-bus provider match via `trace.balanced`.
- **`envOf trace i` (building an OpEnvelope from the trace) is feasible but the SLOWER
  route and NOT needed** — go trace → construction → conclusion directly (what P6 wants).

---

<a id="buckets"></a>
## §2. The bucket audit (DONE — `trust/envelope-burden-audit.md`, #61 step 2 via #83)

All 65 OpEnvelope constructor fields classified:
- **(a) derivable** (most fields): trace data, row membership, lookup/table soundness,
  bus matches, validators, promise bridges → discharged by `construction_<op>_sound`.
- **(b) genuine named premises** (5 classes): program-binding/decode, boot/profile state
  (misa.C, cur_privilege, PMA/mstatus…), `aeneasBridgeTrust`, load memory timeline
  (`memoryTimelineConstructionEvidence`, #76), `NoKnownDefect`.
- **(c) NON-EMPTY — must be eliminated, NOT promoted to premises** — two classes:
  - **(c1) subword-store preserved-byte RMW** (`sb.h_m1..h_m7`, `sh.h_m2..h_m7`,
    `sw.h_m4..h_m7`) → fold into the #76 store replay (Spike #2).
  - **(c2) exec-bus shape artifacts** (`execRow` ∀-binder + `h_exec_len/h_e0_mult/h_e1_mult`)
    → a **phantom channel** (ZisK has only OpBus/RomBus/MemBus; `bus_effect` is a foreign
    openvm import). Eliminated by restating the conclusion off `bus_effect` onto
    ZisK-native channels — a separate P6-style retirement, NOT promoted to premises.
- **(b)-pending-infra:** `h_nextPC_matches` (next-PC, **every** opcode) — the one
  semantically-real exec fact; not derivable today (cross-row PC handshake lives only in
  the dead legacy Extraction model). Named residual until **XCAP/#100**.

> Naming drift: the audit doc says `memoryTimelineEvidence`; main uses
> `memoryTimelineConstructionEvidence` (P3 rename). Roadmap says "28"; actual is **30**.

---

<a id="orthogonality"></a>
## §3. The orthogonality finding (the load-bearing correction)

**env-elimination and `bus_effect` retirement are ORTHOGONAL.** Proof from live code:
`construction_<op>_sound` is *already* env-free (concludes `execute = (bus_effect …).2`
from trace+binding) AND *still* carries `execRow` + `h_exec_len/h_e0_mult/h_e1_mult` as
residual binders (`ConstructionSub.lean:213-216`). So:
- **env goes** by deriving the per-opcode equation from a trace (the assembly layer).
- **exec artifacts ride along** as explicitly named bucket-(c) residuals of the new
  trace-level theorem — there is no trace object to derive them from.
- **`bus_effect` retirement is a SEPARATE, lower-priority P6-style campaign**, NOT a P5
  prerequisite.

This means P5 ("deriving env") does **not** wait on the phantom-bus cleanup.

> **⚠ Correction (2026-06-17, from the Gap-(c) scope — [`RESEARCH_GAP_C.md`](RESEARCH_GAP_C.md)):**
> the orthogonality holds for env *shape*-elimination, but it was over-stated for the
> **next-PC DISCHARGE**. `h_nextPC_matches` (carried by all 30 sound arms) is about the
> foreign `exec_row[1].pc`; discharging it requires reaching into `exec_row` and tying it to
> the real `pc` column. That is NOT a free ride-along — it needs **Route C** (the P5 env
> builder populates `exec_row[1].pc := pc(i+1)` faithfully from the trace, then the #100 seam
> + the column↔Sail bridge discharge it). So: env-*elimination* ⊥ `bus_effect` *shape*
> retirement (still true), but the next-PC *fact* discharge is entangled with reaching into
> `exec_row` — handled in P5 via Route C, short of the full `bus_effect` (Route B) retirement.

---

<a id="scope"></a>
## §4. The scope fork (the decision P5 must resolve)

- **Option A — full env-free theorem.** Blocked until: P4 = 63/63 (M-ext + loads/stores
  + branches/JAL/JALR + FENCE), **bucket-c1** eliminated (#76 store replay, itself gated
  on #103), **next-PC** derivable (XCAP/#100), and **bucket-c2** ideally retired
  (`bus_effect` campaign) for faithfulness. Roadmap default; far downstream; nothing
  buildable now.
- **Option B — scoped skeleton, buildable NOW.** A trace-level `∀ i, exec_eq_at trace
  binding i` theorem that dispatches the **30 sound arms** to their constructions and
  carries the **33 missing arms + next-PC + exec-artifacts + store-RMW** as **explicit
  named residuals**, plus the decode function and a **non-vacuous multi-row witness**.
  Demonstrates env-elimination end-to-end; refined as P4/#76/#100 land.

**Risk on B:** if the named residuals merely re-house env's content of identical shape,
it is *relocation, not reduction* (laundering). B is only legitimate if it collapses the
~1087-line caller-burden ledger into one DERIVED constraint-satisfaction surface and is
witnessed non-vacuously. **Must not silently pick B and call #61 "done."**

---

<a id="signature"></a>
## §5. The honest trace-level signature (the target)

```
theorem zisk_compliant_trace
    (trace : AcceptedTrace) (binding : ProgramBinding trace)
    (h_aeneas      : …)   -- Aeneas lowering / decode bridge (named until generated Aeneas Lean imported)
    (h_mem         : …)   -- #76 memory residual (boot + cross-seg seed + trace coherence) — irreducible floor
    (h_known_bugs  : …)   -- NoKnownDefect, scope restriction (retires with patched ZisK)
    (h_exec_resid  : …)   -- bucket-c2 exec artifacts (execRow + mults) until bus_effect retired
    (h_nextpc      : …)   -- bucket-b-pending until XCAP/#100
    (h_arm_resid   : …)   -- the 33 not-yet-constructed arms (Option B only)
    : ∀ i, exec_eq_at trace binding i
```
`trace.balanced` (proof-system channel balance) is already an `AcceptedTrace` field — the
deepest external-trust input, carried inside the trace, not a separate hypothesis.
**No `env`.** NOT unconditional.

---

<a id="anti"></a>
## §6. Anti-laundering + vacuity for P5

1. **Reduce, don't relocate.** The new signature must net-shrink the audited surface
   (caller-burden ledger collapses to one derived predicate). Gate re-rooting is
   plan-governed; a reviewer confirms the diff REMOVES more than it adds.
2. **Non-vacuity witness required** — instantiate on a realistic multi-row trace with
   `binding.stateAt i` opaque (not let-bound to a replay RHS), ≥2 sound opcodes; never
   the one-row/`rfl` floor (`global_theorem_instantiation_add.lean` is the zero-row
   sanity check, not sufficient).
3. **Named residuals must be REAL undischarged premises** (the per-opcode equation), not
   `True`-fallthroughs that let the aggregate hold vacuously on instruction-free traces.
4. **bucket-(c) must not be promoted to premises** — c1 folds into #76; c2 is named-until-
   retired but flagged as an artifact, not a real fact.
5. Phrasing: **"0 PROJECT (`ZiskFv.*`) axioms; Sail-translation + Lean-kernel axioms
   present as documented external trust"** — never "0 axioms"; never "premise-free".
