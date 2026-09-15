# RESEARCH — closing Gap (c): the exec-bus ↔ real-pc bridge (XCAP #100 payoff)

> # ⛔⛔ FAITHFULNESS DEAD END (2026-06-17, PIL-verified) — Route C / the whole gap-c plan does NOT work
> Executing the plan (PR-GapC.0/.1 + X100.1a) revealed the **seam it depends on is a
> FABRICATED channel.** ZisK has **no per-row `pc`-tagged bus**: within-segment PC is a
> per-row POLYNOMIAL constraint `(1-SEGMENT_L1)*(pc-expected_current_pc)===0` (`main.pil:410`,
> the existing `pc_handshake`), and cross-segment PC is a `direct_update` AIRVAL bus
> (`MAIN_CONTINUATION_ID`, `main.pil:501-529`). The per-row `PcContChannel` is type-illegal on
> the continuation bus (degree-0 only) and has no counterpart. So `pc_seam_of_balanced` is
> sound over a fabricated model but **cannot balance on a real trace** (open chain), and
> `h_seam` is unfaithful. **#100 ≠ #103** (cross-segment IS a bus; cross-row within-segment PC
> is a constraint). The genuine #100 path is **route A**: get the per-row `pc_handshake`
> constraint (`main.pil:410`) into the live single-row Clean component — the ORIGINAL #100
> cross-row obstruction the channel was (unfaithfully) trying to dodge. Everything below is
> retained as the wrong-turn record; do NOT execute it.

**Provenance.** 4-reader scope+route-probe (workflow `wp9ubg80g`, 2026-06-17) over
`origin/main` + the built seam/pins on `xcap-x100-wiring` (`74afae9b`). Raw:
[`_raw/gap-c-scope.json`](_raw/gap-c-scope.json). Consumed by the plan in
[`../plan/PLAN_ENDGAME_XCAP.md`](../plan/PLAN_ENDGAME_XCAP.md) (PR-X100.1c) +
[`../plan/PLAN_ENDGAME_P5.md`](../plan/PLAN_ENDGAME_P5.md) (where Route C resides).

## Index
- [§S. The gap in one chain](#chain)
- [§1. Why it is real (not bookkeeping)](#real)
- [§2. Route decision — C](#routes)
- [§3. Blast radius + interactions (#101, #76)](#blast)
- [§4. Anti-vacuity / anti-laundering discipline](#anti)
- [§5. The honest residual after Route C](#residual)
- [§6. PR breakdown + sequencing](#prs)

---

<a id="chain"></a>
## §S. The gap in one chain

`h_nextPC_matches` (carried by **all 30 sound constructions**) is:
`(register_type_pc_equiv ▸ BitVec.ofNat 64 (exec_row[1]!.pc).val) = pure_nextPC`.
`bus_effect` (`BusEffect.lean:124-126`) literally **writes `Register.nextPC := exec_row[1].pc`**,
so this is load-bearing, not vestigial. Discharging it is a **chain of three equalities,
only one new**:

```
exec_row[1].pc  =  pc(i+1)        ... (1) NEW = Gap (c) proper  [Route C: faithful population]
pc(i+1)         =  nextpc(row i)  ... (2) the #100 SEAM (built; a theorem once X100.1a lands)
nextpc(row i)   =  pure_nextPC    ... (3) the column↔Sail bridge (ALREADY exists, sequential)
∴ exec_row[1].pc = pure_nextPC = h_nextPC_matches
```

So Gap (c) proper is **only equality (1)** — and `exec_row` is **caller-chosen** (`busSub`
sets `exec_row := execRow`, a free ∀-binder; it is an `OpEnvelope` field; P5 builds `env`
from the trace). So the caller can set `exec_row[1].pc := the real pc(i+1)` (read from
`mainOfTable(…).pc (i+1)`).

---

<a id="real"></a>
## §1. Why it is real (not bookkeeping)

- `bus_effect` final arm: `Sail.writeReg Register.nextPC (… (execution_bus[1]!.pc).val) state`
  (`BusEffect.lean:124-126`). The canonical conclusion `execute = (bus_effect …).2`
  **defines** the post-state nextPC as `exec_row[1].pc`.
- `exec_row[1]` is the **producer** entry (mult +1); semantically the producer next-PC,
  consumed by the next instruction as its current PC = the **next Main row's `pc` column**.
  → `exec_row[1].pc := pc(i+1)` is the **definitionally correct, unique faithful** choice.
- Confirmed gap: exhaustive grep — **no** theorem/def/constraint links any
  `ExecutionBusEntry.pc` to `MainRow.core.pc` / the seam. The only op-bus→exec constructor
  (`execEntryOfOpBus`, `StateEffect.lean:64`) takes `pc` free and has **zero callers**. The
  seam (`pcLastMessageExpr`, real columns) and `h_nextPC_matches` (exec_row) live in
  **disjoint vocabularies**.

---

<a id="routes"></a>
## §2. Route decision — **C** (both maps converge)

| Route | What | Verdict |
|---|---|---|
| **A** — channelize the exec bus | add a real exec-bus channel tying its pc to the real column | **REJECT** — redundant (the PcContChannel *already is* the real-column pc channel); re-introduces a foreign artifact ZisK lacks (faithfulness regression). |
| **B** — restate the conclusion off `bus_effect` | read next-PC from the real `pc` column in the conclusion | the genuinely-cleanest **end state**, but a **63-arm + global + gate-rebaseline P6 campaign** (bucket-c2 retirement; audit-deprioritized). The *right eventual* fix, the *wrong first* step. |
| **C** — populate `exec_row` faithfully at the caller + use the seam | set `exec_row[1].pc := pc(i+1)` in the env builder; discharge via the 3-equality chain | **CHOSEN.** Localized (one bridge lemma + threading `exec_row` population through env-construction). DERIVES `h_nextPC_matches`; no foreign bus; no 63-arm rewrite. |

**Route C is the compose-seam-with-row-tie pattern of the #103 L5
`cross_segment_real_memory_continuity`** (balance-derived seam + a tie pinning the foreign
columns to genuine row state) — the right structural template to mirror.

---

<a id="blast"></a>
## §3. Blast radius + interactions

- **Universal:** `h_nextPC_matches` is carried by **all 30 sound arms** (even LUI/AUIPC
  carry the sequential `pc+4` handshake). Closing Gap (c) removes a residual from **every**
  opcode — not just branches.
- **#101 last mile:** the BEQ/BNE flag is fused into the *column-side*
  `pc_handshake_with_next_pc`; #101 needs the seam (split flag→PC) + the flag lemma
  (`binary_eq_chunks_eq_bv_eq_of_wf`, banked) + **Gap (c)** to push the real next-PC through
  exec_row into `bus_effect`. Gap (c) is its last mile too.
- **#76 shared:** loads/stores also carry `h_nextPC_matches` → Gap (c) is shared
  infrastructure (orthogonal to #76's hard memory-timeline part).
- **Ownership:** a #100-discovered, P6-class fact, but **solved inside P5's env-construction
  layer** (where `exec_row` gets populated from the trace). Corrects the stale
  "env-elimination ⊥ bus_effect" claim: env-*elimination* ⊥ bus_effect *shape*, but next-PC
  *discharge* needs reach into `exec_row` — which P5's env builder does, faithfully.

---

<a id="anti"></a>
## §4. Anti-vacuity / anti-laundering discipline (the reviewer checks)

- **Faithful population, not arbitrary.** `exec_row[1].pc` MUST be a function of the real
  trace (`mainOfTable.pc (i+1)`), gated by `stepCoherent`. An arbitrary `exec_row` makes the
  global conclusion **vacuous/wrong** (writes a garbage nextPC). This is the cardinal sin.
- **Derive, do not relocate.** `exec_row[1].pc = pc(i+1)` must be a **definitional choice**
  in the env/trace construction (`envOf trace i` builds `exec_row`), NOT a new caller
  premise of the same shape. The caller-burden + hypothesis-count baselines must
  **net-remove** the per-opcode `h_nextPC_matches` lines (no equal-shape premise added).
- **Witness non-vacuously** on a **k≥2** real multi-row trace with `stateAt` **opaque**
  (not let-bound to the replay RHS). End the investigation in a **compile probe**, not an
  argument (the #103 discipline: every design-level "confirmed" was refuted one layer deeper).
- Phrasing: **"0 PROJECT (`ZiskFv.*`) axioms; Sail + kernel as documented external trust"**
  — never "0 axioms"; never "premise-free" (`stepCoherent` remains a named residual).

---

<a id="residual"></a>
## §5. The honest residual after Route C

> **⚠ Honest correction (2026-06-17, from executing PR-GapC.0/.1):** Route C is **NOT a
> binder-COUNT reduction** — the live Main AIR does not pin decode bits (`set_pc`/`jmp_offset2`)
> or range-check `pc`, so those are not in-body derivable. It is a **structural unpacking with
> a QUALITATIVE trust reduction**: the HARD cross-row `h_nextPC_matches` (no per-row derivation
> exists in the live Clean model) is replaced by `h_seam` (ensemble-balance class → X100.1a) +
> `AddSeamDecode`/`h_pc_col` (**per-row facts of the `aeneasBridgeTrust` class the global theorem
> already discharges per-arm**) + a small `pc`-range gap (`h_no_overflow`). Per-theorem count
> grows (1→3+1); the GLOBAL footprint does not (the per-row pieces fold into the existing
> `aeneasBridgeTrust` residual — the structural-unpacking-exception shape). Bonus: `h_flag`
> eliminated. So the genuine claim is **cross-row → per-row(existing classes) + ensemble
> balance**, realized at the global level via folding, not a count drop.

Route C closes the **sequential `pc+4` next-PC FACT for all 30 arms**. What survives:
- **`stepCoherent`** — the faithful-exec_row tie to the trace (a pre-existing P5/#76-shared
  named residual; the trace-coherence premise, not an axiom).
- **branch/JAL/JALR targets** — the non-sequential mux still needs **SPINE-#2**
  (`constraint_18` re-extraction) + **#101** (flag). Gap (c) does NOT close these.
- **the exec_row SHAPE** — `execRow` as a ∀-binder + `h_exec_len`/`h_e0_mult`/`h_e1_mult`
  remain (the conclusion is still phrased over `bus_effect`). Full elimination = the **P6
  bus_effect retirement (Route B)**. Gap (c) closes the next-PC *fact*, not the phantom-bus
  *shape*.

---

<a id="prs"></a>
## §6. PR breakdown + sequencing

- **PR-GapC.0 — bridge lemma spike (the gate, startable NOW).** Prove
  `nextPC_matches_of_seam` for the sequential case: GIVEN the seam fact `pc(i+1) =
  nextpc_mux(row i)` **as a stubbed hypothesis** + the existing column↔Sail bridge
  (`jmp_offset2 = 4`, `register_type_pc_equiv`, `m.pc ↔ state.PC`), with `exec_row[1].pc :=
  pc(i+1)`, derive `h_nextPC_matches`. Thread into **one** construction
  (`construction_add_sound`); confirm the `h_nextPC_matches` binder is **removed**
  (caller-burden net-shrink), kernel-only, on a **k≥2** non-vacuous witness. GO/NO-GO.
- **PR-GapC.1 — faithful `exec_row` population (P5-resident).** Define `execRowOf trace
  binding i := [⟨-1, pc(i), ts⟩, ⟨1, mainOfTable(…).pc (i+1), ts⟩]` from the real Main pc
  column, gated by `stepCoherent` (refines `PLAN_ENDGAME_P5.md` PR-P5.2). Makes equality (1)
  definitional, not a premise.
- **PR-GapC.2 — replicate** across the 10 construction files / 30 sound arms; discharge
  `h_nextPC_matches` everywhere (sequential). Net residual removal across all 30. Refresh
  the caller-burden / hypothesis-count baselines (must shrink).
- **PR-GapC.3 — discharge the stubbed seam hypothesis** from the real-ensemble seam theorem
  (**X100.1a**). Closes equality (2) on the live ensemble.

**Sequencing:** Gap (c) is the **LAST step of #100's payoff**, not a prereq of its earlier
steps. Order: **X100.1a** (seam theorem on the real ensemble) → **Gap (c) / Route C** (route
the seam through `exec_row` in P5) → **X100.2** (cash `h_nextPC_matches` out of the 30 + new
arms). **PR-GapC.0 (the bridge lemma) is startable NOW** with the seam stubbed; everything
else composes once X100.1a lands.
