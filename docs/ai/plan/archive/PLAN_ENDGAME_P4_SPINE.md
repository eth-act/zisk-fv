# PLAN_ENDGAME_P4_SPINE — the P4 construction spine

> Originated as the closeout of the off-the-rails #94/#97 construction stack. What
> it establishes and carries forward is the **spine of P4**: the `AcceptedTrace`
> construction infra, the honest §2 construction template, the §4 invariants, the
> recursive audit gate, and the first sound family (SUB). The sweep / memory /
> prerequisite sub-plans build on this. (It is NOT "closing out P4" — P4 is barely
> begun; see `PLAN_ENDGAME_P4_METAPLAN.md` for status.)

**Basis:** `docs/ai/plan/RESEARCH_PR94_CLOSEOUT.md` (read it first — this plan
encodes its verified findings). **Role:** the reviewer/plan-maker wrote this; a
separate agent executes it. **Status:** PLAN WRITTEN, not started.

---

## 0. TL;DR and the decision

The P4 construction stack (PR #94 `da0dfc2c` + the PR2/PR3/PR4 commits
`Add P4 binary provider table extractors` / `branch construction breadth` /
`nomem construction breadth`) is **laundering, not construction**, and the
laundering is **structural and systemic** (the "carry the bucket-(a) facts as
caller-supplied `*RowBinding` fields and forward them through `.promises`" pattern
is baked into 37+ binding structures across families). It must **not** be merged.

**Decision (close-and-replan-with-salvage):**
1. Land the unambiguous truth-corrections on `main` now (audit reclassification +
   a closeout decision record). Direction-agnostic; zero proof risk.
2. **Salvage** the genuinely-sound work (the op-bus Tier-1 balance machinery,
   `AcceptedTrace`, `mainOfTable` + bridges, the gate apparatus mechanics) via a
   manifest, and rebuild P4's construction on a **correct, gated template** proved
   end-to-end on 1–2 ALU families — establishing the honest decomposition the
   research forced out (derive the **data effect**; *name* the **control-flow
   effect** as an explicit residual pending a foundational model change).
3. **Close** PR #94 and its stacked descendants with a documented rationale.
4. **File** the two foundational prerequisites the research surfaced (cross-row
   Clean-model capability; Binary-EQ 8-byte aggregation), and **re-scope** the
   remaining P4 family sweep against the corrected template.

**What this plan delivers** = closeout + corrections + a proven sound template +
filed prerequisites. **What it does NOT deliver** = the full 63-family sound
sweep (that is the re-scoped P4 execution, governed by the updated
`PLAN_ENDGAME_P4_SWEEP.md`) and the prerequisites themselves (separately planned).

**Why close-and-replan, not fix-in-place:** the relabel is structural across
37+ bindings and the stack is still growing; the sound parts are cleanly
separable; the honest construction has a *different shape* (data-effect-derived,
control-flow-named) than the relabel, so it is rebuilt, not patched.

---

## 1. Verdict recap (see RESEARCH_PR94_CLOSEOUT.md for full citations)

- `construction_beq` (and every family analogue) is a **relabel**: it forwards a
  caller-supplied `*RowBinding` (which transitively smuggles the entire
  `MainRowProvenance` decode bundle + the exec-bus facts) into the existing
  `*OfExtractedShape` constructor. `trace.constraints`, `trace.balanced`,
  `mainTable_mem/_component`, and the bridge lemmas `rowAt_mainOfTable` /
  `opBus_row_Main_mainOfTable` are **dead code** in the construction.
- **Genuinely real and salvageable:** PR2's op-bus **Tier-1** balance machinery
  (`exists_*_provider_row_matches_*_from_binding` →
  `exists_construction_*_from_balance`, backed by axiom-free permutation theorems
  in `Balance.lean`) — it really consumes `trace.balanced` to derive the op-bus
  provider match; the `AcceptedTrace` type; `mainOfTable`/`rowAt_mainOfTable`; the
  TrustGate `forallTelescope` apparatus.
- **The audit gate is blind** — it snapshots only the 4 top-level binders of
  `construction_beq` and never recurses into `ProgramBinding`/`*RowBinding`, so the
  smuggling is invisible and the gate gives false assurance.
- **The "extract more?" question (resolved):** ZisK's cross-row PC constraint is
  extracted only into the **dead legacy `Circuit` model**; the **live Clean
  `Air.Flat.Component` model is structurally single-row** and cannot hold a
  cross-row constraint, so `pc_handshake` is **not** in `trace.constraints` and is
  **not** derivable today. Deriving the next-PC needs a **framework change**
  (rotation-capable component or shadow-column encoding) — general to *every*
  opcode's next-PC, not branch-specific. The branch `flag` additionally needs a
  **missing Binary-EQ 8-byte aggregation lemma** (templated by the existing SLT
  chain). ZisK has **no execution bus**; `bus_effect`/`ExecutionBusEntry` is a
  foreign openvm import.

---

## 1a. GitHub issue anchoring (this closeout is NOT freestanding)

- **#61 "Close the OpEnvelope construction gap"** is the umbrella. This closeout
  IS its step-4 work (`AcceptedTrace → OpEnvelope` construction) done correctly.
  - The audit PR1 corrects (`trust/envelope-burden-audit.md`) is **#61's first
    deliverable** (PR #83). #61 already records bucket (c) non-empty (subword-store
    preserved-byte RMW facts in `sb/sh/sw`). PR1 adds a SECOND bucket-(c) class
    (the exec-row artifacts) — connect them in the doc, don't invent a parallel.
  - The §2 decomposition (data-effect → (a); next-PC → (b)-pending-infra; exec
    artifacts → (c)) is exactly #61's three-bucket framing; the trace-level export
    theorem (#61 step 5) is the eventual public statement P4 feeds.
  - **PR1 posts the laundering verdict + corrected approach to #61.** **PR4 files
    the two §6 prerequisites as CHILDREN of #61** (linked, like #74/#75/#76).
- **#74 "Instantiate the global theorem on a real trace"** — the de-risking
  sibling. Its concrete instantiations (`trust/consistency/global_theorem_
  instantiation_ld.lean`, the completeness witness files) are the **pattern PR0's
  spike reuses** for building a concrete envelope.
- **#76 "Discharge h_memory_timeline"** — the memory portion of the same
  construction. NUANCE this plan contributes: Mem encodes cross-row continuity via
  **single-row shadow columns** (`addr_changes`/`previous_step`/`read_same_addr`),
  so #76 is **NOT** blocked by the cross-row ceiling that blocks Main's next-PC
  (prerequisite #1). The "nomem construction breadth" the executor pursued was
  deferring #76; the memory families remain #76's scope, more tractable than the
  PC residual.
- Off critical path: #75 (P1), #77/#78 (P2).

---

## 2. The honest construction model (the spine of the rebuild)

This is the conceptual core every PR below must respect. **Read it before writing
any Lean.**

A per-opcode `OpEnvelope` arm's content splits into three honest buckets against
the live Clean ensemble (channels = OpBus + MemBus only; per-row component model):

*(Bucket assignments below were ADVERSARIALLY VALIDATED by the PR0 SUB spike +
its refuter — the refuter confirmed every "derive" link holds and pinned down the
exact residual set; see the residual budget after the table.)*

| Effect / fact | Bucket | How it is honestly handled in the sound construction |
|---|---|---|
| **Row shape** (`row_eq`: committed row = `Main.rowAt (mainOfTable …) i`) | (a) derive | `mainOfTable` is *defined* as the projection of the trace rows; `rowAt_mainOfTable` gives this ≈`rfl`. **PR0-confirmed.** |
| **Structural BOOLEANITY** (`is_external_op*(1-is_external_op)=0`, etc.) | (a) derive | From `Main.Spec` booleanity constraints in `trace.constraints`. **NOTE (spike-corrected): only booleanity is derivable — NOT the activation VALUES (those are decode pins, below).** |
| **Op-bus provider match** (ALU families) | (a) derive | Salvaged Tier-1 from `trace.balanced`; bottoms in an **axiom-free** permutation theorem (`lean_verify → axioms:[]`, PR0-confirmed). **REUSE, don't reinvent.** |
| **Circuit-internal arithmetic** (rd-bytes = bv-operation of the packed provider lanes) | (a) derive | Provider match + the **already-proven** packed byte-chain lemmas (`binary_{and,or,xor,sub,add,...}_chunks_eq_bv_*`). **PR0-confirmed exists with compatible signatures.** |
| **MemBus write-shape** (`m0..m2`) | (a) derive | Construction-chosen bus entries; ≈`rfl` — but route through `row_eq` for index/instance alignment (`validOfRow … 0` vs `mainOfTable … i.val`; spell this out, it's not bare `rfl`). |
| **Decode pins — the VALUES** (`op`, `is_external_op`, `m32`, `store_pc`) | (b) named premise | **FOUR pins, not one.** The ensemble finishes only OpBus+MemBus (no ROM channel) and `Main.Spec` gives only booleanity, so the activation values are **NOT derivable** — they are the program/ROM residual (`aeneasBridgeTrust`/`ProgramBinding` territory; not new trust). Explicit top-level binders. |
| **Sail-value binding** (lane bridges `h_a/b_lo/hi_t`) + **Sail reads** (`h_input_*`, `rd_idx`, `h_misa_c`) | (b) named premise | Tie the circuit's packed lanes/operands to the Sail register values. The internal arithmetic is derived; **its binding to Sail is named.** Explicit top-level binders. |
| **Control-flow effect** (`nextPC_matches`) | (b)-pending-infra | **Named explicit residual for EVERY opcode** (sequential next-PC = pc+4 is *also* cross-row). Blocked by the cross-row ceiling (filed prerequisite #1; branches additionally need prerequisite #2). |
| **Exec-bus shape artifacts** (`exec_len`, `e0_mult`, `e1_mult`) | (c) artifact | Pure `bus_effect`/`ExecutionBusEntry` bookkeeping — no ZisK counterpart. Explicit residuals now; **eliminated** when `bus_effect` is retired (filed, P6-style). |

**The honest headline (corrected after the PR0 spike):** P4 derives, from
accepted-trace constraints + channel balance + provider correctness: the **op-bus
provider match**, the **row shape**, the **circuit-internal arithmetic** (rd-bytes
= bv-operation of the packed provider lanes), and the **MemBus write shape**. It
does **NOT** derive: the binding of those circuit lanes to the Sail register
values (lane bridges + Sail reads), the decode-pin values, the control-flow
next-PC, or the exec artifacts — these stay **explicit named top-level residuals**.
This is a **real, bounded** trust reduction (facts previously caller-supplied —
op-bus match, row shape, internal arithmetic — become derived) with **every**
residual visible, and it does not touch the canonical conclusion
(`execute = bus_effect.2`). Do NOT overstate it as "derives the data effect": the
Sail-value binding remains named.

**Validated SUB residual budget (PR0 spike — BUILT GREEN, adversarially confirmed).**
The compiled `construction_sub_sound` (293 lines) has **EXACTLY 17 residual
hypothesis binders** (4+5+4+3+1) plus the genuine `execRow` ∀-binder — and **zero
`MainRowProvenance`/`SubRowBinding` leaves** (grep-confirmed). The recursive-gate
deep baseline (PR2) must show this flat list:
- **(b) decode pins (4):** `op`, `is_external_op`, `m32`, `store_pc`
- **(b) Sail reads + operands (5):** `h_input_r1`, `h_input_r2`, `h_input_pc`,
  `h_input_rd`, `rd_idx`
- **(b) lane bridges (4):** `h_a_lo_t`, `h_a_hi_t`, `h_b_lo_t`, `h_b_hi_t`
- **(c) exec artifacts (3):** `h_exec_len`, `h_e0_mult`, `h_e1_mult` — PLUS the
  genuine `execRow : List (ExecutionBusEntry FGL)` ∀-binder (see anti-vacuity
  invariant §4.9: `execRow` MUST be universally quantified; hard-coding it to `[]`
  makes the exec hyps contradictory and the theorem vacuous).
- **(b)-pending-infra (1):** `nextPC_matches`
- **Derived, NOT binders:** `row_eq` + booleanity, op-bus provider match (from
  `trace.balanced`), circuit-internal rd arithmetic, MemBus `m0..m2` (`by rfl` off
  the real trace row), `h_lane_rd`, `h_mode32_zero`/`h_b_op`. Final call:
  `ZiskFv.Compliance.equiv_SUB` (which takes `MainRowPins`, NOT `MainRowProvenance`
  — the smuggling was purely a *sourcing* choice).
- **Salvaged-lemma locations (verified on `origin/endgame-p4-pr2`):**
  `mainOfTable` `Balance.lean:3870`, `rowAt_mainOfTable` `:3912`,
  `rowAt_mainOfTable_core` `:3974`, `opBus_row_Main_mainOfTable` `:4026`,
  `exists_staticBinary_provider_row_matches_sub_from_binding` `AcceptedTrace.lean:9492`,
  `cMemMessage_toEntry_register_write_lanes_match_of_store_pc_zero` `Main/Bridge.lean:250`.

**Non-negotiable:** the construction theorem's residuals are **top-level binders**
(so the recursive gate and a human reviewer see them). No `*RowBinding`/
`MainRowProvenance`-style deep record may carry a bucket-(a) or bucket-(c) fact.

---

## 3. Scope of THIS plan

**In scope:** PR0 (spike + salvage manifest) · PR1 (audit correction + decision
record) · PR2 (sound template, 1 ALU family, + recursive gate) · PR3 (second ALU
family, prove generality) · PR4 (close stale PRs + re-scope P4/roadmap + file
prerequisites).

**Out of scope (filed as follow-on, see §6):** the full 63-family sweep;
prerequisite #1 (cross-row model capability); prerequisite #2 (Binary-EQ
aggregation); the `bus_effect` retirement.

---

## 4. Hard invariants (inherited from the campaign; violations fail review)

1. **Zero new axioms anywhere.** `trust/generated/baseline-zisk-riscv-compliant.txt`
   stays `Total entries: 0`; `trust/baseline-axioms.txt` unchanged unless a PR
   explicitly and justifiably adds a documented-class axiom (none should).
   **AXIOM-CLAIM PHRASING (spike-mandated, non-negotiable):** never write "0
   axioms" / "zero axioms" about a theorem. A raw `lean_verify`/`collectAxioms`
   on a canonical theorem (e.g. `equiv_SUB_of_static_row`) is **non-empty** — it
   includes ~60 Sail-translation axioms (`riscv_f*`, `*_reservation`,
   `plat_term_write`, `get_16_random_bits`, …) and the Lean kernel postulates
   (`propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`). The project's gate (`TrustGate.AxiomClosure.isProjectAxiom`,
   root == `ZiskFv`) deliberately filters these as documented external scopes. So
   always say **"0 PROJECT (`ZiskFv.*`) axioms; Sail-translation + Lean-kernel
   axioms present as documented external trust"** — and distinguish genuinely
   kernel-only lemmas (`{propext, Classical.choice, Quot.sound}`) from
   Sail-carrying ones. Conflating the two is the exact overclaim a reviewer will
   reject.
2. **Anti-laundering metric must shrink or hold honestly.** Every construction PR
   must show the trust surface for the touched family *shrink*: bucket-(a)/(c)
   facts move from caller-supplied to **derived** (data effect) or to **explicit
   named** top-level residuals — not into deep records. The recursive
   construction-binder baseline diff is the audit surface; reviewers confirm
   removals, not renames. **No fact may be axiomatized or hidden to make a metric
   move.**
3. **CRITICAL REPORTING RULE.** If a fact the plan expects to derive cannot be
   derived, the executor **names it as an explicit premise and reports it** in the
   PR body — never axiomatize, never strengthen a `Valid_AIR`, never bury it in a
   record. A "can't derive X" report is a *successful* outcome of a spike, not a
   failure to hide.
4. **Manual worktrees from `origin/main`;** run `lake exe cache get` **first**
   after `git worktree add` (mandatory — skipping costs ~30 min). One STATUS.md
   per worktree.
5. **Build/verify gates** (run before every PR is opened): `lake build`,
   `trust/scripts/check-all.sh` (V1, no build), then after build
   `trust/scripts/check-all-semantic.sh` (V2). `nix run .#test` for the full gate
   before claiming a PR complete.
6. **PR protocol:** open the PR yourself when gates are green; first body line
   `Queued for Claude review — do not merge.`; then STOP.
7. **Anti-laundering principle verbatim (§8) goes into every sub-agent prompt**,
   and the executor reads `trust/README.md#anti-laundering-terms` before starting.
8. Plan-file edits limited to ticking your own checkboxes + prefixed log lines.
9. **ANTI-VACUITY (spike-mandated).** The `execRow` / exec-bus list MUST be a
   genuine universally-quantified top-level binder. The PR0 spike's first cut
   hard-coded `exec_row := []`, which made `h_exec_len : [].length = 2` (i.e.
   `0 = 2`) and the other exec hypotheses **contradictory** → the construction was
   **vacuously true**. Any construction PR must show the residual hypotheses are
   **jointly satisfiable** (the bus is built from the real trace row, not chosen to
   trivialize a hypothesis). A reviewer must sanity-check that no binder set is
   self-contradictory. This is a per-family check, not just SUB.

---

## 5. The PRs

### PR0 — Verification spike + salvage manifest (go/no-go; mostly throwaway Lean + one doc)

**Purpose:** confirm the §2 model is buildable *before* committing the template,
and capture the salvageable work before any branch is closed/deleted.

**Tasks:**
1. **Salvage manifest** (durable doc, the only committed artifact of PR0):
   `trust/p4-salvage-manifest.md`. Record, with commit SHAs and file:line:
   - The Tier-1 op-bus lemmas in `Balance.lean` that genuinely consume
     `trace.balanced` (the `exists_*_provider_row_matches_*_from_binding` and
     `exists_construction_*_from_balance` families), per family covered.
   - `AcceptedTrace` (def), `mainOfTable`/`mainTableRowAtOrZero`/`rowAt_mainOfTable`
     /`opBus_row_Main_mainOfTable`.
   - The TrustGate apparatus (`print-construction-binders` plumbing, `TypeWalk`
     `forallTelescope` renderer).
   - The already-proven packed byte-chain lemmas to reuse for the data effect.
   - Explicitly mark what is **NOT** salvaged: every `*RowBinding` /
     `MainRowProvenance`-carrying construction, every `construction_<op>` relabel,
     the blind `baseline-construction-theorem-binders.txt`.
   - **SPIKE-CORRECTED salvage boundary:** the clean black-box salvage is the
     **Layer-A binding-level provider-match wrappers**
     (`exists_*_provider_row_matches_*_from_binding`), the **Layer-B axiom-free
     permutation theorems**, the column bridges (`mainOfTable`,
     `rowAt_mainOfTable`, `opBus_row_Main_mainOfTable`), `AcceptedTrace`, the
     TrustGate apparatus, and the packed byte-chain lemmas. The
     **`exists_construction_*_from_balance` wrappers are NOT clean salvage** —
     all ~28 of them source their pins via `MainRowProvenance.*Pins_of_extracted_shape`
     off the smuggled record, so they must be **rewritten** to source from the
     honest top-level binders, not lifted as-is.
2. **Spike — the SOURCE chain is ALREADY adversarially validated (GO-WITH-CAVEATS,
   refuter could not break soundness); PR0's binding job is to COMPILE it.** The
   workflow's spike + refuter confirmed (by source-read + `lean_verify`) that for
   `SUB` every "derive" link holds and the residual set is the §2 SUB budget. What
   remains and is **mandatory before GO is unconditional:** on a scratch branch off
   `origin/main`, cherry-pick the salvaged Layer-A/B + bridge + byte-chain lemmas,
   assemble a *sound* `construction_sub` (op-bus match from `trace.balanced`;
   `row_eq`/booleanity from `mainOfTable`+`trace.constraints`; circuit-internal rd
   arithmetic from the byte-chain; decode pins / Sail reads / lane bridges /
   `nextPC_matches` / exec artifacts as **explicit top-level binders**), and
   actually `lake build` it. Source-read is necessary but NOT sufficient — PR #97
   has **no CI**, so nothing yet confirms even the salvaged lemmas elaborate when
   recomposed. When deriving the MemBus lane match, route through `row_eq` to align
   `validOfRow … 0` with `mainOfTable … i.val` (not bare `rfl`).
3. **Go/no-go memo** appended to the salvage manifest: for each §2 "derive" row,
   record whether it COMPILED and how (lemma chain), or what blocked it. Confirm
   the construction's top-level binders are **exactly the validated §2 SUB residual
   budget (~12 binders)** and nothing else leaks (no `MainRowProvenance`/
   `SubRowBinding` leaf).

**Gate:** the assembled `construction_sub` must **compile** (`lake build`, not just
source-read) and its binder set must match the §2 SUB residual budget. If any
"derive" link does **not** close on compile, STOP and report (do not relabel) —
the template design returns to the reviewer.

**Checklist:** ☑ manifest committed (in the docs PR #98, with spike-corrected
salvage boundary) ☑ assembled `construction_sub_sound` COMPILES via `lake build`
(GREEN, 293 lines) ☑ binder set == §2 SUB residual budget (17 + `execRow`, no
`MainRowProvenance`/`SubRowBinding` leaf) ☑ go/no-go memo written ☑ vacuity bug
caught + fixed honestly (execRow → ∀-binder).

**RESULT (2026-06-15) — PR0 GREEN.** Spike file (untracked, throwaway):
`.worktrees/p4-sub-spike/ZiskFv/Compliance/ConstructionSubSound.lean`. PR #97
stack typechecks (despite no CI), so the salvaged lemmas recompose. The §2 honest
template is BUILDABLE for SUB with zero new project trust. PR2 promotes this spike
into a committed construction + the recursive gate.

---

### PR1 — Truth corrections on `main` (direction-agnostic, no proof risk)

Land regardless of everything else; these stop `main` from *claiming* things that
are false.

**Tasks:**
1. **Correct `trust/envelope-burden-audit.md`:**
   - Move "Branch exec-row shape" → **bucket-(c) artifact** (to be eliminated by
     retiring `bus_effect`); cite `Interaction.ExecutionBusEntry` legacy status +
     "ZisK has no exec bus".
   - Move "PC/nextPC bus bridge" → **bucket-(b)-pending-infrastructure** for
     **all** opcodes (not just branches); cite the cross-row Clean-model ceiling
     (`FlatComponent.lean:147,170-172`; `AirsClean/Main/Constraints.lean:12-13`)
     and the missing Binary-EQ aggregation.
   - Add a short "Cross-row capability is a prerequisite" note so the audit no
     longer implies next-PC is derivable today.
   - In the audit doc, **connect the new exec-row bucket-(c) class to the existing
     bucket-(c) finding** (subword-store preserved-byte RMW facts in `sb/sh/sw`,
     recorded on #61 via PR #83) — same category, one section, not a parallel.
2. **Closeout decision record:** `trust/p4-construction-closeout.md` — one page:
   the verdict (laundering), the salvage decision, links to
   `RESEARCH_PR94_CLOSEOUT.md` and the manifest, and the two filed prerequisites.
3. **Post to #61:** a comment with the laundering verdict, the corrected §2
   construction model, and links to this plan + research + manifest. This keeps
   the project's umbrella issue the source of truth (do not let the closeout live
   only in `docs/ai/`, which is local-excluded).

**Gate:** docs-only; `check-all.sh` passes (no code touched). No `lake build`
needed for content, but run it to be safe (cache-warm = seconds).

**Checklist:** ☐ audit reclassified with citations ☐ decision record written
☐ `check-all.sh` green ☐ PR opened with `do not merge` first line.

---

### PR2 — Sound construction template (one ALU family) + recursive gate (Option X)

The heart of the rebuild. Promote the PR0 spike into the real, gated template.

**APPROACH (revised after PR0 — rework-off-#97, supersede; NOT a clean port off
main).** PR0 proved PR #97 typechecks and the salvaged lemmas recompose, so a
clean port off `main` is wasted effort. Instead branch off
`origin/endgame-p4-pr2` (#97), **keep** the salvage (AcceptedTrace, `mainOfTable`
+ bridges, Layer-A/B op-bus lemmas, byte-chains, the `ProgramBinding`
table-skeleton), **STRIP** the relabel (the `*RowBinding`/`MainRowProvenance`
construction records, the `construction_<op>` relabels, the entangled
`exists_construction_*_from_balance` wrappers, the blind
`baseline-construction-theorem-binders.txt`, and the `ProgramBinding` `*RowBinding`
projections), and **ADD** the sound construction + recursive gate. The repo
squash-merges, so the final diff vs `main` is clean regardless of branch history;
on merge this PR **supersedes #94/#97** (which then close as superseded — folding
PR4's closure step into the merge, still gated on Cody).

**Tasks:**
1. **Scope the strip safely (do FIRST, read-only):** map the exact relabel
   "strip set" vs the "keep set", and confirm **nothing live references the
   relabel constructions** (the `construction_<op>` arms are standalone P4
   deliverables, NOT yet wired into the global theorem — verify this before
   deleting; check `Dispatch/`, `Wrappers/`, `OpEnvelope.lean`,
   `AeneasBridgeTrust.lean`, which #97 also touched). Produce a strip manifest.
2. **Write the sound `construction_<fam>`** (recommend `SUB`) exactly per the PR0
   spike: data effect derived; decode/Sail/`nextPC_matches`/exec-artifacts as
   **explicit top-level binders** with descriptive names
   (`h_decode_op`, `h_input_*`, `h_nextpc_residual`, `h_exec_artifact_*`). Add a
   doc comment naming each binder's bucket and (for residuals) the filed
   prerequisite that would discharge it.
3. **Fix the gate (Option X — recursive field enumeration):** in
   `bin/TrustGate/TypeWalk.lean`, add a deep renderer: after `forallTelescope`,
   for each binder whose type head is a structure, enumerate `getStructureFields`,
   telescope function-valued fields, recurse with a `path` prefix + visited set,
   emit one baseline row per leaf field (`path :: fieldName :: ppExpr fieldType`).
   Wire a `print-construction-binders-deep` subcommand in `bin/TrustGate/Main.lean`;
   point `trust/scripts/check-construction-theorem-binders.sh` at it. (Because the
   sound construction has **no** deep records, the deep baseline will be the flat
   list of the construction's honest top-level binders — and any future attempt to
   re-introduce a smuggling record shows immediately as new diff lines.)
4. **Generate honest baselines:** the new
   `trust/generated/baseline-construction-theorem-binders.txt` lists the
   construction's binders; every **residual** appears as an explicit line — that
   list IS the audit surface for what P4 has *not* yet discharged. Refresh
   `baseline-equiv-axiom-deps.txt` / caller-burden as applicable; confirm
   `Total entries: 0` axioms holds.
5. **Anti-laundering self-check in the PR body** (required, per §8): show the
   touched family's data-effect facts moved caller-supplied → derived; show the
   residuals are top-level and named; confirm no axiom added, no `Valid_AIR`
   strengthened, no fact hidden.

**Gate:** `lake build` green; `check-all.sh` 18/18; `check-all-semantic.sh` 12/12
(the deep construction-binder check now meaningful); `nix run .#test` green.

**Checklist:** ☐ salvaged infra in, no relabel ☐ data effect derived from trace
☐ residuals top-level + named + bucketed ☐ recursive gate implemented & wired
☐ deep baseline regenerated & reviewed ☐ 0 axioms ☐ self-check in body ☐ PR
opened `do not merge`.

---

### PR3 — Second ALU family (prove the template generalizes)

Repeat PR2's template for one *different-shaped* ALU family — recommend a logical
op (**`XOR`** or **`AND`**, table-index route) to exercise a different data-effect
chain than `SUB`. Reuse the recursive gate. Confirm the deep baseline grows by
exactly the new family's honest binders (no smuggling). Same gates/checklist as
PR2. Purpose: demonstrate the template is mechanical and the gate scales, so the
re-scoped P4 sweep is low-risk.

**Checklist:** ☐ second family sound ☐ deep baseline grows by honest binders only
☐ gates green ☐ self-check in body ☐ PR opened `do not merge`.

---

### PR4 — Close the stale stack + re-scope P4 + file prerequisites

**Tasks:**
1. **Post a closeout review** on PR #94 (and each stacked descendant): one comment
   summarizing the verdict, linking `RESEARCH_PR94_CLOSEOUT.md` +
   `trust/p4-construction-closeout.md` + this plan + the salvage manifest, and the
   sound replacement PRs. **Then close the PRs** (eth-act is the user's repo —
   within bounds). **Do NOT delete the remote branches** without explicit user
   approval (they hold the salvage source until PR2/PR3 land).
2. **Re-scope `PLAN_ENDGAME_P4_SWEEP.md`:** replace its construction approach with the
   §2 model; the remaining work = sweep the sound template across the other
   families (data-effect-derived, residual-named), grouped by archetype. Mark the
   branch families as **blocked on prerequisite #2** and all next-PC discharge as
   **blocked on prerequisite #1**.
3. **Update `ENDGAME_ROADMAP.md`:** P4 row reflects "sound template established;
   data-effect derivation underway; control-flow residual gated on a new
   foundational phase." Add the two prerequisites to the phase table (see §6).
4. **File the two prerequisites as GitHub issues, as CHILDREN of #61** (link them
   in #61's body/comment alongside #74/#75/#76), with the §6 content as the
   technical anchor. Prerequisite #1 (cross-row Main-PC capability) note that it
   is distinct from #76 (Mem uses single-row shadow columns — not blocked).
5. **STATUS.md:** point at the re-scoped `PLAN_ENDGAME_P4_SWEEP.md`; record the closeout
   as done.

**Checklist:** ☐ closeout comments posted ☐ stale PRs closed (branches kept)
☐ `PLAN_ENDGAME_P4_SWEEP.md` re-scoped ☐ roadmap updated ☐ prerequisite issues filed
☐ STATUS.md current.

---

## 6. The two foundational prerequisites (file these; do NOT attempt in this plan)

### Prerequisite #1 — Cross-row capability for the Clean ensemble (foundational)
**Problem:** the live `Air.Flat.Component` model evaluates each row independently
(`environment row = fromArray row table.data`), so no constraint can reference
`row-1`. The Main PC-handshake (`constraint_18`, extracted only into the dead
legacy model) is therefore *unrepresentable* in `trace.constraints`, and
`pc_handshake_at` is assumed everywhere. **This blocks discharging EVERY opcode's
next-PC.**
**Two candidate approaches (the prerequisite plan must evaluate both):**
- (a) Extend `Air.Flat.Component`/`Table.environment` with a real previous-row
  rotation accessor; re-prove the ensemble soundness wiring; then derive
  `pc_handshake_at (mainOfTable …)` from the (now-live) cross-row constraint via
  the `mainOfTable` bridge (≈`rfl` once the source exists).
- (b) Shadow previous-row witness columns + single-row constraints pinning them +
  an inter-row equality (note: the inter-row equality is itself not per-row
  expressible → reduces back to (a) or a trusted copy/permutation argument; weigh
  honestly).
**Scope flag:** likely its own endgame phase; general benefit (all next-PCs,
Main segment continuation). **File as a child of #61.** **Distinct from #76:** the
Mem AIR already expresses its cross-row continuity with single-row shadow columns,
so the memory argument (#76) is NOT blocked by this ceiling — this prerequisite is
specifically Main's PC handshake (`constraint_18`), which genuinely reads `row-1`
cells of distinct Main columns.

### Prerequisite #2 — Binary-EQ 8-byte aggregation lemma (moderate, templated)
**Problem:** the per-byte EQ rule `wf_EQ` is proven, but there is **no**
`binary_eq_chunks_eq_bv_eq_of_wf` turning the 8 per-byte facts into
`flag = 1 ↔ a == b` over 64 bits; `equiv_BEQ` takes the flag's effect as a free
promise; `h_flag_correct` is comment-only.
**Scope:** write the aggregation lemma in `BinaryPackedCorrect.lean` mirroring the
proven `binary_lt_chunks_eq_bv_slt_of_wf` (8-byte induction + final-byte polarity
flip), a `BinaryCompare`-style consumer, and re-plumb `Beq`/`Bne` EquivCore to take
the byte-chain hypotheses and **derive** the branch flag — exactly the
`equiv_SLT_of_wf` pattern. Needed (with #1) before branch next-PC can be derived.

### (Tracked, lower priority) `bus_effect`/`ExecutionBusEntry` retirement
Restate the canonical conclusion off the foreign openvm `bus_effect` onto the
ZisK-native channels; eliminates the bucket-(c) exec artifacts and (with #1)
folds the next-PC residual into a derived fact. Touches the 63-opcode shared
conclusion form → P6-style negative-diff campaign.

---

## 7. Verification commands (run from the worktree root, inside `nix develop`)

```bash
lake exe cache get                         # FIRST, after worktree add
lake build                                 # the FV check
trust/scripts/check-all.sh                 # V1 syntactic (seconds, no build)
trust/scripts/check-all-semantic.sh        # V2 semantic (needs oleans)
nix run .#test                             # full suite before claiming a PR done
# Inspect the deep construction-binder snapshot:
lake exe trust-gate print-construction-binders-deep
```

---

## 8. Anti-laundering principle — VERBATIM (copy into every sub-agent prompt)

> **Promise discharge exists to REDUCE residual trust, not rearrange it.** Refuse
> these laundering patterns: (1) **Axiom inflation** — a hypothesis becomes an
> axiom of the same shape; every new axiom must fit a documented `trusted-base.md`
> class with a citation to a specific PIL line / Rust fn / soundness theorem.
> (2) **Hypothesis splitting/renaming** — one promise becomes N; the
> hypothesis-count and caller-burden gates must show net REDUCTION. (3)
> **Universalizing too eagerly** — `(h_x : P r)` → `(h_univ : ∀ r, P r)` just
> moves trust to a stronger caller-supplied universal unless it is actually
> dischargeable from the trust ledger. (4) **Overstrong AIR validators** — a
> `Valid_AIR` constraint stronger than the circuit enforces makes equivalences
> vacuous; any change needs a PIL citation + constructibility sketch. (5)
> **Definitional aliasing** — `def Foo := <promise>` hides a hypothesis; mark new
> defs `@[reducible]` so V2 unfolds them, or justify.
>
> **The operational metric:** every promise-discharge PR must REDUCE or hold both
> the hypothesis-count baseline and the caller-burden ledger, with the diff
> visibly REMOVING more than it adds. A "net zero" PR discharged nothing.
>
> **CRITICAL REPORTING RULE:** if a fact you expected to derive cannot be derived,
> NAME it as an explicit premise and REPORT it — never axiomatize, strengthen a
> validator, or hide it in a record to make a metric move. Reporting a genuine
> residual is success, not failure.
>
> Before declaring a step complete, verify: the metric shrank (or residuals are
> explicit & named); any new axiom fits an existing class with citation; any new
> `Valid_AIR` constraint or top-level `def` was reviewed for hidden-promise risk;
> and the PR/commit text uses the canonical glossary terms (`trust/README.md`).

**Project-specific addendum for this plan:** the sound construction's residuals
(decode content, Sail reads, `nextPC_matches`, exec artifacts) MUST be **top-level
binders** of the construction theorem — never carried inside a `*RowBinding` /
`MainRowProvenance`-style record. The recursive (Option X) gate enforces this
mechanically; the executor enforces the spirit.

---

## 9. Risks & open items

- **PR0 go/no-go is load-bearing.** If the data effect does not close from the
  trace for `SUB`, the §2 template is wrong and the plan returns to the reviewer.
  Do not paper over it.
- **`row_eq`/structural-pin derivation** (§2 rows 1–2) is asserted-likely but not
  reviewer-verified; PR0 confirms it.
- **The decode content is bucket-(b) (program/ROM), not bucket-(a).** Do not try
  to "derive" `op = OP_SUB` from constraints — it is program-determined. Name it.
  This is the same residual the project already carries; it is not new trust, but
  it must be an explicit binder.
- **GitHub closures are outward-facing.** Post the rationale comment first; close
  in the user's repo; leave branch deletion to explicit user approval.
- **Do not let the stale stack keep growing** mid-closeout — flag to the user if
  new commits land on those branches during execution.

---

## 10. Execution order

PR0 → PR1 (parallel-safe with PR0) → PR2 → PR3 → PR4. PR1 may land first (lowest
risk). PR4's PR-closures happen only after PR2/PR3 prove the salvage works.
