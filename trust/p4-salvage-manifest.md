# P4 construction stack — salvage manifest

This manifest records what is genuinely sound and reusable from the off-the-rails
P4 construction stack, and what is **not** clean salvage, so the rebuild
(`PLAN_ENDGAME_P4_CLOSEOUT.md` PR2/PR3) can pull the sound parts before the stale
PRs are closed. It is the durable companion to the closeout decision record
(`trust/p4-construction-closeout.md`) and the research evidence base
(`docs/ai/plan/RESEARCH_PR94_CLOSEOUT.md`).

**Source branches (do not delete until the rebuild lands):**

- `origin/endgame-p4-pr1` @ `da0dfc2c` (PR #94).
- `origin/endgame-p4-pr2` @ `6c414ffa` (the PR2/PR3 stack on top — holds the
  genuine op-bus balance machinery and the `mainOfTable` family).

**Axiom-claim phrasing (read before quoting trust numbers).** Never write "0
axioms" / "zero axioms" about any lemma below. A raw `lean_verify` /
`collectAxioms` on these is **non-empty** — it carries the Sail-translation
axioms and the Lean kernel postulates (`propext`, `Classical.choice`,
`Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`), which the project gate
(`TrustGate.AxiomClosure.isProjectAxiom`, root `== ZiskFv`) filters as documented
external scopes. The correct statement is **0 PROJECT (`ZiskFv.*`) axioms;
Sail-translation + Lean-kernel axioms present as documented external trust**. The
"axiom-free permutation theorems" below means **axiom-free of project (`ZiskFv.*`)
axioms** — they bottom out in real permutation reasoning, not a `ZiskFv.*` axiom.

---

## Clean salvage (reuse black-box)

These are the genuinely-sound pieces. They are separable from the smuggling
records and can be cherry-picked / re-derived onto the rebuild branch.

### Layer-A — binding-level provider-match wrappers

The `exists_*_provider_row_matches_*_from_binding` family in PR2's
`ZiskFv/Compliance/AcceptedTrace.lean`. These genuinely consume the
accepted-trace evidence to produce an op-bus provider-row match. Examples:

- `exists_staticBinary_provider_row_matches_logic_from_binding`
  (`origin/endgame-p4-pr2:ZiskFv/Compliance/AcceptedTrace.lean:9400`)
- `exists_staticBinary_provider_row_matches_sub_from_binding`
  (`AcceptedTrace.lean:9492`)
- `exists_staticBinary_provider_row_matches_compare_from_binding`
  (`AcceptedTrace.lean:9702`)
- `exists_staticBinary_provider_row_matches_w_from_binding`
  (`AcceptedTrace.lean:9791`)
- `exists_binaryExtension_provider_row_matches_shift_from_binding`
  (`AcceptedTrace.lean:9880`)

(31 `*_provider_row_matches_*_from_binding` wrappers total in the file.)

### Layer-B — axiom-free permutation theorems

The `Balance.lean`-level theorems the Layer-A wrappers bottom out in: existence
of a provider row whose `opBusMessage` matches the Main row's `opBus_row_Main`,
from channel balance. These are **axiom-free of project (`ZiskFv.*`) axioms** —
real permutation reasoning, not a trust axiom. In PR2 they live in
`origin/endgame-p4-pr2:ZiskFv/AirsClean/FullEnsemble/Balance.lean`:

- `exists_op_provider_row_matches_entry_spec_of_active_main_table_interaction`
  (`Balance.lean:1853`)
- `exists_op_provider_row_matches_legacy_main_spec_of_active_main_table_interaction`
  (`Balance.lean:1989`)
- `exists_staticBinary_provider_row_matches_legacy_main_of_xor_active_main_row_interaction`
  (`Balance.lean:2191`)
- `exists_staticBinary_provider_row_matches_legacy_main_of_logic_active_main_row_interaction`
  (`Balance.lean:2329`)

### Column bridges (`mainOfTable` and friends)

The bridge that defines `Valid_Main` columns as projections of the trace rows and
connects `Main.rowAt (mainOfTable …)` to the evaluated row. In PR2 these live in
`origin/endgame-p4-pr2:ZiskFv/AirsClean/FullEnsemble/Balance.lean`:

- `def mainTableRowAtOrZero` (`Balance.lean:3857`)
- `def mainOfTable` (`Balance.lean:3870`)
- `theorem rowAt_mainOfTable_core` (`Balance.lean:3974`) — binds
  `Main.rowAt (mainOfTable …)` to the evaluated row.
- `theorem opBus_row_Main_mainOfTable` (`Balance.lean:4026`) — binds
  `mainOfTable`'s op-bus row to the concrete trace row.

These were **dead code in the relabel** (the `construction_<op>` proof term never
used them), but they are genuinely sound and are exactly the column bridge the
honest construction needs for `row_eq` and the MemBus lane alignment. The
research's earlier `Balance.lean:1961/1973` anchors for `rowAt_mainOfTable` /
`opBus_row_Main_mainOfTable` are superseded by the verified PR2 locations above
(the lemmas moved to `ZiskFv/AirsClean/FullEnsemble/Balance.lean`).

### `AcceptedTrace`

`structure AcceptedTrace` (`origin/endgame-p4-pr2:ZiskFv/Compliance/AcceptedTrace.lean:33`):
`length` + `program` + an `Air.Flat.EnsembleWitness` over `fullRv64imEnsemble`,
plus `constraints` / `spec` / `balanced` fields. The type itself is sound and
reusable; the construction theorems built on top of it are the relabel and are
**not** salvage (below).

### The TrustGate apparatus

The trust-gate binder-introspection mechanics on `main`:

- `TrustGate.TypeWalk.renderTheoremBinders` (`bin/TrustGate/TypeWalk.lean:117`) —
  `Meta.forallTelescope` over a theorem type, one row per top-level binder.
- `cmdPrintGlobalBinders` (`bin/TrustGate/Main.lean:227`) and the
  `print-global-binders` subcommand dispatch (`Main.lean:328-330`).

The mechanics (`runMeta` / `forallTelescope` / structure introspection) are
reusable for the rebuild's recursive (Option X) deep renderer. **Note:** the
deep `construction_<op>`-targeted variant of the gate is a PR2-only artifact and
is **not** clean salvage — see "blind baseline" below.

### Packed byte-chain lemmas

Already-proven on `origin/main` (not P4-specific); the data effect reuses them to
derive the circuit-internal rd arithmetic from the packed provider lanes:

- `binary_and_chunks_eq_bv_and_of_wf`
  (`origin/main:ZiskFv/Airs/Binary/BinaryPackedCorrect.lean:419`)
- `binary_or_chunks_eq_bv_or_of_wf` (`BinaryPackedCorrect.lean:496`)
- `binary_xor_chunks_eq_bv_xor_of_wf` (`BinaryPackedCorrect.lean:573`)
- `binary_add_chunks_eq_bv_add`
  (`origin/main:ZiskFv/Airs/Binary/BinaryAddPackedCorrect.lean:176`)
- `binary_ltu_chunks_eq_bv_ult_of_wf` (`BinaryPackedCorrect.lean:1654`)
- `binary_lt_chunks_eq_bv_slt_of_wf` (`BinaryPackedCorrect.lean:1910`) — the SLT
  chain that templates the missing Binary-EQ aggregation prerequisite.

---

## NOT clean salvage (must be rewritten, not lifted)

These pieces source from or embody the smuggling pattern. They must be
**rewritten** to source from honest top-level binders, not cherry-picked as-is.

### The `exists_construction_*_from_balance` wrappers

All **28** `exists_construction_*_from_balance` wrappers in
`origin/endgame-p4-pr2:ZiskFv/Compliance/AcceptedTrace.lean` (e.g.
`exists_construction_sub_from_balance` at `AcceptedTrace.lean:10046`,
`exists_construction_xor_from_balance` at `:9982`,
`exists_construction_add_from_balance` at `:10008`). Although they call the
genuine Layer-A wrappers, they source their **pins** via
`MainRowProvenance.*Pins_of_extracted_shape` off the smuggled record. They must
be **rewritten** to source the pins from the honest top-level binders (the §2
SUB residual budget), not lifted as-is. The Layer-A wrapper they call IS clean
salvage; the `from_balance` outer wrapper is not.

### Every `*RowBinding` / `MainRowProvenance` construction

The 37 `*RowBinding` structures (`git show
origin/endgame-p4-pr2:ZiskFv/Compliance/AcceptedTrace.lean | rg -c "structure
.*RowBinding"` → `37`) and the `MainRowProvenance` record they carry are the
smuggling vector itself — fully caller-supplied decode/activation bundles handed
in as premises. They are the shape the rebuild **removes**, not reuses. No
`*RowBinding` / `MainRowProvenance`-style deep record may carry a bucket-(a) or
bucket-(c) fact in the rebuild.

### Every `construction_<op>` relabel

`construction_beq` (`origin/endgame-p4-pr1:ZiskFv/Compliance/AcceptedTrace.lean:143`)
and every family analogue. The proof term uses only `binding.<op> i h_tag` and
threads its fields straight into `OpEnvelope.*OfExtractedShape`; `trace.constraints`
/ `trace.balanced` are dead (zero references in PR1's `AcceptedTrace.lean`). These
are the relabel and are discarded.

### The blind construction-binder baseline

`trust/generated/baseline-construction-theorem-binders.txt` and
`trust/scripts/check-construction-theorem-binders.sh` (both **PR2-only**, not on
`main`). The gate snapshots only the 4 top-level binders of `construction_beq`
and never recurses into `ProgramBinding` / `*RowBinding` / `MainRowProvenance`,
so the smuggling is invisible. The baseline gives false assurance and must be
**regenerated** against the rebuild's recursive (Option X) deep renderer, not
reused.

---

## Salvage boundary, in one line

Clean salvage = Layer-A binding wrappers + Layer-B axiom-free permutation
theorems + the `mainOfTable` column bridges + `AcceptedTrace` + the TrustGate
apparatus + the packed byte-chain lemmas. NOT clean salvage = the 28
`exists_construction_*_from_balance` wrappers (rewrite to source from honest
binders), every `*RowBinding` / `MainRowProvenance` construction, every
`construction_<op>` relabel, and the blind construction-binder baseline.
