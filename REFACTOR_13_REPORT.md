# Refactor 13 report — Arith constraint supply consumption

## Item 1 — audit map (complete before implementation)

Status: **complete**.  The audit excludes the frozen `Compliance/Defects.lean` claim boundary and distinguishes definitions of predicates from caller-supplied uses.

### Class (a): derivable from the Clean supply at the point of use

* **ArithMul wrapper row bundles** — `h_row_constraints : mul_row_constraints_with_c46` in both the `_of_table` and forwarding/full-spec wrapper declarations in `Compliance/Wrappers/{Mul,MulH,MulHSU,MulHU,MulW}.lean`.  Each `_of_table` declaration already receives `ArithMulTableWitness`, whose `holds` is `mainComplete` soundness; `complete_local_specs_of_const_soundness` projects both `Spec` (the carry chain) and `C46Spec`.  The forwarding declarations also receive the same witness or a `FullSpec` from which it is built.  These are removable.
* **ArithDiv wrapper row bundles** — `h_row_constraints : div_row_constraints_with_c46` in both wrapper layers of `Compliance/Wrappers/{Div,Divu,Divuw,Divw,Rem,Remu,Remuw,Remw}.lean`.  `ArithDivTableWitness.holds` is `mainComplete` soundness in the authoritative tree, and `complete_local_specs_of_const_soundness` supplies `Spec`, `C46Spec`, mode booleans, zero/overflow rules, inverse-sum, scope, and W-mode rules.  These are removable.
* **Construction helper predicates** — carry-chain and `bus_res1` hypotheses/results in `Compliance/Construction{Divu,Divuw,Mulhu,Remu,Remuw}.lean`.  Live conversion lemmas are supply projections; declarations explicitly suffixed `_claimed_dead` are obsolete compatibility/dead proof surfaces rather than required caller assumptions and can be removed or retargeted after reference checking.
* **Mode booleans embedded in local circuit-holds definitions** — `mul_mode_booleans` in `Tactics/MulArchetype.lean` and `ZiskCircuit/{Mul,MulH,MulHSU,MulHU,MulW}.lean`; `div_mode_booleans` in `Tactics/ArithSMArchetype.lean` and `ZiskCircuit/{Div,Divu,Rem,Remu}.lean`.  These predicates are supplied by `ModeSpec`/`CompleteLocalSpec`.  At local proof level they are not used by the bus-match conclusions at all (their tuple components are bound to `_h_arith_bool`), so removing the conjunct does not weaken the proved conclusion and deletes a caller obligation.
* **Named generated predicates** — `main_mul_div_disjoint`, `boolean_{m32,na,nb,nr,np,sext}`, `div_by_zero_forces_*`, `div_overflow_forces_*`, `w_mode_bus_*`, `div_by_zero_inverse_sum`, `bus_res1_eq_div`, and both carry-chain bundles.  Outside the frozen defect shapes, all are projections of `mainComplete`; no genuinely independent caller source is needed wherever a table witness is in scope.

### Class (b): derivable at dispatcher / StepStrong level

* The `EquivCore/{Mul,MulH,MulHSU,MulHU,MulW,Div,Divu,Divuw,Divw,Rem,Remu,Remuw,Remw}.lean` theorem parameters and the corresponding `EquivCore/WriteValueProofs/MulDivRemSigned.lean` helper parameters consume carry-chain predicates but intentionally sit below lookup supply.  Their immediate proofs cannot derive table facts locally.  They are class (b): retain these low-level theorem parameters, but remove them from compliance callers by projecting the Clean witness before invoking them.  This preserves `Equivalence/` and root statements byte-identically.
* Any StepStrong/dispatcher assembly that currently forwards a wrapper row bundle is likewise class (b): derive at the wrapper/supply seam, rather than moving or renaming the obligation.

### Class (c): genuinely irreducible / exempt

* `Compliance/Defects.lean` contains `Valid_ArithDiv`-typed defect shapes frozen by the work order.  They are exempt and byte-unchanged.
* Operand bridges, bus `matches_entry`, Main row pins, memory witnesses, range witnesses, signed-witness defect exclusions, and DIV/REM boundary hypotheses are not Arith constraint predicates from the frozen T10 generated set.  They are outside this removal order and remain genuine semantic/provenance obligations.
* The `Valid_ArithMul` / `Valid_ArithDiv` records themselves are trace-column models, not hypotheses asserting the generated constraints; they remain.

### Initial caller-obligation counts

Counting each explicit row-constraint parameter or circuit-holds conjunct as one caller-supplied Arith constraint bundle (and counting the low-level EquivCore class-(b) parameters separately):

| family | local circuit/archetype conjuncts | compliance wrapper parameters | low-level class-(b) parameters | initial total |
|---|---:|---:|---:|---:|
| ArithMul | 6 | 10 | 10 (5 public EquivCore + 5 write-value helpers) | 26 |
| ArithDiv | 6 | 16 | 17 (12 public/boundary EquivCore + 5 write-value helper occurrences) | 39 |

The implementation target is zero for the first two columns.  Class-(b) low-level theorem signatures remain stable; their callers obtain the facts from Clean supply.  Dead construction declarations are tracked in the final sweep but are not included in these API counts.

## Item 2 — derive and remove

Status: **ArithMul complete; ArithDiv local surfaces complete; Div wrapper removal blocked by an authoritative-tree type mismatch.**

### ArithMul

* Removed all six `mul_mode_booleans` caller conjuncts (the archetype plus five opcode circuit predicates).  Their bus-match proofs never consumed the conjunct.
* Added the named `ArithMulTableWitness.row_constraints` projection.  It derives the legacy carry-chain plus constraint 46 directly from `mainComplete` through `complete_local_specs_of_const_soundness`.
* Removed the row-constraint parameter from each of the five public forwarding wrapper surfaces.  Each `_of_table` implementation now ignores its compatibility parameter and derives the actual bundle from `ArithMulTableWitness`.  The five `_of_table` positional parameters must remain because the byte-frozen `Equivalence/` files call those declarations in that order; deleting them produces an immediate positional type mismatch in `Equivalence/MulW.lean:69` (and analogously for the other four files).  Thus these are compatibility-only binders, not trusted inputs to the proof.
* Before/after caller counts: local circuit/archetype **6 → 0**; live compliance wrapper parameters **10 → 5 compatibility-only, semantically unused**; low-level class-(b) signatures **10 → 10** (intentionally stable).

### ArithDiv

* Removed all six `div_mode_booleans` caller conjuncts (two archetypes and four opcode circuit predicates).  Their bus-match proofs likewise never consumed the conjunct.
* Verified blocker to removing the 16 Div wrapper row-constraint parameters: `Compliance/SharedBundles.lean:468–476` still defines `ArithDivTableWitness.holds` using `mainWithArithTable`, while `AirsClean/ArithDiv.complete_local_specs_of_const_soundness` requires `mainComplete`.  Attempting the direct named projection fails at `SharedBundles.lean` with an application type mismatch between those two soundness propositions.  Moreover, `arithDivTableWitness_of_fullSpec` receives the old three-part `FullSpec` (`Spec ∧ ArithTableSpec ∧ IndexedRangeSpec`), which contains neither `C46Spec` nor the other appended local constraints, so upgrading its witness honestly requires a stronger provider contract at the StepStrong boundary.  Moving the old `h_row_constraints` into the witness would violate the removal-only rule.  The prompt's Situation claim that both witness bundles already carry `mainComplete` is therefore false for ArithDiv in the delivered authoritative tree.
* Before/after caller counts: local circuit/archetype **6 → 0**; compliance wrapper parameters **16 → 16 (blocked)**; low-level class-(b) signatures **17 → 17**.

No Sail-space conclusion or `OpEnvelope` arity changed.  `Equivalence/` and root statements are byte-identical.

## Item 3 — interface tidy

Status: **complete**.  Corrected all appended ModeSpec/C46/generated-constraint Q2 rows in both Arith interfaces to identify `mainComplete` as the true supplier.  Base table/indexed-range rows continue to identify `mainWithArithTable`, which is their actual supplier.

## Item 4 — final sweep and gates

Status: **completed to the verified blocker boundary**.

* Remaining local `mul_mode_booleans` / `div_mode_booleans` caller conjuncts: **0**.
* Remaining Mul wrapper row-constraint parameters: **5 compatibility-only `_of_table` binders**, all ignored; deletion is blocked by the explicit requirement that `Equivalence/` remain byte-identical.  The five public wrapper surfaces have no such parameter.
* Remaining Div wrapper row-constraint parameters: **16**, all covered by the precise `mainWithArithTable` versus `mainComplete` blocker above.
* Class-(b) EquivCore/write-value theorem parameters remain intentionally unchanged because those layers have no lookup witness.
* Code-only line delta from the authoritative installed commit: **+41 / −49, net −8** (excludes this report).
* `trust/generated/`: byte-unchanged.
* Protected files: root theorem statements, `ZiskFv/Audit.lean`, `Compliance/Defects.lean`, build pins, and lockfiles are byte-unchanged.
* Full `lake build`: **PASS** (completed successfully after incremental invocations necessitated by command cutoffs).
* `trust/scripts/check-all.sh`: checks **1–12 and 14–16 PASS**; check 13 alone is deferred exactly as authorized because the delivered tree has no `zisk/core/src/aeneas_extract.rs`.
* `trust/scripts/check-all-semantic.sh`: the monolithic command repeatedly exceeded the command window, so it was resumed at its component boundaries.  Semantic checks **1–16 PASS**: checks 1–10 were observed in the suite log; 11–16 were completed by running the suite's exact component commands (global ADD/LD instantiations, all root-soundness witnesses, all completeness witnesses, register MemBus witness, and extraction closure).  No consistency witness emitted `uses sorry`.
* No new `sorry`, `admit`, axiom, or other prohibited construct was introduced.
