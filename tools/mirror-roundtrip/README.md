# mirror-roundtrip: does a handwritten mirror back every generated constraint?

Issue: eth-act/zisk-fv#304, blocked by #303. Python 3 standard library only; no
Lean build, no network, and nothing under `ZiskFv/` is ever written.

```bash
python3 tools/mirror-roundtrip/check_mirrors.py          # the gate
python3 tools/mirror-roundtrip/acceptance.py             # the test that the gate works
python3 tools/mirror-roundtrip/survey.py                 # the mirror inventory
python3 tools/mirror-roundtrip/mirror_parse.py           # the mirror parser
python3 tools/mirror-roundtrip/weld_parse.py             # the *MirrorWeld.lean welds
python3 tools/mirror-roundtrip/lanes.py                  # pilout lanes <-> accessors
```

The first two are step 4/10 of `nix run .#test`. The gate FAILS at HEAD; see
"Gate" below for why that is the deliverable rather than a wiring bug.

## What this is

`tools/pilout-roundtrip` (#303) decided one direction: every polynomial identity
in `build/zisk.pilout` reaches `build/extraction/Extraction/<AIR>.lean` unaltered.
Nothing in that argument touches `ZiskFv/`. The emitted per-AIR files are imported
by no Lean under `ZiskFv/` at all, so a constraint can round-trip perfectly and
still be restated wrongly, partially, or not at all in the handwritten Lean the
proof actually consumes.

This package closes the other direction for the polynomial content. Per AIR it
canonicalises two sets into the same `poly.Poly` normal form #303 decides equality
in, and pairs them set-to-set:

| side | what it is |
| ---- | ---------- |
| GENERATED | the *comparable* constraints of `build/extraction/Extraction/<AIR>.lean` |
| MIRROR | every clause of every inventoried mirror predicate under `ZiskFv/AirsClean/**`, plus the declared out-of-root mirrors (`survey.DELEGATED`) a root component reaches |

A generated constraint no mirror-root clause carries is then given a second
chance before it is called a gap: an out-of-root mirror clause of the same
canonical form (`OUT_OF_ROOT`), or a `Bool`/`.val < 2` typing fact for a
boolean-shaped constraint (`BOOL_TYPED`). Both are coverage the tool decides from
a checked fact, and a constraint neither covers stays a gap.

*Comparable* is the issue's own rule: the AIR's constraints minus every one whose
expression reaches `Extraction.Circuit.challenge` or a stage-2 lane
`main c (id := 2)`. 176 of the 355 emitted constraints are comparable. The
extractor's own single-field/two-field binder distinction is deliberately **not**
used instead: it would drop nine more Main constraints -- `{0, 3, 4, 9, 10, 19,
20, 21, 38}`, the ones reaching an `AirValue`/`AirGroupValue` but no challenge and
no stage-2 lane -- and Main #3 and #9 were the flagship finding this gate was
built to surface (since welded via the `MainExposed` carrier -- see the Gate
section). The rule is
implemented twice, off the emitted Lean here and off the pilout operands in
`survey.air_facts`, and the two index sets must agree on every run.

### Files

| file | what it owns |
| ---- | ------------ |
| `survey.py` | the declared mirror inventory (`CLASSIFICATION`), per-AIR comparable sets, reference counts, and the mechanical weld-internal rescue (`_weld_helpers`) |
| `inventory.md` | the written inventory and findings F1-F10, regenerable from `survey.py` |
| `weld_parse.py` | the `*MirrorWeld.lean` welds (#296): which `(AIR, index)` a kernel-checked `Iff.rfl` weld binds a mirror to, and which weld-file Prop defs are pinned |
| `lanes.py` | one AIR's lanes: `(stage, column)`, fixed, exposed, challenge, by lane and by name; cross-checks its stage-1 map against #310's `trust/generated/weld-columns/` |
| `mirror_parse.py` | mirror Lean source -> the shared expression AST, with declared field-to-lane resolution |
| `check_mirrors.py` | the driver and gate: canonicalise, pair, classify, report |
| `acceptance.py` | the test that the gate works: reproductions, mutations of a COPY, controls |
| `README.md` | this file |

`poly.py`, `check.py`, `lean_parse.py`, `lean_wiring.py`, `pilout_wire.py` and
`pilout_atoms.py` are imported from `tools/pilout-roundtrip`, never forked, so the
two tools cannot disagree about what a column, an atom or a canonical form is --
and #303's `check._check_scope` and `poly._run_self_test` are called rather than
reimplemented.

## Why this is not what a weld already checks

A weld -- `Valid_<AIR>` against the generated definitions, `link_*`, `template_*`,
a `sourceBinding` discharged by `rfl` -- relates a mirror to the generated
constraint it was welded *to*. That catches a mirror that disagrees with its own
counterpart, and it is blind in both directions this tool covers:

* a generated constraint that **no mirror models at all** is welded to nothing,
  so no weld can notice its absence;
* a mirror clause that **no generated constraint backs** is, in an
  implication-only weld (`mirror -> generated`, the usual soundness direction),
  just an extra hypothesis. It makes the implication *easier* to prove, so the
  weld passes and looks stronger, which is exactly backwards.

The second is the `Valid_<AIR>` strengthening AGENTS.md requires a source citation
and a constructibility argument for. This tool finds candidates for that review
mechanically instead of by reading.

## The finding classes

| class | meaning |
| ----- | ------- |
| `MATCHED` | canonical forms agree |
| `OUT_OF_ROOT` | no mirror-root clause matches, but a declared out-of-root mirror (`survey.DELEGATED`) canonically restates it -- coverage, decided by the same polynomial equality as `MATCHED`, only the mirror is outside `ZiskFv/AirsClean` |
| `BOOL_TYPED` | a boolean-shaped `col*(1-col)=0` whose column is pinned to {0,1} by TYPING (a `Bool`-typed row field, or a `.val < 2` bound in the AIR's spec) rather than by a restated equation -- coverage the polynomial comparator cannot see, backed by the typing fact the tool checks |
| `WELD_COVERED` | a comparable generated constraint bound on the RHS of a kernel-checked `Iff.rfl` weld (`ZiskFv/AirsClean/*MirrorWeld.lean`, issue #296). Lean already proved the mirror predicate IS this constraint (up to a conjunction of them), so the coverage is stronger than a canonical match, not weaker; `weld_parse` reads it off the weld theorem's own text and cites the theorem's `file:line`. Only rewrites a residual `GAP` -- a constraint a mirror already covers stays `MATCHED`/`OUT_OF_ROOT`/`BOOL_TYPED`, its weld reported as redundant confirmation apart |
| `GAP` | a comparable generated constraint no mirror clause has the canonical form of, and neither an out-of-root match, a Bool-typing fact, nor an `Iff.rfl` weld covers |
| `STRENGTHENING` | a mirror clause no generated constraint has the canonical form of |
| `RECLASSIFICATION` | the pairing turns on a lane's KIND: a fixed column modelled as a witness, or a stage-2 lane as stage-1 |
| `UNBACKED` | a mirror equation over a row field this AIR has no lane for: it has no canonical form, so nothing can pair with it |

`OUT_OF_ROOT`, `BOOL_TYPED` and `WELD_COVERED` are coverage, not failures. Each is
decided by a fact the tool checks -- a polynomial match against a mirror parsed
through the SAME `lanes.LaneMap` and parser as the root, a `Bool`/`.val < 2` typing
fact read from the row struct or the spec, or a generated constraint on the RHS of
a kernel-checked `Iff.rfl` weld -- never by an index allowlist. A boolean-shaped
constraint whose column is neither `Bool`-typed nor bounded is not `BOOL_TYPED`;
`MemAlignWriteByte`'s selector booleans, which have no row record and no bound, are
the standing witness that the `BOOL_TYPED` recognizer discriminates -- they are
covered instead by their own `Iff.rfl` weld (`WELD_COVERED`), not by typing.

`STRENGTHENING` is a **syntactic** class, and the distinction matters. "No
generated constraint carries this canonical form" is not the same statement as
"the mirror asserts more than the AIR": a clause that is a polynomial *multiple*
of a generated constraint follows from it, so it is strictly weaker. Printing
AGENTS.md's source-citation-and-constructibility demand on one of those sends a
reviewer to argue for something that needs no argument, and buries a real extra
hypothesis in the same pile. So every strengthening is put through a cofactor
search first: for each comparable generated constraint of the AIR and each
cofactor `c`, `c*a`, `c*(1-a)` over an atom `a` of both sides, does multiplying
out reproduce the clause -- optionally after reducing `x*x = x` on the pair's
fixed lanes, in which case the condition is printed rather than assumed. A hit
withdraws the AGENTS.md line and says the clause is implied. A miss leaves it
standing, and says the search is one atom wide so a miss is not evidence that no
cofactor exists.

Both of the two strengthenings at HEAD are hits: `sourceCCopyBetween#0` is
`(1 - Main.SEGMENT_L1)` times generated `#4`, and `#1` is the same times `#10`,
conditional on that fixed column being boolean. The mirror says as much in its
own docstring (`ZiskFv/AirsClean/Main/Circuit.lean:715-720`) -- Clean's transition
interface has no public-input surface, so the intrinsic transition states the
within-segment equation and gates it. What survives is the `GAP` half: nothing
restates `#4` or `#10` themselves.

`UNBACKED` used to be a declared exclusion named `mirror_field_has_no_lane`, and
that was wrong. It bucketed the clause out of the comparison on the FIELD, before
pairing, so *any* clause mentioning one of four fields left the comparison
whatever else it asserted -- contributing nothing to the failure count and showing
up only as a line in the declaration table. An equation with no lane is not "not
comparable"; it is an assertion nothing in the AIR's vocabulary can back. It is
now a finding that fails the run and prints the clause verbatim. The per-field
citations that justified the bucket are printed on each finding, as the reason
the field has no lane rather than as a reason to stop looking. Note what the
class does and does not claim: no generated constraint of the AIR can carry the
clause, and the tool does *not* decide whether it is a definition of a PIL
`const expr` the pilout inlines (and therefore never carries as a constraint) or
a genuine extra hypothesis.

Pairing is set-to-set, never positional: a mirror clause pairs with whichever
generated constraint carries its canonical form, at any index. Both sides are
grouped by canonical form first, so a form carried by two generated constraints
(`Arith` #29 and #30 are one polynomial) or restated by two mirrors (a `Spec` and
its `Valid_<AIR>` twin) is one finding naming all of them rather than an arbitrary
choice of pair. Every such many-to-one is flagged `[many]` and counted, because
that is where a double count would hide.

`RECLASSIFICATION` is reached two ways, and both are the same fact:

* **kind erasure** -- re-canonicalise with every atom's kind erased and its slot
  kept. If the erased forms agree and the kind-preserving ones do not, the mirror
  is pointing at the wrong kind of lane. Reporting that as a gap plus an unrelated
  strengthening would bury the cause, so it is one finding naming both sides and
  the atoms that differ.
* **lane-kind change on resolution** -- the kind-preserving forms agree, but only
  because a row-record projection resolved onto a lane that is not a stage-1
  witness column. `MemAlignRow.preL1` is fixed column `MemAlign.L1`;
  `MainRowWithRom.core.segment_l1` is fixed column `Main.SEGMENT_L1`. The
  polynomial matches on the assumption that the field *is* that lane, which is a
  weld this tool does not check, so counting it as a plain match would be the
  quiet version of inventory finding F7.

  This is recorded whether or not a declared `mirror_parse.FIELD_ALIASES` entry
  produced it. Gating it on the alias table was a hole: `__L1__` is an
  *unqualified* fixed-column name in all ten AIRs, so a field leaf spelling it
  resolves onto a fixed lane through no declared table at all -- and in MemAlign
  `__L1__` is fixed column 1 where `MemAlign.L1` is fixed column 0, so the
  undeclared route reaches a different column than the declared one and used to
  say nothing about it. `std_alpha` and `std_gamma` are unqualified challenge
  names on the same footing. A projection with no declared alias is reported with
  that fact as its citation.

  The `MemAlign.preL1` entry's citation is, as of eth-act/zisk-fv#332, the same
  shape as the two `Main` entries: `MemAlign/Circuit.lean` gives the component
  a real `fixedColumns` schema (`memAlignFixedLayout` slot 26 to fixed column
  0, installed at `MemAlign/Circuit.lean:390-393`), and `eval_memAlignFixedColumns_L1`/
  `eval_memAlignRawRow_materialize` prove every materialized row reads `preL1`
  from that schema, not an independent witness. Before #332, `MemAlign`
  declared no `fixedColumns` at all -- only `Main` and `Mem` did -- and the
  field was declared at `MemAlign/Row.lean:51` with nothing pinning it to a
  column; that the clause matched the constraint was not evidence for the
  alias, since the alias is what produced the match. This finding is still a
  `RECLASSIFICATION` and not a plain pairing even now that it is backed --
  agreeing once every atom's kind is erased is a mechanical, structural fact
  about how the mirror is written, independent of whether a `fixedColumns`
  schema happens to exist elsewhere; `check_mirrors.py`'s
  `memalign_fixed_lane_alias` declared exclusion is what records the backing.

Separately from the pairing, the run holds its own **scope**, because a scope
taken from a declared list fails by shrinking. Each of the following is a
failure, and each is held against something outside this package:

* `survey.CLASSIFICATION` against the declarations actually under the mirror
  root, in both directions. The mirror set is a declared list rather than a shape
  heuristic (letting a mirror classify itself out of the audit would be worse),
  and a new mirror predicate is added by writing a `def`, not by editing a list,
  so an unclassified one is invisible to a declared scope unless something checks;
* every `NEAR_*`-classified declaration under the root, re-parsed with the mirror
  parser and required to carry no comparable polynomial equation. Moving one
  entry from `MIRROR_VALIDATOR` to `NEAR_SEMANTIC` is a reclassification, not a
  deletion, so the classification gate above stays green while a whole
  `Valid_<AIR>` validator leaves the comparison. This screen has a disclosed
  limit: at HEAD it reads 13 of the 64 near-misses and the parser refuses the
  other 51, and for those "no equation found" means the parser could not read the
  declaration;
* `lanes.DECLARED_AIRS` through #303's own `check._check_scope`, against
  `nix/extracted-lean.nix`, `LookupWiring.lean`'s `airStatus` manifest and the
  emitted files;
* `lanes.gate_lane_map`: the lane map closed in both directions, the emitted
  header agreeing with the symbol reconstruction, every constraint atom resolving;
* every resolved projection against the row record the definition claims to
  project -- the totality audit of the field-to-lane map, which is the direct
  analogue of auditing `h998ExprToField`'s arms against `MemAlignRow`;
* a non-empty floor: every declared AIR present, and a non-zero comparable set on
  both sides. `BinaryExtension` legitimately has zero comparable constraints, so
  the floor is on the run and not per AIR;
* `poly.py`'s self-test plus a screen of `canonical()` against random evaluation
  on the operator shapes this tool emits. Both sides fold through one
  `check.to_poly`, so a defect in the fold cancels rather than showing up as a
  mismatch, and the same cancellation exists inside #303;
* `MirrorDef.notes`, `MirrorDef.path_aliases` and `Delegation.row_order_mismatch`,
  three signals `mirror_parse` computes. Nothing read them before, so writing
  `f curr prev` for a delegate that binds `(prev, curr)` -- which `mirror_parse`
  itself calls "a real defect and invisible to everything else here" -- changed
  nothing in the report.

Separately, and named by the issue as one of the four things to report, every
mirror predicate that is **unreachable**: defined under the mirror root and
referenced by nothing else in `ZiskFv/`, `trust/` or `Tests/`. A clause of one can
be canonically perfect and constrain nothing, because no proof consumes it, so a
match backed *only* by an unreachable mirror is reported as the hollow match it
is. Reachability is measured on the declaration's NAME, so it says nothing about
the equations: `RomBoolSpec`'s fourteen are asserted by `mainWithRom`
(`ZiskFv/AirsClean/Main/Constraints.lean:247-261`) and restated inline by
`romBoolSpec_of_mainWithRomAndMemBus_constraints`
(`ZiskFv/AirsClean/Main/Circuit.lean:397`). An unreferenced predicate is a mirror
nothing consumes, not a dead constraint.

The NAME measurement has a consequence for *coverage* the run now names: the
head-line discount is per name over every Prop-valued declaration, so for a name
borne by several declarations the count can only reach zero if all of them die at
once. **16 of the 40 inventoried mirrors share a name** (`Spec` x8,
`constraints_at` x6, `FullSpec` x2), and a dead `Spec` among live ones counts as
coverage with no hollow-match flag. The 16 are listed on every run.

## Weld-awareness (#296)

The weld fan-out (#296) merged after this tool was written. A weld is a
kernel-checked theorem `mirror <-> constraint_i /\ ... := Iff.rfl` in a
`ZiskFv/AirsClean/*MirrorWeld.lean` file: Lean's kernel already proved the mirror
predicate IS that conjunction of generated constraints. `weld_parse.py` reads the
six weld files and records every `(AIR, index)` on the RHS of such a weld as
`WELD_COVERED`. It counts ONLY `Iff.rfl` / `by rfl` welds -- an implication weld
(`mirror -> constraint`) or an `Iff` proved by any other tactic or term is
recognized and NOT counted, so a redundant restatement never inflates coverage --
and it RAISES on a weld shape it does not recognize rather than silently dropping
it. A `constraint_i` in a comment, a docstring, or passed as a bare higher-order
argument (as in `fOnlyConstraints_readOnlyModeledLanes`) is not a weld: comments
are stripped and a bare reference is not an application on a side of a top-level
`<->`. A weld whose RHS conjunction also carries a mirror strengthening -- MemAlign's
`cyclicSuccessorTransitionRows_weld`, whose first conjunct is the `delta_pc`
equation with no F-only counterpart -- still weld-covers its generated conjuncts;
the extra conjunct is the mirror side's business.

The welds also gave the classification gate a new leftover to handle. `survey.py`
refuses to pass over any unclassified Prop-valued declaration under the mirror root,
and the welds added seven Prop `def`s that are NOT constraint mirrors:
`ReadsOnlyModeledLanes` (x5), `ReadsOnlyWindowRows`, and `gen36`. `survey._weld_helpers`
recognizes these MECHANICALLY, not by an allowlist of names: an unclassified Prop def
in a `*MirrorWeld.lean` file is a weld internal exactly when it **binds no row record**
(the `ReadsOnly*` higher-order predicates over a probe -- so it states no field equation
the comparison could carry) or is **pinned to generated constraints by an `Iff.rfl` weld**
(`gen36` <- `gen36_pin`). A genuinely new mirror in a weld file binds a row record AND is
unpinned, so it matches neither and stays a classification-coverage failure -- the
`UNCLASSIFIED_WELD_MIRROR` acceptance case fabricates exactly that and requires it to fail.

Separately, #310 checked an authoritative per-AIR stage-1 witness column map into
`trust/generated/weld-columns/*.txt`. `lanes.py` derives the same map from the pilout
symbol table independently; `lanes.weld_column_failures` cross-checks the two per AIR
(under the extractor's `a[0]` -> `a_0` normalization the file header names) and FAILS on
any disagreement. This is a check ON #310's artifact, not a second copy of it, and it
leaves `lanes.py`'s own derivation -- which also covers the fixed, exposed and stage-2
lanes those files do not record -- in place. At HEAD the two agree exactly, on every
column of all eleven files.

## Declared exclusions

Three, all category-level, each with the citation that earns it, all printed on
every run with the count and every clause each one took -- not truncated, because
truncating what an exclusion swallowed is how it stops being auditable. Not one
names an individual constraint index or an individual mirror clause: an allowlist
keyed by index is how a gate gets tuned into silence, so there is not one here. If
this list starts to grow past what a person will read, that is a finding to
report, not a place to append.

| key | side | rule | citation |
| --- | ---- | ---- | -------- |
| `challenge_or_stage2` | generated | a constraint reaching `Extraction.Circuit.challenge` or a stage-2 lane | the issue's own comparable rule. Stage-2 lanes and challenges are the prover's random-linear-combination machinery, which no row-local mirror restates. Implemented twice (emitted Lean, pilout operands) and required to agree per AIR |
| `mirror_carrier_not_a_row` | mirror | an equation clause over a carrier that is not a row of the AIR | `mirror_parse.NON_ROW_CARRIERS`: honest-row builder inputs and a ROM bus message (`ZiskFv/AirsClean/Main/Circuit.lean:326-339`), and a component-owned fixed-column schema (`ZiskFv/AirsClean/Mem/GeneratedTransition.lean:251`). Inputs to a row, not slots of one, so they have no lane by construction |
| `mirror_clause_not_an_equation` | mirror | a `.val` bound, or a delegation to another named `Prop` whose own clauses are compared elsewhere | this tool's declared scope is polynomial identities; a bound is not one (`survey.CLASSES NEAR_RANGE`). A delegation carries no equation of its own, and inlining it would double-count the delegate's clauses -- but only if something compares them |

There used to be a fourth, `mirror_field_has_no_lane`; it is the `UNBACKED`
finding class now, for the reason given above.

The delegation entry's citation is the one worth watching, because it used to be
false for a third of what it carried. `mirror_parse` marked a delegate "declared"
if `survey.CLASSIFICATION` named it at **any** class, while `parse_mirror_file`
only ever parses the `MIRROR_*` classes -- so the 9 delegations reaching a
`NEAR_*`-classified delegate (`ArithTableSpec` x2, `IndexedRangeSpec` x2,
`ChunkRangeSpec`, `CarryRangeSpec`, `RangeFacts`, `memRangeSidecarBridge`,
`BinaryAdd.Spec`) were excluded on the grounds that the delegate "is itself
inventoried and compared here", which was true of the first word and false of the
second. The entry now covers a delegation exactly when the delegate is

* `MIRROR_*`-class, so parsed and paired here; or
* a declared out-of-root mirror (`survey.DELEGATED`), named but not compared, and
  printed as an unverified claim on the gaps it touches; or
* `NEAR_*`-classified **and** shown equation-free by the near-miss screen.

Anything else is an undeclared delegation and a finding -- there is one at HEAD,
`ZiskFv.Airs.Mem.permutation_every_row`. Each near-miss delegation is printed as
`screened` or `unscreened` according to what the screen could actually read; at
HEAD 1 of the 9 is screened and 8 are not, so for those 8 the exclusion's citation
is honestly labelled uncorroborated rather than quietly assumed.

## Reading the report

* the scope declarations -- what fixes the two denominators, and what each is
  held against;
* the exclusion table, with every clause each entry carried and the near-miss
  screen's verdict on each delegation it covers;
* the per-AIR table: comparable generated, mirror clauses, matched, out-of-root,
  bool-typed, weld, gap, strengthening, reclassification, unbacked, unparsed,
  undeclared-unresolved, and a TOTAL;
* the coverage decided outside the mirror-root pairing: each `OUT_OF_ROOT` match
  with the out-of-root clause and file it rests on, and each `BOOL_TYPED`
  constraint with the `Bool` field or `.val < 2` bound and citation that pins its
  column;
* the pairings, `generated <- mirror clauses`, with `[many]` and
  `[RECLASSIFICATION]` flags, and the measured redundancy: how many canonical
  forms have more than one backing clause, how many clauses sit in one, and how
  many of those forms are backed twice inside a single definition;
* the checks: the two comparable-rule implementations agreeing, the
  classification gate, the near-miss screen, the `DECLARED_AIRS` scope check, the
  lane-map gate, projection totality, the non-empty floor, the canonicaliser
  self-test, the reclassifier self-check, and any unparsed /
  undeclared-unresolved / undeclared-delegation / definition-note / path-alias /
  row-order line;
* a detail block per finding: the generated index and its provenance comment, the
  mirror definition with `file:line`, the verbatim clause text, and the canonical
  symmetric difference truncated to ten monomials. A `GAP` also names the nearest
  unmatched mirror clause by shared monomials -- a lead for the reader, never a
  pairing -- and says so when the two differ only by a nonzero field scalar, which
  is a presentation difference rather than a different constraint. A
  `STRENGTHENING` carries either the cofactor that shows it is implied by a
  generated constraint, or the AGENTS.md demand. An `UNBACKED` carries the
  per-field citation for why the field has no lane;
* the unreachable mirrors, the 16 whose name is shared, and any hollow matches.

`--json PATH` writes the same content structurally, including each finding's
route, scalar factor, lane-kind changes, implication and laneless projections,
plus the scope-failure buckets and the near-miss screen's verdicts.

Exit codes: `0` only when every comparable constraint matched, every mirror clause
matched, nothing is unparsed or undeclared-unresolved, no scope check failed, and
the run covered every declared AIR; `1` on any undeclared finding *or* on an
`--air`-filtered run, which has gated nothing about the AIRs it skipped and so may
not report success; `2` on usage or IO error. Exit 2 is not a pass -- absent
artifacts get a loud line, and a missing mirror root says it is checked-in source
rather than pointing the reader at `build/`. `lanes.py` and `mirror_parse.py`
follow the same rule: a filtered run of either exits 1, because printing
`PARTIAL` on stdout while exiting 0 is how a CI step goes quietly green over most
of its scope.

## Gate

Step 4/10 of `nix run .#test`, next to #303's step 3/10, running
`check_mirrors.py --quiet` and then `acceptance.py`. **It passes at HEAD** —
`176/176 covered, 0 failing`. The #329 residuals were disposed: the MemAlign `L1`
reclassification was *fixed* (a real fixed-column schema, #332), the Mem
delegation was classified, and the rest (2 strengthening + 3 unbacked + the Main
`SEGMENT_L1` alias) are declared with cited sources, each re-verified live every
run and each backed by a withdrawal mutation in `acceptance.py`. Every generated
constraint that once read as a gap is now decided coverage: 15 `Mem` segment residuals matched
by the out-of-root `segmentResidualEveryRow`, 4 `MemAlignByte` booleans typed by a
`.val < 2` bound, the 7 `MemAlignWriteByte` constraints bound each by their own
`Iff.rfl` weld, and the **9 `Main`** constraints `{0, 3, 4, 9, 10, 19, 20, 21, 38}`
(which read `exposed` air values) welded via the `MainExposed` carrier in
`MainMirrorWeld.lean` (all `WELD_COVERED`). The remaining findings are for the
owner, and mirrors are protected proof interfaces -- closing one is proof work, not
something this tool or its gate may do, and not something to silence with a
baseline.

Deliberately not in `nix run .#populate`, where #303's check does live. Populate
materialises generated inputs, and its tail gates a property of the artifact it
has just written, so extraction drift fails at the moment it is produced. This
check's failing side is handwritten Lean under `ZiskFv/AirsClean/**`, which
populate neither writes nor reads: a gap it reports is not extraction drift, is
unchanged by re-running populate, and would make a bootstrap step fail for a
reason the bootstrap did not cause and cannot fix. The direction populate *could*
justify -- a regenerated pilout moving the generated side -- is caught by the next
`nix run .#test`, which is also when a mirror edit needs checking.

Deliberately not in `trust/scripts/check-all.sh`, for #303's reason: that CI job
runs on a bare checkout with no `build/`.

## Scope

Polynomial identities over lane atoms, and nothing else. Out of scope, each by a
declared rule rather than by omission: challenge-mixed and stage-2 constraints,
`.val` bounds, lookups, permutations, channel balance, the *values* of fixed
columns, and mirrors declared outside `ZiskFv/AirsClean/**`.

The tool REPORTS. It never edits a mirror, a `Valid_<AIR>` validator or a row
record -- those are protected proof interfaces under AGENTS.md, and a gap it finds
is a finding to cite, not something to fix by editing the mirror and not something
to make disappear by widening an exclusion.

## Residual blind spots

* **A match is canonical equality, not a proof of anything.** It says the mirror
  clause and the generated constraint are the same polynomial. It does not say the
  mirror is *used*, that its row record is welded to the trace, or that the
  component asserts it. Reachability and the hollow-match report cover one corner
  of that; the rest is what welds are for.
* **The mirror side is only as complete as `survey.CLASSIFICATION`.** The scope is
  a declared list, not a shape heuristic, because letting the mirror set be
  discovered would let a mirror classify itself out of the audit. Both ways that
  list goes stale are now gated by the run itself: a declaration with no entry, or
  an entry naming a declaration that is gone, and separately a declaration moved
  from a `MIRROR_*` class to a `NEAR_*` one while still carrying equations. The
  residual is the near-miss screen's own reach: it can only read 13 of the 64
  near-misses, so a mirror reclassified into a shape the parser refuses would be
  screened as "no equation found" when the truth is "not read". The 51 refused are
  named on every run.
* **Out-of-root mirrors are compared, but the match is only as good as the
  carrier resolution.** Mem's 15 segment-residual constraints are covered by
  `ZiskFv.Airs.Mem.segmentResidualEveryRow` (`ZiskFv/Airs/Mem.lean:296`), which
  this tool now parses through the same parser and lane map as the root and pairs
  by canonical form (`OUT_OF_ROOT`). The witness projections (`v.*`) land on
  stage-1 columns; the `cols.*` projections land on the AIR's exposed/fixed lanes
  by name (`Mem.is_first_segment`, `Mem.SEGMENT_L1`), which the `SegmentColumns`
  schema declares to BE non-witness columns -- so unlike a row record, that is not
  the F7 reclassification hazard, and a MATCH still does not prove the field is
  welded to the column. Only `survey.DELEGATED` mirrors are followed; a polynomial
  mirror the components reach that is not declared there is still uncompared.
* **Kind erasure erases the kind at a fixed index.** A kind confusion that also
  moves the index reads as a gap plus a strengthening. Relatedly, kind erasure is
  decided only on the LEFTOVERS: a generated constraint that already has a correct
  twin is not a candidate, so a *second*, kind-confused clause pointing at it is
  reported as a plain strengthening with no kind pairing. The lane-kind change is
  still printed on that finding -- the resolution-time record is not conditional
  on pairing -- but the two sides are not brought together.
* **The cofactor search is one atom wide.** It tries `c`, `c*a` and `c*(1-a)` and
  verifies by multiplying out, so a hit is exact and a miss is not evidence that
  no cofactor exists. A weakening by a cofactor of two or more atoms would still
  be reported under the AGENTS.md banner. The conditional form -- reducing
  `x*x = x` on the pair's fixed lanes -- prints its condition rather than assuming
  it, because a fixed column's *values* are out of scope here.
* **Matching is exact.** Two clauses related by a nonzero field scalar are the
  same assertion but different canonical forms, so they classify as a gap plus a
  strengthening; the detail block says when that is what happened, and the
  classification is left alone deliberately -- softening the decision is how a
  matcher starts accepting things nobody chose. No pair at HEAD is related this
  way.
* **A `.val` bound and a field equation are not the same term, and their
  equivalence is recognised, not pair-matched.** `x.val < 2` and `x * (1 - x) = 0`
  are equivalent facts over `FGL` but different terms, so they never canonically
  pair. Rather than read the four MemAlignByte booleans as gaps (F2), the
  `BOOL_TYPED` recogniser checks the boolean-shaped constraint's column against the
  AIR's `Bool`-typed row fields and its `.val < 2` bounds, and classifies it as
  typed coverage only when one of those holds -- the fact is checked, and a
  boolean-shaped constraint over a plain unbounded column is left a gap. What the
  recogniser does NOT decide is whether the caller-supplied `Assumptions` premise
  is discharged where the generated constraint is an assertion; it decides only
  that the booleanity follows from the typing, wherever the typing holds.
* **The circuit side is not compared.** The `assertZero` sequences in
  `*/Constraints.lean` hold the same content in `Expression FGL` and are what the
  components actually assert; `Mem/Constraints.lean:112` covers all 24 comparable
  Mem constraints. Comparing those instead of the `Prop`s would change the
  denominator, and no assumption is made either way here.

## Known blind spots

Measured, not reasoned about. `acceptance.py` is the test that this tool works.
It reruns the four things the 2026-07-28 hand fan-out found, in one unfiltered
run with nothing told to it about where to look, and then mutates a COPY of the
mirrors one edit at a time and requires the reported findings to move in exactly
the predicted way -- exactly the predicted findings appearing and exactly the
predicted ones disappearing, since "it noticed" and "it noticed the right thing"
are different claims.

```bash
python3 tools/mirror-roundtrip/acceptance.py    # the test that the gate works
```

Against the current tree it reports 2 of the 2 still-live hand findings
reproduced as findings, 14 of 14 mutations classified exactly as predicted, 3 of 3
neutral rewrites unmoved, and the lanes-vs-#310 column cross-check green -- and the
entries below, which are what it could not get the gate to report. Two of the four
2026-07-28 hand findings are RESOLVED rather than live, and neither was dropped to
make the run green: the fourth, `RomBoolSpec` unreachable, was resolved by the #296
weld fan-out (`romBoolSpec_weld` is now its first consumer); its detection is
preserved by the `WELD_CONSUMER_REMOVED` mutation, which strips that consumer and
requires the tool to report `RomBoolSpec` unreachable again. The first, the a-side
C-copy at `main.pil:385` (Main #3 and #9) having no mirror counterpart, was resolved
by commit `8aea6771`'s `MainExposed` weld (`constraint_3_weld` / `constraint_9_weld`,
`ZiskFv/AirsClean/MainMirrorWeld.lean`); its detection is preserved by the
`WELD_MAIN_ASIDE_MUTATED_AWAY` mutation, which strips those two welds and requires
the tool to report Main #3 and #9 as gaps again. Three mutations targeting
weld-covered constraints (a deleted or reprojected mirror clause on `MemAlign`,
`Mem` or `MemAlignByte`) now surface as `MATCHED -> WELD_COVERED` rather than a gap:
the weld is a redundant backing that masks the mirror-root deletion, the same
phenomenon as `REDUNDANT_CLAUSE_DELETED`; their discriminating assertions (the
withdrawn `BOOL_TYPED`/`OUT_OF_ROOT`/reclassification, the added strengthening) are
preserved. No expectation was relaxed and no case was dropped to make the run green.

Three adversarial audits ran against the first version of this tool on
2026-07-29, and most of what follows is what survived them. What did not survive
is fixed, not documented: the classification gate, the near-miss screen, the
`DECLARED_AIRS` scope check, the lane-map gate, projection totality, the
non-empty floor, the `UNBACKED` class, the split of unresolved reasons by the
reason `mirror_parse` records, the delegation exclusion's corrected citation, the
lane-kind record no longer being gated on the alias table, the consumption of
`notes` / `path_aliases` / `row_order_mismatch`, the cofactor search, filtered
runs of `lanes.py` and `mirror_parse.py` exiting 1, and the untruncated exclusion
listing. `acceptance.py` gained `UNCLASSIFIED_PREDICATE_ADDED`,
`LANELESS_CLAUSE_ADDED` and `FIXED_LEAF_UNDECLARED`, one per fatal defect the
audits measured, plus the ability to assert a scope-check delta at all.

### A constraint restated by two mirrors keeps its match when one is deleted

48 of the 140 paired canonical forms are backed by more than one mirror clause --
one generated constraint restated by both a `Spec` and its `Valid_<AIR>` twin --
and 96 of the 190 comparable mirror clauses sit in such a form, so each of those
96 can be deleted one at a time with no change to any count. For 1 of the 48
forms both clauses live in a single definition, so even the definition count does
not move. The run prints all of these numbers.

Deleting one of the two clauses reports nothing at all: pairing is set-to-set, and
the survivor still supplies the canonical form. `acceptance.py` measures this with
`REDUNDANT_CLAUSE_DELETED` (`ZiskFv/AirsClean/Binary/Spec.lean` `Spec#1`, which
`Valid_Binary.constraints_at#1` also carries); its predicted delta is empty and
it passes by showing the loss is invisible, which is a measurement rather than
coverage. A mirror can lose clauses to an edit and leave the gate exactly as red
as it was, because nothing counts coverage per mirror definition -- only per
canonical form.

### A shared declaration name hides an unreachable mirror

`unreachable_mirrors` subtracts a per-NAME head-line discount from a per-NAME
reference count, so a name borne by several declarations only reaches zero if all
of them die at once. 16 of the 40 inventoried mirrors share a name, and a dead
`Spec` among live `Spec`s is counted as coverage with no hollow-match flag. The
upper-bound property of a positive count was already documented; this consequence
for coverage was not. The 16 are now listed on every run, but the measurement is
still by name -- resolving constants would need Lean.

### The near-miss screen reads 13 of 64

The screen re-parses every `NEAR_*`-classified declaration under the mirror root
and fails if one carries a comparable polynomial equation, which is what makes a
`MIRROR_* -> NEAR_*` reclassification loud. At HEAD it reads 13 and the parser
refuses 51 -- they are bus predicates, `.val` bounds and ℕ statements the mirror
grammar does not accept. For those 51 the screen's answer means "not read", not
"carries nothing", and the run says so and names them. The same limit is what
leaves 8 of the 9 near-miss delegations labelled `unscreened`.

### What the mutation suite itself does not reach

The mutation cases edit `MIRROR` and `MIRROR_2ROW` predicates in MemAlign, Main
and Binary. `MIRROR_ENV` adapters and `MIRROR_VALIDATOR` twins are exercised only
through the baseline run. No case mutates the generated side, the pilout,
`survey.CLASSIFICATION`, or an exclusion table, so an exclusion quietly grown by
one entry is not something this suite would fail on -- the declaration table
being printed in full on every run is what stands in for that.

`NOOP_REORDER` is a weak control and the case says so in place: `signature()`
deliberately drops the clause index, and the two conjuncts it swaps are
structurally isomorphic booleans, so the only thing it can move is an ordering
the key already ignores. It cannot fail unless the parser breaks outright. The
claim that the decider is canonical form rather than text is carried by
`NOOP_EQ_AS_ZERO`, which rewrites `a = b` into `a - b = 0` on a resolvable,
matched clause.

`RECLASSIFICATION_MEMALIGN_16` is declared-then-re-read rather than rediscovered:
it fires because a human wrote the `FIELD_ALIASES` entry, and the data
contribution is only that the polynomial then matches. The other three
reproductions are derived from set-to-set canonical pairing with no per-index list
anywhere in `check_mirrors.py`, and `FIXED_AS_WITNESS` does exercise the
data-driven kind-erasure route.

A staged copy must carry every root reachability is measured over (`ZiskFv`,
`trust`, `Tests`), because `--airs-clean` redirects `survey.REPO_ROOT` and a
partial copy would make a use in an unstaged directory look like no use at all --
over-reporting unreachable mirrors. `check_mirrors.py` refuses such a copy with
exit 2 rather than reporting from it.
