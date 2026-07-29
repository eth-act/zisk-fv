# pilout-roundtrip

A checker that decides, for every polynomial-identity constraint in
`build/zisk.pilout`, whether the constraint the extractor emitted into
`build/extraction/Extraction/` is the same polynomial.

Issue: eth-act/zisk-fv#303. Python 3 standard library only -- no protobuf
library, no numpy, no third-party package of any kind. It runs on a bare
`python3` with nothing installed, and it does not need a Lean build.

## Why

`tools/pil-extract` is trusted end to end. Nothing checked that every pilout
constraint reached Lean, or that it arrived unaltered. Counting emitted
constraints, or diffing the `-- <air>.pil:NNN` provenance comments, checks only
accounting: both pass while a constraint is silently mistranslated -- right
count, right cited line, wrong polynomial. That is a defect class no amount of
downstream Lean proving can catch, because the Lean proof is about the emitted
constraint, not about the one in the pilout.

## The round-trip argument

Write `f` for the extractor, `pilout -> Lean`. Build an independent `g`,
`Lean -> expression AST`, and decide `g(f(t)) == t` for every constraint `t`,
in the pilout's own algebra.

* A dropped constraint shows up as a `t` that `g(f(-))` does not cover.
* A distorted one shows up as a non-equivalence.

`==` is polynomial normal form, not a list of allowed rewrites. Both sides are
polynomial expressions over column atoms, so each is expanded into a sorted
monomial map with Goldilocks coefficients and the maps are compared exactly.
That is total and it decides the question. An enumerated rewrite set
(associativity, commutativity, `a - b` versus `a + (-1)*b`, constant folding)
would be strictly weaker and would need maintaining.

Random evaluation is also computed, per constraint, and the two verdicts are
cross-checked, because `random_screen` returning `False` is documented
conclusive -- a screen that says "differ" against a decider that says "equal" is
a contradiction inside `poly.py`, and the run fails rather than picking a side.
It is a second reading of the same term map, not corroboration of the fold that
built it; both are always computed, so it is not a pre-filter either.

### `f` emits two Lean renderings, and both are decided

For a constraint whose expression tree reaches a challenge, an air value or an
air group value, the extractor emits *two* Lean terms:

| rendering | vocabulary | who imports it |
| --------- | ---------- | -------------- |
| `Extraction/<AIR>.lean`, `constraint_<i>_<suffix>` | the four `Extraction.Circuit` accessors | nothing under `ZiskFv/` |
| `Extraction/LookupWiring.lean`, `constraint_<Air>_<i>` / `constraintOnly_<Air>_<i>` | the `Expr` inductive | `ZiskFv/AirsClean/*` (`link_*`, `template_*`, `ValidatedLink.constraint`) |

The second is strictly richer: `Expr` keeps `airValue` and `airGroupValue`
apart, keeps `challenge`'s stage, keeps `rowOffset` signed, and carries the
constant as a decimal string. So both are checked, in two vocabularies:

* the **accessor vocabulary**, which is what `Extraction.Circuit` can express:
  `main`, `preprocessed`, one flattened `challenge` index, one `exposed` index
  for both kinds of exposed value;
* the **operand vocabulary**, one atom per `pilout.proto` operand message, with
  nothing merged.

At HEAD that is 355 constraints in the first and 203 of them also in the second.
The 203 are exactly the constraints the accessor vocabulary cannot render
faithfully; on the other 152 the accessor mapping is injective, because
`WitnessCol` and `FixedCol` map bijectively onto `main` and `preprocessed`. So
no constraint is decided only in a vocabulary that loses information -- which is
what the earlier version of this document got wrong when it called the
`AirValue`/`AirGroupValue` collapse unclosable.

## The two conditions from the issue

**1. `g` must not reuse `f`'s code.** A `g` derived from `f` lets compensating
errors round-trip clean.

`g` is `lean_parse.py` (a tokeniser and recursive-descent parser for the
emitted per-AIR Lean) and `lean_wiring.py` (the same for `LookupWiring.lean`'s
`Expr` terms). Both are derived only from the emitted artifacts and the
generated `Extraction.Circuit` shim, never from the Rust extractor. They are
deliberately dumb structural readers -- every token, accessor, argument name,
binder list and syntactic shape is recognised explicitly, and anything else
raises rather than being skipped, because a silently dropped construct would
turn an extraction defect into a passing gate.

The pilout side is equally independent: `pilout_wire.py` is a hand-rolled
protobuf wire-format decoder (the extractor uses Rust `prost`, so a decode-side
distortion cannot cancel against an extraction-side one), and `pilout_atoms.py`
re-derives the operand-to-atom correspondence from `pilout.proto` and the pilout
symbol table.

Two of those derivations are *checked*, not argued:

* `main c (id := s) (column := k)` has `s` the stage and `k` the stage-relative
  column. `witness_column_names` reconstructs the emitted
  `-- stage S col C: name` header from `PilOut.symbols` alone -- stage, starting
  `id`, and `lengths` for arrays -- and it must reproduce it exactly. At HEAD
  that is 299 columns across the ten AIRs, all matching.
* `Operand.Constant.value`'s byte order. `pilout.proto` declares it as bare
  `bytes`; `pilout_wire` calibrates an order from `PilOut.baseField`, a different
  field that need not share the convention. `constant_byte_order_evidence` tests
  it against the constraints' own `debugLine` strings, which are PIL-compiler
  output quoting their literals in decimal. At HEAD: 345 constants read
  differently under the two orders, 73 corroborate big-endian, **0** corroborate
  little-endian. A corroboration under the reversed order, or none under the
  calibrated one, fails the run.

`to_poly` in `check.py` is used on every side. That does not weaken the
condition: it constrains the *readers*, which share no code. The canonicaliser
must be one function everywhere or it is not deciding a single equality.

**2. `f` must be injective on the constraint set**, or coverage has to be
counted on the image. Two pilout constraints collapsing into one Lean definition
would hide a drop.

`f` keys each emitted definition by the pilout constraint index
(`constraint_<i>_<suffix>`, `constraint_<Air>_<i>`). The checker verifies, per
AIR, that the Lean indices are exactly `0..n-1` with no gap and no duplicate,
and that `n` equals the pilout constraint count. Two pilout constraints landing
in one definition would leave an index unclaimed, which is reported as
`PILOUT_ONLY` and fails the run. The report prints this as an explicit
`condition 2` line rather than leaving it implicit. A repeated index is reported
as an accounting failure in its own right.

Injectivity on *operands* is a separate question, and it is where `f` genuinely
fails -- see the fidelity-loss section below.

## Scope is declared, not discovered

`DECLARED_AIRS` in `check.py` lists the ten AIRs the gate covers. This is
deliberate and it replaces an earlier design that discovered the scope from the
extraction directory. Discovery made `f` the author of its own audit: an AIR
that stopped arriving -- deleted, or reduced entirely to `--skip-unsupported`
stubs by one new `bail!` in `render_operand` -- simply left the discovered scope,
taking its constraints out of both the numerator and the denominator, and the
run stayed green with a smaller, still-perfect-looking ratio.

A list has the opposite failure mode: it goes stale. So it is cross-checked
against two independent declarations of the same intent, and any disagreement in
either direction is a global failure:

| source | what it declares |
| ------ | ---------------- |
| `nix/extracted-lean.nix` | the `--air` invocations the build actually runs |
| `LookupWiring.lean`'s `airStatus_<Air>.emittedConstraintFile` | the extractor's own list, from a fixed constant in `lookup_wiring.rs` rather than from whether rendering succeeded |

A Lean file carrying constraint definitions for an AIR `DECLARED_AIRS` does not
list is also a failure: the declaration is stale and that AIR is checked by
nothing.

## Running it

```
python3 tools/pilout-roundtrip/check.py
```

Defaults are `build/zisk.pilout` and `build/extraction/Extraction`, resolved
relative to the repository root, so it works from any directory. Full run over
the ten declared AIRs takes about 1.5 s.

```
python3 tools/pilout-roundtrip/check.py [--pilout PATH] [--extraction DIR]
                                        [--air NAME]... [--json PATH]
                                        [--quiet] [--verbose]
```

* `--air NAME` restricts the run, repeatable. A filtered run does not cover the
  declared scope, so its summary line says `PARTIAL`, never `OK`.
* `--json PATH` writes the full structured result, including the raw atom
  tuples of every differing monomial. `"ok"` there is the same value the summary
  line prints and is false whenever the exit code is non-zero.
* `--quiet` prints only failures and the summary line. `--verbose` adds every
  matched constraint and stops truncating difference witnesses.

Exit codes:

| code | meaning |
| ---- | ------- |
| 0 | every declared AIR present and fully accounted for, every constraint matched in both renderings |
| 1 | mismatch, drop, invention, accounting failure, parse error, scope violation, or a run that checked nothing |
| 2 | usage or IO error: no pilout, no extraction directory, an unknown `--air`, an unwritable `--json` path |

Exit 2 exists so that "the artifacts are not there" is distinguishable from
"the check failed". **Neither is success.** Gate wiring must not treat a missing
artifact as a pass; the tool prints `ARTIFACTS ABSENT -- this is not a pass` on
stderr to make that hard to get wrong. A failing check outranks an unwritable
`--json`, so exit 1 wins when both happen.

The sibling modules each run standalone and print a report of their own layer,
which is the fastest way to inspect one part in isolation:

```
python3 tools/pilout-roundtrip/pilout_wire.py    # decoded pilout structure
python3 tools/pilout-roundtrip/lean_parse.py     # parsed per-AIR Lean
python3 tools/pilout-roundtrip/lean_wiring.py    # parsed LookupWiring renderings
python3 tools/pilout-roundtrip/pilout_atoms.py   # atom mapping and its evidence
python3 tools/pilout-roundtrip/poly.py           # canonicaliser self-test
python3 tools/pilout-roundtrip/selftest.py       # mutation test: the gate can fail
```

## What it reports

A per-AIR table (pilout constraints, Lean definitions, skip stubs, matched,
mismatched, pilout-only, lean-only) with a TOTAL row; then the P3
second-rendering result, the condition-2 line, the screen-versus-decider counts,
the byte-order evidence, the fidelity-loss table, and the full denominator:
every polynomial identity the pilout carries, split into in-scope, in an
unextracted AIR, and global.

Then a detail section for every non-matched constraint giving the AIR, the
index, the provenance comment, and a minimal difference witness: the symmetric
difference of the two canonical monomial maps, truncated to the first ten terms,
with the number of differing terms. Coefficients are printed as signed
representatives mod p, so `p-1` reads `-1`.

The witness is the point. A checker that says "mismatch" without showing what
differs is not useful to whoever has to fix it. For a single wrong column
index, for example, it reads:

```
  MISMATCHED  Arith #4
    provenance   arith/pil/arith.pil:54 div_by_zero*(1-div_by_zero)
    suffix       pilout 'every_row' / lean 'every_row'
    reason       canonical forms differ in 4 monomial(s) (pilout 2 terms deg 2, lean 2 terms deg 2)
    canonical symmetric difference: 4 differing monomial(s), showing 4
      main(1,36)             pilout  1  lean  0
      main(1,36)*main(1,37)  pilout  0  lean -1
      main(1,36)^2           pilout -1  lean  0
      main(1,37)             pilout  0  lean  1
```

Per-constraint outcomes:

| outcome | meaning |
| ------- | ------- |
| `MATCHED` | both sides present and canonically equal |
| `MISMATCHED` | both present and they disagree (polynomial, suffix and/or binder form) |
| `PILOUT_ONLY` | a pilout constraint that did not reach Lean -- a drop |
| `LEAN_ONLY` | a Lean definition with no pilout constraint -- an invention |
| `SKIPPED` | a pilout constraint with no Lean-representable operand, correctly paired with a Lean skip stub |

`SKIPPED` is the extractor's declared non-coverage (`--skip-unsupported`). It
is not a translation defect, so it does not fail the run, but it is not a check
either: it is printed in the detail section and named in the summary line, and
the summary's `matched/total` ratio drops below 1, so it cannot pass silently.
A skip stub over a *representable* constraint is a different thing entirely --
a silent drop -- and is reported as `PILOUT_ONLY`, which does fail. There are
zero of either at the current HEAD. If this ever becomes non-zero, decide
deliberately whether declared non-coverage should be a hard gate failure; the
policy lives in `FAILING_OUTCOMES` in `check.py`.

### What else is checked per constraint

* the `constraint_<i>_<suffix>` suffix against the pilout constraint kind;
* the binder list, against a table of the two exact spellings the emitter
  writes. This is not decoration. It carries the type of `row` -- `ℕ`, which is
  what the extractor's own saturating-subtraction argument for negative row
  offsets rests on -- and whether the definition is quantified over a general
  `Extraction.Circuit F ExtF C` or over the `ExtF := F` collapse. Which one is
  correct is decided by the operands: at HEAD the 203 collapsed definitions are
  exactly the 203 constraints reaching an extension-field operand. Using the
  collapse where it is not needed quantifies over strictly fewer circuits than
  the pilout constraint does, and the polynomial comparison cannot see it;
* the provenance comment, as a warning only -- a comment is not a constraint,
  but a constraint whose cited PIL line moved may have been re-keyed.

## Fidelity loss in the per-AIR Lean files

`Extraction.Circuit` declares one `exposed` accessor, and the extractor sends
both `Operand.AirValue {idx}` and `Operand.AirGroupValue {idx}` to it. Any
instance of the class therefore supplies one function for both, so the emitted
file identifies two different pilout values. This is not hypothetical: in
`BinaryAdd.lean`, `exposed (index := 0)` is `BinaryAdd.padding_size` in
`constraint_7_every_row` and `Zisk.gsum_result` in `constraint_8_every_row`.
Measured at HEAD: 8 of the 10 AIRs have index 0 used by both kinds, and 54
constraints reference an operand at such an index.

The gate reports this, counted per AIR, as a fidelity loss rather than as a
comparison failure, because it is a property of that artifact and not a
disagreement between the pilout and the Lean *in the vocabulary that artifact
can express*. What closes it is the second rendering: a constraint touching
either kind necessarily reaches an extension-field operand, so all 54 are in
P3's expected set, and P3 decides them against `Expr.airValue` and
`Expr.airGroupValue`, which are distinct constructors. The information is
preserved in the extraction as a whole and the gate checks that it is.

It remains worth fixing in the extractor: the per-AIR files are the artifact a
future proof would import if it wanted the row-local constraints, and as emitted
they are quantified over a class of circuits the pilout does not describe.

## Scope, and what a green run does not assert

Polynomial identities only. Out of scope, because they are separate proto
messages and separate work:

* lookups and permutations as *channel* facts (`PilOut.hints`); the constraint
  terms `LookupWiring.lean` publishes for them are checked, their hint payloads
  and the balance argument are not;
* fixed column *values* -- the checker relates `FixedCol` operands to
  `Extraction.Circuit.preprocessed` by index, and says nothing about the column
  contents, which this pilout does not store anyway;
* public inputs and public tables;
* the global constraint and the global expression pool. The pilout carries
  4095 AIR constraints plus 1 `GlobalConstraint` (`std_sum.pil:745`, the
  top-level `Zisk.gsum_result` identity); nothing in `tools/pil-extract`
  renders it, so it reaches no Lean at all. The report prints it in the
  denominator rather than leaving it out of the accounting;
* the 3740 constraints in the 25 pilout AIRs nothing extracts. The report names
  them and their counts.

Much of Main sits outside the F-only slice that the maintained Lean actually
consumes; the round trip checks that all 144 of its constraints arrived intact,
not that all 144 are used.

It does not reduce trust in PIL itself, or in PIL matching the Rust prover. It
closes the extractor step, for the polynomial content: pilout in, Lean out, same
polynomial.

## Known residual blind spots

These are places where a real defect could exist and this gate would still be
green. Each is measured, not assumed; `selftest.py` carries the ones that can be
expressed as a mutation, as controls that must stay green.

**`row - k` is a symbolic offset here, not Lean's ℕ subtraction.** The
extractor rewrites `rowOffset = -k` to `(row := row - k)`, and over `ℕ` that
saturates: at `row = 0` the emitted term reads row 0 instead of row `-k`. The
extractor's soundness argument is that every such constraint carries a
`(1 - SEGMENT_L1)` factor that vanishes there (see
`docs/extraction/extractor-notes.md`). This gate does not check that argument.
Its atoms carry the offset symbolically -- `('main', s, c, -1)` is a free
variable, not `Nat.sub row 1` -- so both sides agree on the offset and the
question of what the Lean term *means* at `row = 0` is outside the algebra being
decided. 52 emitted sites use a negative offset and 27 a positive one. What the
gate does now enforce is the precondition: `row : ℕ` in the binder list, exactly,
so the emitted Lean cannot quietly move to `ℤ` and take the argument with it.
Symmetrically, PIL's row domain is cyclic mod N and `row + k` over `ℕ` is not;
the gate is silent on that too.

**Literals are compared modulo p.** Both sides fold constants into GF(p), so an
emitted literal differing from the pilout's by a multiple of `p` round-trips as
equal: `4294967296` and `4294967296 + p` are one field element and the gate
cannot separate them. That is the right verdict for the algebra the gate
decides in, and the extraction targets Goldilocks, but the emitted Lean is
generic over `[Field F]`, so at another characteristic those two spellings are
different constraints. `selftest.py` carries it as a neutral control
(`NOOP_LITERAL_MOD_P`), so the behaviour is measured rather than assumed. Every
other mutation of a literal, small or large, is caught.

**Challenge flattening is corroborated but not discriminated, in the accessor
rendering.** `Operand.Challenge {stage, idx}` is flattened to a single Lean
index as `sum(numChallenges[:stage-1]) + idx`. On this pilout the prefix sum is
zero, because the only populated challenge stage is the last one, so the
degenerate rule `flat = idx` would match equally well. The derived rule is what
is implemented. This is confined to the accessor rendering: every constraint
carrying a challenge is also decided in the operand vocabulary, where the stage
survives unflattened and is compared directly against the pilout's.

**`AirGroupValue.idx` is witnessed at index 0 only**, because the file declares
exactly one air group value, so a mapping rule agreeing at 0 and diverging later
would not be caught.

**Three of the four constraint kinds are unexercised.** All 4095 pilout
constraints are `EveryRow` and all 355 emitted definitions use the `every_row`
suffix, positionally aligned, so that row is pinned by data. The expected
suffixes for `FirstRow`, `LastRow` and `EveryFrame` are inferred from the
message names and have no occurrence to confirm them -- and for those kinds the
row restriction lives only in the suffix, since nothing in a definition's body
encodes it. `pilout_atoms.suffix_is_pinned` reports which is which and the
checker emits a warning if an unpinned kind is ever used.

**The `neg` arm is unexercised.** `Expression.Neg` occurs 41 times in the
pilout, entirely in `ArithEq` and `ArithEq384`, neither of which is extracted.
Every reader implements it per the shared spec; none confirms another on it.

**`rotation` has no pilout counterpart.** The Lean accessors carry a
`rotation` argument that `pilout.proto` has no field for. Every emitted
occurrence is `rotation := 0` and `lean_parse` rejects any other value, so the
round trip can confirm it is always the identity and nothing more. It is a
Lean-side degree of freedom outside the gate.

**Nothing binds the pilout's vintage to the extraction's.** The emitted Lean
carries no digest of the pilout it came from, so the two paths are related only
by content. That covers most of the risk -- a changed constraint against a stale
extraction is a mismatch, a removed or added *declared* AIR is a scope failure --
but a regenerated pilout that grows an AIR nobody declared, against an
extraction from the previous pilout, is silent, because that AIR is genuinely
out of scope either way. Closing it properly needs the extractor to stamp a
pilout digest into its output, which is outside this tool.

**Two Arith constraints share a canonical form.** `Arith` #29 and #30 are
`div_overflow*div_by_zero` and `div_by_zero*div_overflow`, one polynomial. A
body swap between them is undecidable here and also harmless; their provenance
comments differ, and that comparison is a warning. No constraint in the checked
set canonicalises to zero.

**The wire decoder can diverge from `prost` rather than share a bug with it.**
`read_varint` does not truncate to a field's declared width, so a `uint32`
written as a wider varint would read differently than `prost` would. Neither
occurs in this file, and the bounds checks in `operand_atom` would reject the
result rather than pass it, but "shares no code" is an argument about shared
bugs, not divergent ones. The repeated-occurrence case is now refused outright
rather than resolved differently from proto3's merge rule.

**Nothing here checks that the pilout is what PIL meant, or that the Lean
constraint is *used*.** A constraint can round-trip perfectly and still be
dead: whether `ZiskFv/` consumes it is a different question, tracked
separately. The per-AIR files, in particular, are imported by nothing under
`ZiskFv/` today.

## The gate can fail: `selftest.py`

`check.py` reporting 355/355 is worth nothing until we know which extraction
defects it would have caught, so `selftest.py` establishes that empirically: it
copies the emitted Lean into a temporary directory, applies exactly one mutation
to the copy, runs `check.py` against the real pilout and the mutated copy, and
requires both the expected exit code and the expected *failure class* -- because
"it failed" and "it failed for the right reason" are different claims. The real
`build/` tree is digested before and after to prove it was never written.

At HEAD: 33 cases, 28 defect classes caught and correctly classified, 5 neutral
controls green, about 10 s. The classes include a whole AIR deleted, a whole AIR
reduced to skip stubs, an undeclared AIR file appearing, `noncomputable def`,
`row : ℤ`, an extra binder, the wrong binder form, a rotated witness-name
header, a constraint missing from the `LookupWiring` rendering, a wrong column
inside it, `airGroupValue 0` rendered as `airValue 0`, a manifest flip, and the
per-constraint algebra mutations (sign, column, stage, row offset, literal,
dropped factor, swapped bodies, duplicated or renumbered indices).

An uncaught mutation is a residual blind spot: it gets reported as one and
documented in the section above. Its expectation does not get relaxed and the
case does not get deleted.

## Layout

| file | role |
| ---- | ---- |
| `pilout_wire.py` | zero-dependency protobuf decoder for `zisk.pilout` |
| `pilout_atoms.py` | pilout operands and the expression pool to the shared AST, in either vocabulary; the atom mapping and its evidence |
| `lean_parse.py` | `g`: emitted per-AIR Lean to the shared AST |
| `lean_wiring.py` | `g2`: `LookupWiring.lean`'s `Expr` terms and `airStatus` manifest to the shared AST |
| `poly.py` | exact multivariate polynomials over GF(p); `canonical()` is the decider |
| `check.py` | driver and gate entry point: scope, accounting, both round trips, reporting |
| `selftest.py` | mutation test: one defect per case, each required to be caught |

The shared expression AST, identical on every side:

```
('add', e1, e2) | ('sub', e1, e2) | ('mul', e1, e2) | ('neg', e)
('const', n)                      n a non-negative Python int
('atom', a)                       a one of, in the ACCESSOR vocabulary
    ('main', stage, column, delta)   delta a SIGNED row offset
    ('pre', column, delta)           delta a SIGNED row offset
    ('chal', index)
    ('exposed', index)
                                  or, in the OPERAND vocabulary
    ('witness_col', stage, column, delta)
    ('fixed_col', column, delta)
    ('challenge', stage, index)
    ('air_value', index)
    ('air_group_value', index)
```

## Where it is wired

| place | what runs |
| ----- | --------- |
| `nix/populate.nix`, at the tail | `check.py --quiet`, so extraction drift fails at the moment the artifacts are produced |
| `nix/test.nix`, step 3/9 | `check.py --quiet` and `selftest.py` |
| `.github/workflows/proofs.yml` | both of the above, via `nix run .#populate` and `nix run .#test` |

It is deliberately **not** in `trust/scripts/check-all.sh`. That gate runs in CI
on a bare checkout with no `build/` directory, so the check would find no
artifacts there and exit 2 on every run; wiring it into a job that cannot see
its inputs is worse than not wiring it at all.

The exit code is the whole contract, and the one rule that matters is that
exit 2 must not be swallowed: an absent `build/` is not a passing round trip.
