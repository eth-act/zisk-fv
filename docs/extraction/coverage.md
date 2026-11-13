# Extraction coverage inventory

`tools/extraction-coverage/manifest.json` is the reviewed structural inventory
of the flake-pinned `build/zisk.pilout` and every file produced under
`build/extraction/`. It closes a failure mode that semantic round trips cannot
close on their own: a new AIR, constraint, lookup route, or generated output
must not disappear by shrinking the set a gate chooses to inspect.

Run the gate after `nix run .#populate`:

```bash
python3 tools/extraction-coverage/check.py --report build/extraction-coverage-report.json
python3 tools/extraction-coverage/selftest.py
```

The manifest records all 35 pilout AIR coordinates, all 4,095 constraint
indices and kinds, all `gsum_debug_data` lookup routes, every generated
`ValidatedLink`, and the closed generated-output inventory. A lookup route
retains its pilout hint index, PIOP kind and numeric type, bus-id operand,
multiplicity operand, and every named tuple slot's source operand. Operand
sources are structural identities such as witness column coordinates or an
expression-pool index. They are not hashes of expanded expressions.

Each AIR has three independent reviewed labels:

- `extraction` says whether a per-AIR constraint module is generated. The 25
  AIRs without one are recorded as `unsupported`; this cannot be mistaken for a
  theorem exclusion.
- `theorem_scope` distinguishes RV64IM core AIRs, support-only AIRs, and AIRs
  outside the RV64IM claim. These dispositions are the rows in
  `docs/extraction/air-inventory.md`; precompiles and DMA remain outside scope as
  described by `trust/defects.md`, while support-only tables are not called
  defects.
- `model_status` states whether generated constraints are consumed, merely
  generated, partially represented by support infrastructure, or have no full
  model. In particular, `MemAlignWriteByte` remains visibly
  `generated_not_consumed`; `Rom`, `RomData`, and the three table AIRs are not
  presented as fully modeled.

To refresh structural observations after an intentional pinned-input or
generator change, run:

```bash
python3 tools/extraction-coverage/check.py --update
git diff -- tools/extraction-coverage/manifest.json
```

The update preserves a classification only when the AIR's group index, AIR
index, and name all still match. New or shifted AIRs become `unclassified`, the
command exits nonzero, and a maintainer must review the source disposition
before the normal gate can pass. The manifest diff is expected review material;
the updater does not edit trust policy or theorem scope.

This inventory does not prove semantic equality. It deliberately omits
polynomial bodies, expanded lookup expressions, fixed-table values, and artifact
hashes. The pilout and mirror round trips check polynomial translation, the
kernel table equalities check live static tables, validated-link proofs check
supported lookup templates, and adversarial mutations test whether meaningful
source changes reach those layers. A green coverage inventory means every
structural item has an explicit disposition, not that every AIR is modeled or
proved.

The CI artifact includes a compact report of added, removed, and changed AIRs,
routes, links, and outputs. The full manifest remains the reviewed baseline.

`tools/mirror-roundtrip/exposure.py` complements this structural denominator
with `trust/generated/exposure-ledger.txt` (schema 2). It first runs
`lake build ZiskFv trust-gate`, then reads `trust-gate report-dependencies`:
sorted elaborated declarations with separate type/value edges, including
compiler-generated helpers and generated extraction declarations. Missing
modules, failed builds and missing root declarations fail the accounting;
there is no saved-report or source-text success fallback. The report API also
accepts an explicit imported module for deterministic compiled regression tests.
Only this report mode loads normal elaborator extensions/initializers so Meta
can resolve the imported classes and instances when reconstructing assertion
types. This is tooling runtime initialization, not a new proof assumption or
trust discharge; the other TrustGate commands retain their frozen import mode.
Import, initialization and typechecking failures are fatal, never a reason to
fall back to declaration-name matching.

The root is the **declaration** `ZiskFv.Compliance.root_soundness`, not its
module's import closure. Comments, unused imports and unconsumed aliases cannot
add reachable declarations. A consumed proof-carrying family is traversed
through its actual elaborated list/accessor and retains all its members.

The independent columns distinguish:

- `exposed-to-build`: no maintained theorem dependency or compiled component
  correspondence checks that constraint. Standalone welds still earn build
  fidelity credit even when the root never calls them.
- `exposed-to-root`: no root declaration dependency on the raw generated
  predicate, checked link, or proof-backed generated component assertion.
- `build-only-check`: a build check without a theorem-consumed tie. This can
  coexist with generated-model consumption: consuming `main` does not consume
  the separately checked manifest equality.
- `theorem-consumed-tie`: the root reaches a checked link, manifest equality,
  or an equality/iff theorem whose dependencies include the raw predicate.
- `generated-model-root`: the root reaches the generated component `main`,
  and a compiled manifest equality maps that assertion to the raw constraint.
  This does **not** mean the root consumes the equality theorem.
- `tied-not-composed`: a maintained proof reaches a generated link whose bus
  is not among the finished provider buses inventoried from
  `fullRv64imSoundEnsemble`. This is independent of local predicate/model use;
  it does not discharge provider/channel composition.

Residuals remain source-cited scope declarations. Wirable links are generated
links not reached by maintained theorem checks. Virtual byte-table exports are
reported as fidelity inputs present, never as proof that their executable
fidelity gate has run. Rebaselining these measurements is an accounting change,
not a stronger root theorem or a discharged extraction/channel obligation.
These are conservative declaration-dependency measurements, not a guarantee
that every mutation to a reached declaration is rejected. Mutation rejection
still requires its own observed proof or fidelity-gate evidence.

The #405 rebaseline, regenerated after a full build of frozen code
`6808cfcf` (base `8e25bc30`), measures the same 355 extracted constraints:

| Measurement | Textual schema 1 | Elaborated schema 2 |
|---|---:|---:|
| Exposed to build | 96 | 97 |
| Exposed to root | 313 | 347 |
| Tied, not composed | 24 | 24 |
| Declared residuals | 34 | 34 |
| Wirable links | 96 | 96 |

The new independent columns record 254 build-only checks, four theorem-consumed
ties (`Mem.29`–`Mem.32`), and four generated-model assertions
(`BinaryAdd.0`–`BinaryAdd.3`). All four BinaryAdd correspondence proofs remain
build-only even though their generated `main` is consumed. Constraints 4–8
remain unclaimed by that manifest; the separate c5 wiring check retains its
build-only credit.

The root increase withdraws 33 Main and one MemAlign import/mention credits;
the build increase withdraws the unconsumed `Arith.62` predicate alias.
Standalone welds and genuine proof-carrying families retain their checked
dependencies. These are accounting corrections, not changed proof statements,
newly discharged obligations, or root-proof improvements.

Verification of immutable code `6808cfcf` with this regenerated ledger passed:
`lake build --log-level=warning`, both trust suites, and the full unskipped
`nix --option cores 2 --option max-jobs 1 run .#test`, using
`LEAN_NUM_THREADS=2` and `CARGO_BUILD_JOBS=2`. The full gate rechecked all 14
compiled accounting regressions and the clean ledger (`97` build / `347` root /
`96` wirable). Its semantic suite checked 3,406 extraction/decode declarations'
unfiltered axiom closures against the three ordinary postulates. These
independent, potentially overlapping accounting columns must not be summed as
distinct discharged proof obligations.


`tools/clean-components/faithfulness.py` runs `pil-extract clean-component` for
the same ten registered AIRs and compares each emitted `Row.lean` and
`Constraints.lean` with its committed `ZiskFv/AirsClean/<Air>/` counterpart.
The report preserves unsupported-emission reasons and changed-line counts.
It becomes a failing equality gate for an AIR only after that AIR is reviewed.
`expected = "identical"` compares the emitted pair with its maintained source;
after model switchover, `expected = "consumed"` compares against the populated
`Extraction.Components.<Air>` pair and also requires both maintained modules to
re-export those generated declarations.

A `consumed` AIR earns per-index generated-model credit only through compiled
`constraint_N_correspondence` theorems. TrustGate reconstructs the elaborated
`Iff`: evaluation of an actual in-bounds generated `main` assertion on
`Manifest.sourceRow`, at the same source cells, offset and environment, is zero
iff the matching raw `constraint_N_every_row` holds. The whole type must match
without extra hypotheses. Merely mentioning `main`, an unrelated equality, or
the fallback value of an out-of-bounds selector cannot supply that boundary.
The kernel checks the proof, including the selected assertion; accounting also
requires its unfiltered axiom closure to stay within Lean's three ordinary
postulates. Generated-model credit verifies that `main` was declared in the
generated component module. The unchecked `assertZeroConstraints` list does
not grant credit. Importing such a theorem
only makes it a build fidelity check; root consumption of the theorem and
consumption of the generated `main` are measured separately.

`unclaimedConstraints` is the complement of the mapped indices, retaining both
ExtF-mixing and excluded cross-row constraints. The channel push is
reconstructed from a `gsum_debug_data` hint with no constraint index, so
`busPushConstraints` is empty and hints earn no manifest credit. In BinaryAdd,
only constraints 0–3 are mapped; 4–8 remain unclaimed by this manifest.
