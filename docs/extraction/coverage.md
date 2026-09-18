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
with the generated `trust/generated/exposure-ledger.txt`: for each extracted AIR
and constraint class it records what is exposed to the normal Lake build and to
the root-soundness import closure, which consumed generated links are tied to a
bus that `fullRv64imSoundEnsemble` does not compose, and which findings have a
source-cited residual declaration. It also reports generated links that are
currently wirable but unconsumed; those are never counted as proof exposure.

`tools/clean-components/faithfulness.py` runs `pil-extract clean-component` for
the same ten registered AIRs and compares each emitted `Row.lean` and
`Constraints.lean` with its committed `ZiskFv/AirsClean/<Air>/` counterpart.
The report preserves unsupported-emission reasons and changed-line counts.
It becomes a failing equality gate for an AIR only after that AIR is reviewed
and marked `expected = "identical"` in `trust/generated-components.toml`.
