# pil-extract — extractor notes

Maintainer notes for `tools/pil-extract/`: command contract, pilout structure
observations, and rendering limitations. This file is intentionally outside the
trust ledger; it records extractor behavior and empirical pilout facts used to
maintain generated Lean surfaces, while trust policy and axiom closure gates
live under [`../../trust/`](../../trust/README.md).

## Contract

```
pil-extract air --pilout <path> --air <needle>
                 [--output <path>] [--list]
                 [--skip-unsupported] [--only <i>[,<j>…]]

pil-extract bus-emissions --pilout <path> (--air <needle> | --airs <a,b,...>)
                 [--output <path>] [--bus-id <N>]

pil-extract lookup-wiring --pilout <path> [--output <path>]

pil-extract arith-table --rust-source <path> [--output <path>]

pil-extract clean-component --pilout <path> --air <needle>
                 [--row-output <path>] [--constraints-output <path>]
                 [--bus-id <N>] [--channel op-bus|mem-align-bus]

pil-extract mem-air-facts --pilout <path> [--air Mem]
                 [--pil-source <path>] [--output <path>]
```

- `air`: emit Lean constraint definitions for one AIR, or list AIRs.
- `bus-emissions`: emit bus-emission specs from `gsum_debug_data` hints.
- `lookup-wiring`: emit a closed typed syntax manifest for all pilout AIRs.
  A hint tuple is retained only when a generated Lean `rfl` check links it to
  a standard direct or two-hint-cluster accumulator template.
- `arith-table`: emit the extracted arithmetic lookup table from upstream
  Rust source.
- `clean-component`: emit Clean `Row.lean` / `Constraints.lean` source for
  one AIR and one supported channel shape.
- `mem-air-facts`: emit a Markdown source report for the Mem generated AIR
  facts consumed by `MemTableGeneratedAirFacts`, including the pilout source
  map for `MemTableGeneratedRawSourceSidecar`.
- `--pilout`: path to a compiled `.pilout` (protobuf, schema vendored at
  `tools/pil-extract/proto/pilout.proto`).
- `--air`: substring matched against each AIR's `name` (case-sensitive). Must
  resolve to exactly one AIR; otherwise the tool errors with the list of
  conflicting matches.
- `--output`: file to write. If omitted, the Lean source is printed on stdout.
- `--list`: dump `[group_idx][air_idx] group::name (rows, exprs, constraints)`
  for every AIR in the pilout and exit. Useful for locating needles.
- `--skip-unsupported`: emit a commented stub (`-- constraint_N skipped: …`)
  instead of aborting when a constraint uses an operand kind we don't render
  yet. Off by default — unsupported operands abort with a nonzero exit.
- `--only <i>[,<j>…]`: restrict emission to the given constraint indices.
  Constraints outside the set are omitted entirely (no stub). `--only` always
  aborts on an unsupported operand inside a selected constraint, even with
  `--skip-unsupported` set — the point of `--only` is to assert that a
  specific constraint extracts cleanly.
- `--bus-id <N>`: bus-id filter for `bus-emissions` mode and channel selection
  for `clean-component`. Defaults to `5000 = OPERATION_BUS_ID`
  (`zisk/pil/opids.pil:2`). Set to `0` in `bus-emissions` mode to emit every
  `gsum_debug_data` hint for the AIR (useful for memory-bus exploration).
- `--pil-source <path>`: optional `mem.pil` source path for
  `mem-air-facts`. Pilout symbols do not encode original `bits(N)`
  declarations, so the report attaches source lines from this file when
  supplied.

Output shape mirrors `openvm-fv/OpenvmFv/Extraction/*.lean`: one `constraint_N`
definition per pilout constraint, typed over `Circuit F ExtF C` (from
`LeanZKCircuit.OpenVM.Circuit`), with witness-column references rendered as
`Circuit.main c (id := <stage>) (column := <col_idx>) (row := row) (rotation :=
<rowOffset>)`. Debug lines from the pilout are preserved as Lean comments.

## Pilout structure observations

- The top-level `PilOut` contains `air_groups`. The current ZisK pilout has
  one group named `Zisk` with 35 AIRs.
- `BinaryAdd` lives at `airs[11]`: 198 expressions, 9 constraints.
- `air.constraints[i]` is a oneof `{firstRow, lastRow, everyRow, everyFrame}`;
  each variant carries `expression_idx` (an `Operand.Expression` wrapper around
  a `uint32`) and an optional `debug_line`.
- Expressions are a pool (`air.expressions`) indexed by the `Operand.Expression`
  references. Operands are a oneof covering constants, witness columns, fixed
  columns, challenges, public values, etc.
- **`Constant.value` bytes are big-endian, variable-length**, with leading zeros
  stripped. Example: `[0x01, 0x00, 0x00]` decodes to 65536. This is not
  documented in the `.proto` — the comment merely says "basefield element,
  variable length". Verified empirically by matching against `debugLine`
  strings in `BinaryAdd` constraints.
- Witness columns expose `(stage, col_idx, row_offset)`. The `Symbol` table
  names them — for arrays, `Symbol.id` is the base index and `Symbol.lengths`
  gives per-dimension sizes; we flatten to `name[k]` entries.

### Bus emissions (Track O POC, 2026-04-26)

Permutation- and lookup-style bus emissions (PIL2 macros `lookup_assumes`,
`lookup_proves`, `permutation_assumes`, `permutation_proves`) compile to two
artefacts in the pilout:

1. **One or more `Constraint` entries** that update a stage-2 `im_col`
   running-product accumulator. These mix witness cells with `Challenge`
   operands (the `α` / `γ` permutation challenges that compress the tuple
   into a single field element). `air` emits these in its single-field
   `Circuit F F C` specialization; they are not skip-stubbed.
2. **One `Hint` named `gsum_debug_data`**, attached to the same AIR, that
   records the tuple structurally — bus id, multiplicity expression, and
   per-slot human-readable name + Expression-index pair. The hint payload
   layout (verified empirically via `examples/probe_buses.rs`) is an outer
   `HintFieldArray` with named slots:
   * `name_piop`: string — `"Permutation"` / `"Lookup"` / `"Direct"` /
     `"Range Check"`.
   * `type_piop`: `Const` byte — `1` = proves-side, empty bytes = assumes.
   * `busid`: `Const` bytes (big-endian); `5000 = OPERATION_BUS_ID`,
     `10` = `MEMORY_BUS_ID`, etc.
   * `num_reps`: `Operand` (typically `Expression(idx)`) — multiplicity /
     gating selector.
   * `name_exprs`: `HintFieldArray` of `String` — human-readable per-slot
     names (verbatim from PIL macro call site).
   * `expressions`: `HintFieldArray` of `Operand` (typically
     `Expression(idx)`) — the rendered tuple slot values.
   * `deg_expr`, `deg_sel`: degree bookkeeping (ignored).

The hint is the structurally-clean rendering target. Operation-bus emissions
in ZisK's pilout reference only stage-1 witness cells (no challenges), so
the existing constraint renderer types them cleanly over `F`. The
`bus-emissions` mode walks these hints and produces `BusEmissionSpec`
defs.

### Lookup wiring (S3 PR 1, 2026-07)

`lookup-wiring` is intentionally separate from `bus-emissions`. The latter
targets the older `F`-valued `BusEmissionSpec` interface and still replaces a
hint operand containing `Challenge`, `AirValue`, or `AirGroupValue` with `0`.
The lookup-wiring manifest has a closed `Expr` syntax with distinct typed
constructors for witness, fixed, challenge, AIR value, AIR-group value, and
opaque operand kinds; it never uses that fallback.

The generated module reports every pilout AIR through `AirStatus`, including
whether the current Nix extraction emits its constraint file and how many
mixed constraints and gsum hints it has. PR 1 publishes links only for those
currently emitted constraint files; all other AIRs are explicit absence
reports. For an emitted AIR, an unlinked mixed constraint is retained as a
`ConstraintOnly` typed AST without any hint payload; this preserves, for
example, the global-sum constraint for later wiring extraction. An unlinked
hint contributes only to counts: its bus id, multiplicity, and tuple AST are
not published, so no caller can treat a search witness as a channel emission.

For each published `ValidatedLink`, the generator retains the raw named tuple
AST, multiplicity, PIOP side, accumulator expression, and the exact alpha and
gamma `Challenge` ASTs. It builds either the standard direct template or the
standard two-hint cluster template and emits a Lean `example := by rfl` for
the extracted constraint. The template passes through `normalise`, a narrow
syntax normalizer for only `x + 0`, `0 + x`, `x - 0`, and multiplication by
`1`. This accounts for PIL macro padding such as `AirValue(11) + 0` while the
raw tuple remains in the manifest; it is not an ExtF-erasure or an algebraic
solver. `nix/test.nix` regenerates and Lean-compiles the module, checks the
kernel examples are present, and asserts the Mem `AirValue(11)` raw padding
survives.

## Clean `Air.Flat.Component` emission (`clean-component`, C0g)

The `clean-component` subcommand emits the **Clean `Air.Flat.Component`
source shape** of an AIR — the rendering target for the Clean-integration
epic (plan decision D-EXT: `Constraints.lean` / `Row.lean` become
generated, faithful-by-construction). Module: `src/clean_component.rs`.

```
pil-extract clean-component --pilout <path> --air <needle>
                 [--row-output <path>] [--constraints-output <path>]
                 [--bus-id <N>] [--channel op-bus|mem-align-bus]
```

`--channel` selects the proves-side `push`'s Clean channel shape
(C1 staged extension, plan D-EXT):

* `op-bus` (default) — the 11-slot `OpBusChannel`
  (`ZiskFv/Channels/OperationBus.lean`), the BinaryAdd-family
  operation-bus providers. The proves-side emission is a
  logUp **`Lookup`** argument (`proves_operation`,
  `bus_id = 5000`).
* `mem-align-bus` — compatibility spelling for the 6-slot
  `MemBusChannel` (`ZiskFv/Channels/MemoryBus.lean`), the
  MemAlign-family memory-bus providers. The proves-side emission is a
  **`Permutation`** argument (`permutation_proves`,
  `bus_id = 10`); the tuple is
  `[mem_op, ptr, timestamp, width, value_0, value_1]`. The inert
  `Direct`-mode range-check emissions on the same bus
  (`multiplicity = 0`) are filtered out.

Resolution rule: among the AIR's `gsum_debug_data` hints, the
emitter keeps the single one with `type_piop = proves`, matching
`bus_id`, and `name_piop` equal to the channel's PIOP kind
(`Lookup` for `op-bus`, `Permutation` for `mem-align-bus`).

It produces two files:

- **`Row.lean`** — the AIR's *stage-1* witness columns as a
  `ProvableStruct` (`<Air>Row`), plus the `packed32` / `cPacked` reducible
  helpers. Pilout column names are sanitized to Lean field identifiers
  (`a[0]` → `a_0`). Stage-2 columns (the permutation accumulator `gsum` and
  intermediates) are **omitted** — Clean's channel-balance machinery
  subsumes them; they are listed in the generated docstring for the record.
- **`Constraints.lean`** — `main : Var <Air>Row FGL → Circuit FGL Unit`,
  a do-block of one `assertZero` per F-only pilout constraint followed by
  the operation-bus `OpBusChannel.push`; plus `<air>Elaborated :
  ElaboratedCircuit`. The permutation/lookup running-product constraints
  (the ones `--air` skip-stubs as ExtF-mixing) are **not** emitted as
  `assertZero`s — they are *represented* by the channel `push`.

The op-bus `push` tuple is reconstructed from the AIR's proves-side
`gsum_debug_data` hint (the `proves_operation(…)` PIL macro). Its 11 slots
map positionally onto `OpBusMessage`'s declared fields
(`ZiskFv/Channels/OperationBus.lean`). The renderer folds the additive /
multiplicative identities (`x + 0 → x`, `x * 1 → x`, `x * 0 → 0`) so the
PIL-macro slot padding (`cell + 0`) collapses, making the emission
slot-for-slot faithful to the hand-written `opBus_row_<Air>`
(`ZiskFv/Airs/OperationBus/OperationBus.lean`) — the faithfulness
cross-check D-EXT mandates.

C0g validated this on **BinaryAdd** (op-bus); C1 extended it for the
**memory-bus** shape and validated on **MemAlignByte**. Both AIRs'
committed `{Row,Constraints}.lean` are the generated output verbatim
(faithful-by-construction) — `lake build` is green and the opcodes'
axiom closures are unchanged. Like every other extractor shape,
`clean-component` is extended one AIR-interaction-kind at a time;
later phases add range-lookup / ROM-lookup / cross-row emission, each
validated on one AIR before reuse.

Regenerate the Clean Component source with:

```
# BinaryAdd (op-bus provider)
pil-extract clean-component --pilout build/zisk.pilout --air BinaryAdd \
    --row-output ZiskFv/AirsClean/BinaryAdd/Row.lean \
    --constraints-output ZiskFv/AirsClean/BinaryAdd/Constraints.lean

# MemAlignByte (memory-bus provider)
pil-extract clean-component --pilout build/zisk.pilout --air MemAlignByte \
    --bus-id 10 --channel mem-align-bus \
    --row-output ZiskFv/AirsClean/MemAlignByte/Row.lean \
    --constraints-output ZiskFv/AirsClean/MemAlignByte/Constraints.lean
```

Unlike the `air` / `bus-emissions` outputs (which land in the gitignored
`build/extraction/`), these are *committed* source files: the regeneration
is run deliberately when the BinaryAdd AIR changes, and the diff is the
audit surface.

## Mem AIR facts source report (`mem-air-facts`)

The `mem-air-facts` subcommand emits a Markdown audit report for the source
surface behind the Lean `MemTableGeneratedAirFacts` package. It is not a Lean
proof generator. Its purpose is to make the remaining Mem-table proof inputs
concrete: which pilout constraints supply `generated_every_row`, which hints
source range-check obligations, which witness/fixed columns are named, and
which `mem.pil` lines provide bit-width provenance that pilout does not carry.

```
pil-extract mem-air-facts --pilout build/zisk.pilout --air Mem \
    --pil-source zisk/state-machines/mem/pil/mem.pil \
    --output /tmp/mem-air-facts-report.md
```

The report maps constraints `0..=23` to
`MemTableGeneratedConstraintFacts.segmentAt` / `segment_every_row` and
constraints `24..=33` to `.permutationAt` / `permutation_every_row`. It also
emits a sidecar source map tying `MemTableGeneratedRawSourceSidecar` fields and
their `ProverData` keys to stage-2 witness columns, fixed columns, AIR_VALUE
symbols, and the `std_alpha`/`std_gamma` challenges. The report lists
`gsum_debug_data` hints whose `name_piop = "Range Check"`; those are the
extractor-facing source for `MemTableGeneratedRangeFacts` and
`MemSegmentGeneratedRangeFacts`. It also emits a Lean range-fact coverage table:
range-check hints cover `incrementChunks`, `dualStepDelta`, and
`distanceBaseChunks`. The `addrColumns`, `valueColumns`, and `stepColumns`
facts require the `mem.pil` bit-width lines supplied through `--pil-source`. The generated
artifact contract section names the remaining callback exactly: a generated
Lean module should supply `FullWitnessMemAirSourceProverDataWitnessFacts` for
the named `witness.data` sidecar keys and pass it to
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`;
`FullWitnessGeneratedTimelineEvidence` is the checked generated timeline wrapper,
while `fullWitnessMemoryTimelineEvidence_of_proverDataWitnessFacts` builds its
inner timeline evidence. Per mutable Mem table, that callback must return
`MemTableGeneratedConstraintAssertionFacts`,
`MemTableGeneratedRangeLookupFacts`, and
`MemSegmentGeneratedRangeLookupFacts`.
`fullWitnessMemAirSourceRawSidecars_of_proverDataWitnessFacts` is the sidecar
packager and the lower-level `FullWitnessMemAirSourceProverDataFacts` callback
remains available for generated modules that prove raw Mem facts directly; use
the generated wrapper's `buildRawFacts` to assemble it from raw per-table
constraint/range families, or `buildWitnessFactsFromRawParts` to feed those
families directly into the current witness-facts target. The underlying checked
adapter is `fullWitnessMemAirSourceProverDataWitnessFacts_of_rawFacts`. A
module can also build
`MemTableGeneratedRawSourceSidecar` values directly for mutable Mem tables and
expose them through `FullWitnessMemAirSourceRawSidecars`.
Lean stores that sidecar callback on `FullWitnessMemoryTimelineEvidence`;
`exists_fullWitnessMemAirSource_of_rawSidecars` selects the concrete replay
source, and `fullWitnessMemoryTimelineEvidence_of_rawSidecars` feeds the
compliance timeline boundary directly from sidecars plus the residual Sail
timeline facts. `fullWitnessMemAirSourceRawFacts_of_sidecars` and the inverse
raw-facts compatibility adapter remain available for lower-level generated
modules that still expose the raw sigma callback.
The table-level
`memTableGeneratedAirSource_of_witnessFacts` constructor remains available when
a concrete source already has explicit Clean assertion/lookup witnesses.
Because Clean component emission deliberately omits stage-2 running-product
columns and does not support previous-row witness cells, this mode records the
source surface rather than pretending those facts follow from the existing
Clean table soundness API.

The companion `mem-generated-artifact` subcommand emits a typed Lean wrapper
for the same generated-artifact boundary:

```
pil-extract mem-generated-artifact --pilout build/zisk.pilout --air Mem \
    --output /tmp/MemGeneratedArtifact.lean
```

The wrapper defines `Extraction.MemGeneratedArtifact.WitnessFacts` as the
current `FullWitnessMemAirSourceProverDataWitnessFacts witness` target,
`buildWitnessFacts` as the checked assembly point from the three per-table
callback families, `RawFacts` plus `buildRawFacts` as the checked assembly
point from raw per-table fact families, `buildWitnessFactsFromRawFacts` and
`buildWitnessFactsFromRawParts` as checked paths from raw ProverData facts into
that target, and
`buildTimelineEvidence` as the call into
`fullWitnessGeneratedTimelineEvidence_of_proverDataWitnessFacts`. It does not
prove the witness facts; it pins the generated module's public entry point to
the current generated timeline constructor.

The generated `MemGeneratedConstraintBridge.lean` companion instantiates the
extracted `Extraction.Circuit` interface with the same ProverData-backed Mem
source view and names `Extraction.Mem.constraint_0..33` as
`ExtractedConstraintFacts` for that concrete view. It also checks the
definitional adapter from those extracted predicates to the wrapper's split
`RawConstraintFacts`, maps explicit bit-width/range inequalities to raw
row/segment range facts, and exposes `ExtractedSidecarFacts` as the preferred
source-level generated target, including a direct builder for
`GeneratedTimelineEvidence`. It also checks the reverse raw-to-extracted path:
raw split constraints and raw row/segment ranges can be repackaged as
`ExtractedSidecarFacts` callbacks, so generated modules may target either raw
PIL facts or the extracted source-level fields and use checked adapters between them. This
is still a source surface, not a proof of the constraints or ranges; the
remaining generated bridge step is to produce the raw/extracted sidecar fields
for the witness.

`nix run .#populate` also materializes the same report at
`build/extraction/MemAirFacts.md`, the generated-only circuit shim at
`build/extraction/Extraction/Circuit.lean`, the Mem extracted constraints at
`build/extraction/Extraction/Mem.lean`, the wrapper at
`build/extraction/Extraction/MemGeneratedArtifact.lean`, and the ProverData
constraint bridge at
`build/extraction/Extraction/MemGeneratedConstraintBridge.lean`, produced by
the pinned `extracted-lean` derivation from `build/zisk.pilout` and upstream
`mem.pil`. Those files are reproducible generated artifacts, not Lake
dependencies; the top-level test gate compiles the checked Mem extraction
surface with `lake env lean -R build/extraction ...`.

## Limitations (deliberate; expand as phases demand)

`render_operand` renders these operand kinds: `Constant`, `WitnessCol`,
`FixedCol`, `Challenge`, `AirValue`, `AirGroupValue`, and `Expression`
(recursive). These four remain unsupported and produce a comment stub in place
of `constraint_N`: `PeriodicCol`, `ProofValue`, `PublicValue`, `CustomCol`. No
constraint in the ten extracted AIRs reaches one, so the current tree contains
zero stubs — the round-trip gate checks that, and requires any stub it does find
to correspond to a constraint the pilout shows is genuinely unrepresentable.

`AirValue` and `AirGroupValue` share the single `Extraction.Circuit.exposed`
accessor, so their index spaces overlap in the per-AIR files. See the round-trip
gate section above for the measured extent (8 of 10 AIRs, index 0, 54
constraints) and for why the `LookupWiring` rendering, which keeps the two
kinds apart, is the one the maintained links import.

Constraint kinds: `constraint_kind_suffix` encodes the pilout row domain in the
definition name (`every_row` / `first_row` / `last_row` /
`every_frame_<min>_<max>`), so `everyFrame`'s offsets reach the Lean name. All
4095 constraints in the current pilout are `everyRow`, so the other three
suffixes are unexercised, and for them the row restriction lives only in the
name — nothing downstream reads it yet.

Constraints that hit an unsupported operand are skipped with a warning on
stderr, and the extracted Lean file contains a one-line comment recording the
skip reason.

## Reproducibility check

Reproducibility is now anchored by **`flake.lock`** at the repo root.
Every transitive build input — the sail compiler, the sail-riscv
source, the ZisK source, pil2-compiler, pil2-proofman, the nixpkgs
revision — is content-addressed by narHash. Changing any input edits
the lock file, which becomes the audit surface for build-input
changes.

The flake derivations (`sail-lean-tree`, `zisk-pilout`,
`extracted-lean`) are deterministic functions of the lock. Their
outputs reproduce bit-identically across machines. The historical
per-AIR `*.hand.lean` oracles and the explicit `pil-extract --list`
fingerprint pin (formerly in `docker/versions.txt`, removed when the
docker pipeline was retired) are subsumed by Nix's content-addressed
build graph.

If the fingerprint diverges, investigate before "fixing" it. Genuine causes:
(a) extractor output changed (flags, new operand kinds, different
parenthesization) — update the pin and note the change here;
(b) extractor regressed — fix the extractor, not the pin;
(c) the upstream `.pil` source changed — rebuild the pilout from the
new source and re-pin.

## Round-trip gate (`tools/pilout-roundtrip`, eth-act/zisk-fv#303)

Reproducibility says the extractor's output is a deterministic function of the
lock. It says nothing about whether that output is a faithful translation. The
round-trip gate is what checks the translation: for every polynomial identity in
`build/zisk.pilout` it decides, in the pilout's own algebra, that the emitted
Lean is the same polynomial. It reads the pilout with its own hand-rolled
protobuf decoder (not `prost`) and the Lean with its own parser (never the
extractor's code), so a distortion on one side cannot cancel one on the other.
Python 3 stdlib only, ~1.5 s, no Lean build needed.

Both renderings the extractor produces are decided:

- `Extraction/<AIR>.lean`'s `constraint_<i>_<suffix>`, over the four
  `Extraction.Circuit` accessors — 355 constraints across the ten AIRs
  `nix/extracted-lean.nix` extracts;
- `Extraction/LookupWiring.lean`'s `constraint_<Air>_<i>` and
  `constraintOnly_<Air>_<i>`, over the `Expr` inductive — the 203 of those that
  reach a challenge, AIR value or AIR-group value, which is also the set the
  maintained `ZiskFv/AirsClean/*` links import. Which constraints must be there
  is computed from the pilout, so a missing rendering is a detected drop.

The second rendering matters for fidelity, not just for coverage.
`Extraction.Circuit` has one `exposed` accessor for both `AirValue` and
`AirGroupValue`, so the per-AIR files identify two distinct pilout values
wherever an index is used by both kinds (8 of the 10 AIRs, index 0, 54
constraints — e.g. `BinaryAdd.padding_size` and `Zisk.gsum_result` are both
`exposed (index := 0)` in `BinaryAdd.lean`). `Expr` keeps them apart, and every
affected constraint is in the second rendering, so the distinction is checked
even though the per-AIR file cannot express it. Worth closing in the emitter:
those files are quantified over a class of circuits the pilout does not describe.

Also checked, because each was an assumption before: the emitted witness-column
name header against a reconstruction from `PilOut.symbols` alone (299 columns,
exact); `Operand.Constant.value`'s byte order against the constraints' own
`debugLine` literals (345 discriminating constants, 73 corroborate big-endian,
0 corroborate little-endian); and the binder list against the two exact
spellings `render_constraint` writes, which pins `row : ℕ` — the precondition for
the saturating-subtraction argument in the next section — and pins the
`ExtF := F` collapse to the constraints whose operands actually need it.

The scope is declared in `check.py` and cross-checked against
`nix/extracted-lean.nix` and `LookupWiring.lean`'s `airStatus_<Air>` manifest,
in both directions. It is deliberately not discovered from the extraction
directory: an AIR whose constraints all became `--skip-unsupported` stubs has no
`def` left, so a discovered scope would drop it silently and keep reporting a
perfect ratio.

Wiring: the tail of `nix run .#populate` (so drift fails where it is produced)
and step 3/10 of `nix run .#test` (`check.py` plus the mutation selftest). Not in
`trust/scripts/check-all.sh`, whose CI job has no `build/` at all. Exit 1 is a
mismatch or an uncovered constraint, exit 2 is a missing artifact; neither is a
pass.

`tools/pilout-roundtrip/README.md` carries the full argument, the two atom
vocabularies, and the measured residual blind spots.

## Mirror gate (`tools/mirror-roundtrip`, eth-act/zisk-fv#304)

The round-trip gate above ends at `build/extraction/`. Nothing in its argument
touches `ZiskFv/`, and no Lean under `ZiskFv/` imports a per-AIR
`Extraction.<AIR>` module at all, so a constraint can round-trip perfectly and
still be restated wrongly, partially, or not at all in the handwritten Lean the
proof actually consumes. This gate closes that second direction for the
polynomial content.

How the two differ:

| | round-trip gate (#303) | mirror gate (#304) |
| - | - | - |
| decides | `pilout` vs `build/extraction/` | `build/extraction/` vs `ZiskFv/AirsClean/**` |
| both sides are | generated | one generated, one handwritten |
| a failure means | the extractor dropped or distorted a constraint | a constraint has no mirror, or a mirror has no constraint |
| its verdict is | `OK` at HEAD | `FAILED` at HEAD, and the failures are the finding |
| the fix is | change the generator and rerun | proof work on a protected interface |

It reuses `poly.py`, `check.to_poly`, `lean_parse.py`, `pilout_wire.py` and
`pilout_atoms.py` from `tools/pilout-roundtrip` rather than forking them, so the
two tools cannot disagree about what a column, an atom or a canonical form is.
Per AIR it canonicalises the *comparable* generated constraints — the issue's
rule: all of them minus every constraint reaching `Extraction.Circuit.challenge`
or a stage-2 lane, 176 of the 355 — and the clauses of every inventoried mirror
predicate, and pairs the two sets by canonical form rather than by index. The
comparable rule is implemented twice, off the emitted Lean and off the pilout
operands, and the two index sets must agree on every run.

Five finding classes: `MATCHED`; `GAP`, a comparable constraint no mirror clause
has the canonical form of; `STRENGTHENING`, a mirror clause no constraint has the
form of — a *syntactic* class, so the report also runs a cofactor search and says
when the clause is in fact implied by a constraint and therefore weaker rather
than stronger; `RECLASSIFICATION`, a pairing that turns on a lane's kind;
`UNBACKED`, an equation over a row field this AIR has no lane for, which has no
canonical form to pair with and so is reported rather than compared.

Besides the pairing, the run holds its own scope: `survey.CLASSIFICATION` against
the declarations actually under the mirror root, every `NEAR_*`-classified
declaration re-parsed and required to carry no comparable equation,
`DECLARED_AIRS` through #303's own `_check_scope`, `lanes.gate_lane_map`, every
resolved projection against the row record it claims to project, and a non-empty
floor on both denominators. A scope that shrinks is the failure mode a
declared-list scope has, and each of those is what makes one loud.

Wiring: step 4/10 of `nix run .#test` (`check_mirrors.py` plus `acceptance.py`,
the mutation suite that is the evidence the gate can fail and classify). Exit 1
is a finding, exit 2 a missing artifact; neither is a pass. Deliberately NOT in
`nix run .#populate`: populate materialises generated inputs, and this gate's
failing side is handwritten source that populate neither writes nor reads, so a
gap here is not extraction drift and re-running populate cannot change it.
Deliberately not in `trust/scripts/check-all.sh` either, for #303's reason — that
CI job has no `build/`.

**This step fails at HEAD**, and that is the deliverable rather than a wiring
bug: 35 comparable generated constraints have no mirror clause of their AIR.
Those are findings for the owner. Mirrors and `Valid_<AIR>` validators are
protected proof interfaces, so closing one is proof work — not something the tool
may do, and not something to silence with a baseline here.

`tools/mirror-roundtrip/README.md` carries the full argument, the declared
exclusions with their citations, and the measured blind spots.

## Negative row rotations (Phase 2.5 D2)

PIL2 uses a postfix `'` to denote "previous-row" cells (row rotation `-1`),
as in `'set_pc` and `'c[0]` inside the PC-handshake constraint
(`main.pil:409-410`). `Circuit.main` / `Circuit.preprocessed` from
`LeanZKCircuit.OpenVM.Circuit` both type rotation as `ℕ`, so a negative
rotation can't live in the rotation field. The extractor rewrites
`row_offset = -k` (k > 0) to `(row := row - k) (rotation := 0)` — evaluated
cells are definitionally identical, so this is sound wherever `row ≥ k`.

**Soundness at row 0**: Lean's `ℕ` subtraction saturates at 0, so `row - 1`
evaluates to `0` when `row = 0`. That misaligns the decoded cell relative to
PIL's semantics. Every constraint in ZisK's pilout that uses a negative
rotation gates itself with `(1 - SEGMENT_L1)`, where `SEGMENT_L1` is a
fixed column equal to `1` on the first row of each segment and `0`
elsewhere. At row 0, the gate factor is `0`, so the misaligned subterm is
multiplied out and the constraint is vacuously true. Callers of the named-
constraint layer (e.g. `Airs/Main.lean::pc_handshake_to_next_pc`) must
provide a `segment_l1 (row + 1) = 0` witness to derive the useful
specialization.

Positive row rotations are still rejected loudly — ZisK's pilout doesn't
use them and supporting them would require auditing every AIR for
`row + k` semantics.

## Extending

Adding a new operand kind is a match arm in `render_operand` (`src/main.rs`).
Keep the "fail loudly on unhandled cases" stance: raise an `anyhow!` so the
skip path in `render_air` emits a clearly labeled stub. Do not silently emit
`sorry` — the goal is visibility, not typecheck happiness.
