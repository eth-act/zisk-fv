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

pil-extract arith-table --rust-source <path> [--output <path>]

pil-extract clean-component --pilout <path> --air <needle>
                 [--row-output <path>] [--constraints-output <path>]
                 [--bus-id <N>] [--channel op-bus|mem-align-bus]

pil-extract mem-air-facts --pilout <path> [--air Mem]
                 [--pil-source <path>] [--output <path>]
```

- `air`: emit Lean constraint definitions for one AIR, or list AIRs.
- `bus-emissions`: emit bus-emission specs from `gsum_debug_data` hints.
- `arith-table`: emit the extracted arithmetic lookup table from upstream
  Rust source.
- `clean-component`: emit Clean `Row.lean` / `Constraints.lean` source for
  one AIR and one supported channel shape.
- `mem-air-facts`: emit a Markdown source report for the Mem generated AIR
  facts consumed by `MemTableGeneratedAirFacts`.
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

- The top-level `PilOut` contains `air_groups`. ZisK's pilout has one group
  named `Zisk` with 22 AIRs (`Main`, `Rom`, ..., `BinaryAdd`, ...).
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
   into a single field element) and are the constraints the existing
   extractor skip-stubs as `mixes F (witness cells) with ExtF`.
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
lists `gsum_debug_data` hints whose `name_piop = "Range Check"`; those are the
extractor-facing source for `MemTableGeneratedRangeFacts` and
`MemSegmentGeneratedRangeFacts`. The report also emits a Lean range-fact
coverage table: range-check hints cover `incrementChunks`, `dualStepDelta`, and
`distanceBaseChunks`, while `addrColumns` and `stepColumns` require the
`mem.pil` bit-width lines supplied through `--pil-source`. A generated Lean
module should call `memTableGeneratedAirSource_of_witnessFacts` after supplying
Clean assertion witnesses for the split generated constraints and lookup
witnesses for the explicit range-check facts; the lower-level
`memTableGeneratedAirSource_of_constraintFacts` remains available when a module
proves the raw generated constraints and range propositions directly. Because
Clean component emission deliberately omits stage-2 running-product columns and
does not support previous-row witness cells, this mode records the source
surface rather than pretending those facts follow from the existing Clean table
soundness API.

## Limitations (deliberate; expand as phases demand)

The extractor renders these operand kinds: `Constant`, `WitnessCol`,
`Expression` (recursive). All others are unsupported and produce a comment
stub in place of `constraint_N`:

- `FixedCol` — needed for the row-indicator / final-state constraints on
  `BinaryAdd` (constraints 6, 8).
- `Challenge`, `AirValue` — used by the permutation / operation-bus argument
  (constraints 4, 5, 7).
- `PeriodicCol`, `ProofValue`, `AirGroupValue`, `PublicValue`, `CustomCol`.

Constraint kinds: only `everyRow`, `firstRow`, `lastRow`, `everyFrame` are
handled uniformly (they all produce the same emission — rowness is not yet
tracked in the Lean output). `everyFrame`'s `offsetMin`/`offsetMax` are
ignored.

Constraints that hit an unsupported operand are silently skipped with a
warning on stderr, and the extracted Lean file contains a one-line comment
recording the skip reason. The boolean target constraint (`constraint_0` for
`BinaryAdd`) does not touch any of these, which is why Phase 0 ships.

Phase 1 must add `FixedCol`, `Challenge`, `AirValue` to render the Main AIR,
and will need to distinguish `firstRow` / `lastRow` / `everyFrame` from
`everyRow` at the Lean level.

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
