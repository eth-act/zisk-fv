# zisk-pil-extract — extractor notes

Contract, pilout structure observations, and known limitations for the Phase 0
extractor at `tools/zisk-pil-extract/`.

## Contract

```
zisk-pil-extract --pilout <path> --air <needle>
                 [--output <path>] [--list]
                 [--skip-unsupported] [--only <i>[,<j>…]]
```

- `--pilout`: path to a compiled `.pilout` (protobuf, schema vendored at
  `tools/zisk-pil-extract/proto/pilout.proto`).
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

## Oracle (`BinaryAdd.hand.lean`)

`ZiskFv/ZiskFv/Extraction/BinaryAdd.hand.lean` is the differential-testing
oracle for the `BinaryAdd` extraction; `just verify-phase0` diffs the generated
file against it (whitespace-normalized) and fails on drift.

**Provenance.** The oracle was written by hand from the
`vendor/zisk/state-machines/binary/pil/binary_add.pil` source, applying the
rendering rules described in the "Contract" and "Pilout structure observations"
sections above — not by copying generator output. Metadata lines are
pass-through, not
translation:
- the `-- airgroup: …` line and the `-- witness column names:` block are
  derived from the pilout symbol table;
- per-constraint `-- binary/pil/binary_add.pil:…` debug comments are pilout
  `debug_line` strings;
- `-- constraint_N skipped: …` stubs report extractor coverage, not
  translations of skipped constraints.

If the diff gate ever fails, investigate before "fixing" it. Genuine causes:
(a) extractor output changed (flags, new operand kinds, different
parenthesization) — update the oracle to match and note the change here;
(b) extractor regressed — fix the extractor, not the oracle; (c) the `.pil`
source changed — re-translate the oracle from the new source.

## Extending

Adding a new operand kind is a match arm in `render_operand` (`src/main.rs`).
Keep the "fail loudly on unhandled cases" stance: raise an `anyhow!` so the
skip path in `render_air` emits a clearly labeled stub. Do not silently emit
`sorry` — the goal is visibility, not typecheck happiness.
