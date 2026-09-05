# Adversarial mutation corpus

This directory turns the 52 rounds in
`docs/adversarial-mutation-sweep.md` into reproducible fixtures. It preserves
the report's exact source precondition, edit, historical class, artifact delta,
and expected detection layer. It does not recreate evidence that the report did
not retain.

`corpus.json` is the machine-readable source of the edits. Its compact round
rows have these fields, in order:

```
round, AIR, operator, historical class, historical outcome,
source path, source line, before, after, changed generated artifacts
```

The source path starts with `zisk/`; the runner removes that prefix when it
addresses the pinned ZisK tree. All 52 edits are one-line replacements supported
by verbatim diffs in the report. The runner requires the recorded text at the
recorded line. A missing or changed precondition is an explicit infrastructure
result and is never treated as a mutation kill.

## Modes

List or inspect fixtures without build inputs:

```bash
python3 tools/adversarial-mutations/runner.py list
python3 tools/adversarial-mutations/runner.py list --json
```

Apply a fixture to an already-isolated source tree:

```bash
python3 tools/adversarial-mutations/runner.py apply \
  --round 32 --source /tmp/zisk-copy
```

`full` is the evidence-producing mode. It copies the pinned source, applies one
fixture, builds the pilout and extracted Lean through the repository's pinned
production tools, runs the independent round-trip
gate, and builds both an isolated unmutated proof tree and an isolated mutant
proof tree. The baseline must pass before a mutant failure can be called a proof
detection. Nix input revisions remain those in `flake.lock`.

For PIL mutations the runner uses `.#compile-mutation`, which installs the three
actual fixed-column payloads produced by the pinned ZisK generators and invokes
the pinned compiler directly on the private source copy. Its unmutated output
must be canonically equal to `.#zisk-pilout` before any mutant is classified.
The baseline compiler also runs in a disposable source copy. Its actual
`Main.fixed` output must match both modeled Main fixed columns over all physical
rows, and the fixed-data checker must reject an interior corruption and a
truncated file. The report records that check and the fixed payload's identity.
`--baseline-compiler-pilout` supplies an additional cached comparison; it does
not skip fresh compilation, since pilout equality alone cannot establish the
contents of separately emitted fixed data.
This avoids rebuilding the Rust/C++ fixed generators 47 times without replacing
their data with stubs. ArithTable and MemAlignRom mutations reuse the baseline
pilout because those production extraction paths read ZisK source directly.

```bash
python3 tools/adversarial-mutations/runner.py full --round 32 \
  --baseline-pilout build/zisk.pilout \
  --baseline-extraction build/extraction \
  --output mutation-results/round-32.json
```

The pinned ZisK source defaults to the `zisk-src` flake input. `--zisk-source`
may point at a previously resolved copy of that same revision. The runner checks
the locked revision against the corpus identity either way. `--skip-proof` is a
development option and deliberately returns an incomplete infrastructure result;
it cannot publish a kill.

`boundary` is the fast mode for comparing artifact pairs made elsewhere by the
same production pipeline:

```bash
python3 tools/adversarial-mutations/runner.py boundary --round 32 \
  --baseline-pilout /path/base/zisk.pilout \
  --mutant-pilout /path/mutant/zisk.pilout \
  --baseline-extraction /path/base/Extraction \
  --mutant-extraction /path/mutant/Extraction
```

It compares canonical polynomial identities, every generated artifact, and both
round-trip controls. A real artifact delta stops at the proof boundary and is
reported as incomplete; only full mode can distinguish proof detection from a
fidelity miss.

CI-facing suites create their own source mutants through the full production
pipeline. The boundary profile selects one mutation for each repaired interface
(rounds 5, 7, 32, 38, and 50); the full profile runs all fixtures:

```bash
python3 tools/adversarial-mutations/runner.py suite \
  --profile boundary --results-dir mutation-results/boundary
python3 tools/adversarial-mutations/runner.py suite \
  --profile full --results-dir mutation-results/full
```

For focused reproduction, repeat `--round`, for example
`--round 7 --round 38`; profile defaults remain fixed when no override is given.

The suite owns one private proof workspace and restores the pinned generated
artifacts before every round. A green baseline build is required immediately
before installing that round's mutant artifacts. This keeps one mutable Lake
cache without allowing a previous mutant to serve as the baseline. Each source
copy and transient workspace is deleted after its logs and JSON are copied under
`results-dir/round-NN/`; uploaded reports therefore contain no inaccessible
temporary log paths. Its summary fails on incomplete,
infrastructure, or unexpected detection layers. The target is proof detection
for every valid mutation except round 27's documented fidelity scope boundary.
The three commutativity controls retain their historical expected false-positive
diagnostics until the syntactic weld behavior is deliberately normalized.

By default, large transient caches live in `.zisk-fv-mutation-work` beside the
repository rather than in `/tmp`; `--work-root` overrides this location.

## Outcomes and evidence

The JSON report records commands, working directories, input sizes and SHA-256
identities, elapsed times, exit codes, portable log paths, canonical constraint
deltas, generated-file deltas, historical observations, and the post-hardening
expected detection layer.
Full-mode workspaces and their logs are retained by default. `--cleanup` removes
the workspace after a complete run.

| outcome | meaning |
| --- | --- |
| `invalid` | recorded edit produced no canonical circuit or artifact change |
| `equivalent` | edit is semantically equivalent to the baseline |
| `compiler` | the pinned compiler rejected the edited source |
| `extractor` | a canonical circuit change was lost or the round-trip gate failed |
| `fidelity` | changed generated artifacts still passed the proof build |
| `proof` | a green baseline plus the isolated mutant made the proof build fail |
| `infrastructure` | missing input, precondition drift, timeout, baseline failure, or abnormal tool exit |

Timeouts and unrelated baseline failures are infrastructure outcomes. Pilout
bytes are recorded as identities but never compared for circuit meaning; the
canonical comparison uses the same independent decoder and polynomial normal
form as `tools/pilout-roundtrip`.

## Reconstruction limit

The original exploratory harness and its command logs were not committed. This
runner reconstructs the reported source edits and invokes the current pinned
production Nix derivations. Historical verdicts in `corpus.json` are labels to
compare against, not newly verified results. A round becomes current evidence
only when `full` records all required controls and returns a complete result.

Run the fast self-tests with:

```bash
python3 tools/adversarial-mutations/selftest.py
```

They check all 52 fixture records, the published scoreboard totals, mutation
isolation, source-precondition rejection, baseline artifact identity, canonical
pilout self-comparison when `build/zisk.pilout` exists, and every result class.
