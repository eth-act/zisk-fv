# mutation-sweep

Adversarial mutation testing for the extraction-fidelity work (#368, harness port is #369).

A round breaks one thing in the pinned ZisK sources, recompiles the circuit with `pil2-compiler`,
re-runs `tools/pil-extract`, installs the result where `nix run .#populate` installs it, and runs
`lake build`. A **caught** round is one where the build fails. Results:
[`docs/adversarial-mutation-sweep.md`](../../docs/adversarial-mutation-sweep.md).

## State of this directory — read before trusting it

This is the session harness, carried over so #369 does not start from nothing. **It is not ported.**

| works today | not ported |
|---|---|
| `report.py` — regenerates the committed report byte-identically from `rounds/` | the round drivers still need a writable copy of the pinned ZisK tree and hard-code nix store paths for `pil2-compiler` and `pil2-proofman` |
| `mutate.py list\|stats\|sample\|apply` — site enumeration and mutation operators | `compile_round.sh`, `test_round.sh`, `sweep.sh`, `extract.sh` assume `$SWEEP_ROOT` holds `zisk-pristine/`, `round0.pilout` and `extraction-pristine-nix/`, none of which are committed |
| `semdiff.py base.pilout mut.pilout` — polynomial-normal-form diff, reusing `tools/pilout-roundtrip` | `make_artifact.py` targets the Artifact publishing path |

Verified: `SWEEP_ROOT=$PWD/tools/mutation-sweep python3 tools/mutation-sweep/report.py` reproduces
`docs/adversarial-mutation-sweep.md` exactly.

## What is committed

- `rounds/<n>/` — the evidence for all 52 rounds: the mutation site, status, `lake build` exit code
  and duration, the Lean errors, the polynomial diff, the source diff, which generated files changed,
  the trimmed build log (the `Built …` lines only), and the hand-written note arguing why that
  mutation is a reasonable thing to break.
- `report/*.md` — the narrative fragments `report.py` assembles around the round data.
- `sites*.json` — the three sampled site sets (seeds 20260904 / 20260905 / 20260906).
- `gen_dummy_frops.py` — writes zero-filled `FrequentOps` `extern_fixed_file` payloads so PIL can be
  recompiled without building three Rust binaries from the ZisK workspace. `FrequentOps` is a virtual
  lookup table contributing no polynomial identity to any extracted AIR; round 0 confirms the
  extraction is byte-identical with these stubs.

## What #369 has to do

Make the round drivers runnable from a clean checkout, add the operators the sweep lacked
(`BUS_ID_SWAP`, `SELECTOR_ARG`, `MULTIPLICITY`, `AIRVAL`), drop `CONST_PERTURB` on `bits(n)` — it is a
`witness_bits` hint, never a constraint (#358) — and ship a `regression/` subset. Do not wire it into
CI: one round costs about ten minutes of `lake build`.
