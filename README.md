# zisk-fv

Lean 4 formal verification of the [ZisK](https://github.com/0xPolygonHermez/zisk)
zkVM against the [Sail RISC-V specification](https://github.com/rems-project/sail-riscv),
via [`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean)'s
`LeanRV64D` module.

**Phase 0 status:** CLOSED. `just verify-phase0` regenerates the BinaryAdd
pilout extraction, diffs it against the hand oracle, typechecks the Lean
package, and runs extractor unit tests.

**Phase 1 status:** CLOSED. `just verify-phase1` extends the Phase 0 gate
with Main-AIR extraction, the harness-emitted golden-trace fixture, and a
full lake build covering the compositional ADD spec
(`ZiskFv.Spec.Add.add_compositional`) and final equivalence
(`ZiskFv.Equivalence.Add.equiv_ADD`) — both with zero `sorry`. See the
phase plans and metaplan documents have been removed from the tree
(commit `ac2d5e4`); recover any of them via
`git show ac2d5e4^:ai_plans/<file>` if needed.

## Layout

| Path | Purpose |
|------|---------|
| `docs/fv/` | Live library-reference notes: trust ledger, extractor contract, AIR inventory |
| `tools/zisk-pil-extract/` | Rust CLI: decodes `.pilout` protobuf → Lean constraint definitions |
| `tools/zisk-fv-harness/` | Rust CLI: emits a golden-trace fixture (`ZiskFv/GoldenTraces/Add.lean`) |
| `ZiskFv/` | Lake 4 package (mathlib + LeanZKCircuit + LeanRV, toolchain v4.26.0) |
| `pil/zisk.pilout` | Vendored ZisK pilout (input to the extractor) |
| `vendor/zisk/` | ZisK source tree (git submodule, pinned at `48cf7ccef`) |
| `trust/` | Trust-boundary baselines + enforcement scripts. See `trust/README.md`. |
| `repro/` | Docker-based reproducibility for `pil/zisk.pilout` + Sail-Lean spec. See `repro/README.md`. |
| `site/` | Single-page trust-boundary explainer (run `site/serve.sh`, port 4044). |
| `justfile` | `verify-phase0` / `verify-phase1` gates |

## Trust gate (CI)

The trust boundary is **mechanically enforced** on every PR via
`.github/workflows/trust-gate.yml`, which runs
`trust/scripts/check-all.sh`. The gate ensures:

- All `axiom` / `opaque` / `constant` / `unsafe def` / `partial def`
  / `@[extern]` / `@[implemented_by]` declarations live in one of the
  files listed in `trust/allowed-axiom-files.txt`.
- The hash + name + location of every project axiom matches
  `trust/baseline-axioms.txt`. Any add, remove, rename, or subtle
  weakening of an axiom shows up as a diff on this file.
- No `equiv_<OP>_metaplan_tier1` theorem accepts a forbidden hypothesis
  parameter (the named parameters retired by the finishing series:
  `h_rd_val`, `h_byte_sum`, etc. — see `trust/forbidden-param-shapes.txt`).
- Sanity floors on axiom count and tier1 theorem count.

To legitimately extend the trust surface, edit the relevant allowlisted
file, run `trust/scripts/regenerate.sh`, commit the updated baseline,
and have a CODEOWNER review the `trust/baseline-axioms.txt` diff (these
files are protected by `.github/CODEOWNERS`). See `trust/README.md`
for the full process and `CLAUDE.md` for guidance to AI agents
contributing to this repo.

Run `trust/scripts/check-all.sh` locally to see what CI will check.

## Reproducibility

`pil/zisk.pilout` and the `LeanRV` Lake dependency (Sail RISC-V
semantics translated into Lean) are both **rebuildable from primary
source via Docker**. See `repro/` for the containers + verifiers:

```bash
repro/build-pilout.sh        # rebuilds pil/zisk.pilout, structural diff against vendored
repro/build-sail-lean.sh     # rebuilds the Sail-Lean tree, file-level diff against Lake-resolved
```

Pinned upstream versions live in `repro/versions.txt`. Cold builds
take ~10 min (pilout) and ~5 min (sail-lean); warm Docker layers
make subsequent runs nearly instant. The pilout build matches the
vendored copy structurally (every AIR — name, columns, constraints —
is byte-for-byte identical via `tools/zisk-pil-extract` fingerprint;
~13 KB residual binary delta is source-line-number annotations from
pil2-proofman's std/pil library, never read by the proofs). The
sail-lean build is tree-identical to the Lake-resolved
`NethermindEth/sail-riscv-lean@81c8c84f`.

## Vendored ZisK inputs

`pil/zisk.pilout` (7 MB) is vendored directly (the upstream tree gitignores
it). The rest of the ZisK tree is pulled in as a git submodule at
`vendor/zisk/`, pinned to `0xPolygonHermez/zisk@48cf7ccef` (`Merge pull request
#875 from 0xPolygonHermez/develop`). Clone with `git clone --recurse-submodules`
or run `git submodule update --init` after cloning.

## Getting started

```bash
just verify-phase0
```

First cold build takes roughly 10 minutes, dominated by `native_decide` on
Goldilocks primality.

Requires `cargo`, `just`, and the Lean toolchain (`elan`). The Lake package
pulls `mathlib` + `LeanZKCircuit` on first `lake update` (run automatically by
the `verify-phase0` target if absent).
