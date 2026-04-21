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
"Phase 1 status — CLOSED" section at the end of
`ai_plans/zisk-fv-phase-1.md` for the post-execution learnings, and
`ai_plans/zisk-fv-metaplan.md` for the overall plan.

## Layout

| Path | Purpose |
|------|---------|
| `ai_plans/` | Metaplan + per-phase planning documents |
| `docs/fv/` | Extractor contract, oracle provenance, phase handoff notes |
| `tools/zisk-pil-extract/` | Rust CLI: decodes `.pilout` protobuf → Lean constraint definitions |
| `tools/zisk-fv-harness/` | Rust CLI: emits a golden-trace fixture (`ZiskFv/GoldenTraces/Add.lean`) |
| `ZiskFv/` | Lake 4 package (mathlib + LeanZKCircuit + LeanRV, toolchain v4.26.0) |
| `pil/zisk.pilout` | Vendored ZisK pilout (input to the extractor) |
| `vendor/zisk/` | ZisK source tree (git submodule, pinned at `48cf7ccef`) |
| `justfile` | `verify-phase0` / `verify-phase1` gates |

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
Goldilocks primality (see `ai_plans/zisk-fv-phase-0.md` "What was learned"
section for why).

Requires `cargo`, `just`, and the Lean toolchain (`elan`). The Lake package
pulls `mathlib` + `LeanZKCircuit` on first `lake update` (run automatically by
the `verify-phase0` target if absent).
