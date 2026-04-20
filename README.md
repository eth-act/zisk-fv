# zisk-fv

Lean 4 formal verification of the [ZisK](https://github.com/0xPolygonHermez/zisk)
zkVM against the [Sail RISC-V specification](https://github.com/rems-project/sail-riscv),
via [`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean)'s
`LeanRV64D` module.

**Phase 0 status:** CLOSED. `just verify-phase0` regenerates the pilout
extraction, diffs it against the hand oracle, typechecks the Lean package, and
runs extractor unit tests — all green from a clean build. See
`ai_plans/zisk-fv-phase-0.md` (status section) for the post-execution gap
inventory and `ai_plans/zisk-fv-metaplan.md` for the overall plan.

## Layout

| Path | Purpose |
|------|---------|
| `ai_plans/` | Metaplan + per-phase planning documents |
| `docs/fv/` | Extractor contract, oracle provenance, phase handoff notes |
| `tools/zisk-pil-extract/` | Rust CLI: decodes `.pilout` protobuf → Lean constraint definitions |
| `ZiskFv/` | Lake 4 package (mathlib + LeanZKCircuit, toolchain v4.26.0) |
| `pil/zisk.pilout` | Vendored ZisK pilout (input to the extractor) |
| `state-machines/binary/pil/binary_add.pil` | Vendored ZisK PIL source (ground truth for the hand oracle) |
| `justfile` | `verify-phase0` and future `verify-phaseN` gates |

## Vendored ZisK inputs

`pil/zisk.pilout` (7 MB) and `state-machines/binary/pil/binary_add.pil` (< 1 KB)
are taken from [`0xPolygonHermez/zisk`](https://github.com/0xPolygonHermez/zisk)
at commit `48cf7ccef` (`Merge pull request #875 from 0xPolygonHermez/develop`).
Paths preserve the ZisK tree layout so upstream references remain valid.

If a future phase needs broader access to the ZisK tree (e.g. more PIL sources,
RISC-V → Zisk transpiler contract), add it as a submodule at `vendor/zisk/`
pinned to the matching commit. Phase 0 doesn't need it.

## Getting started

```bash
just verify-phase0
```

First cold build takes roughly 10 minutes, dominated by `native_decide` on
Goldilocks primality (see `docs/fv/phase-0-handoff.md` for why).

Requires `cargo`, `just`, and the Lean toolchain (`elan`). The Lake package
pulls `mathlib` + `LeanZKCircuit` on first `lake update` (run automatically by
the `verify-phase0` target if absent).
