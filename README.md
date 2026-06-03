# zisk-fv

This repository is still undergoing quality control. Do not treat it as a
production claim that any released ZisK circuit correctly implements RV64IM.

`zisk-fv` is a Lean 4 formal-verification project for
[ZisK](https://github.com/0xPolygonHermez/zisk)'s zkVM circuit against the
[Sail RISC-V specification](https://github.com/riscv/sail-riscv), restricted
to RV64IM.

The current verification claim is:

```lean
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

That theorem dispatches all 63 covered RV64IM opcode surfaces through
`ZiskFv/Compliance/Wrappers/<Op>.lean` to the canonical `equiv_<OP>` theorem
for each instruction. `lake build` typechecking is the formal check.

## Trust Boundary

All trust-boundary documentation and all machine-checked trust ledgers live in
[`trust/`](trust/README.md). The current source trust ledger contains 7
Lean axiom declarations. The global compliance theorem's transitive project
axiom closure contains 1 of those declarations, recorded in
[`trust/generated/baseline-zisk-riscv-compliant.txt`](trust/generated/baseline-zisk-riscv-compliant.txt).

The narrative trust ledger is
[`trust/trusted-base.md`](trust/trusted-base.md). The generated flat index is
[`trust/generated/axiom-index.md`](trust/generated/axiom-index.md).
## Build And Verify

After a fresh clone, populate the generated inputs:

```bash
nix run .#populate
```

Day to day:

```bash
lake build
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
```

The full repository test path, including the pinned Aeneas transpiler
extraction harness, is:

```bash
nix run .#test
```

The RV64IM transpiler Aeneas extraction harness is pinned by `flake.lock` and can
be rerun with:

```bash
nix run .#aeneas-rv64im-extract
```

The direct-import compatibility probe for the main Lean 4.28 project is:

```bash
scripts/aeneas-rv64im-lean428-compat.sh
```

It rebuilds the pinned extraction and checks that the generated Aeneas bridge
builds under Lean 4.28 with the documented compatibility patch. The extraction harness also
hard-checks the generated manifest counts: 71 valid encoded-word cases, 3
invalid decode cases, and 71 Aeneas-to-main-static equality theorems.

The proof-side migration target is
`ZiskFv.Compliance.MainStaticRowProvenance`: it ties selected Main/ROM rows to
static rows produced by the decode/lower model. The former transpiler axiom
surface is now retired from the Lean source ledger; dynamic immediate/PC and
operand-lane obligations are explicit route facts.

## Layout

| Path                              | Purpose                                                                                                 |
| ---                               | ---                                                                                                     |
| `ZiskFv/`                         | Lean proofs, per-opcode equivalence theorems, compliance wrappers, and the global theorem.              |
| `trust/`                          | The trust ledger, generated axiom indices, caller-burden baselines, and trust-gate scripts.             |
| `build/`                          | Generated Sail-Lean, PIL extraction, and pilout artifacts. Gitignored; created by `nix run .#populate`. |
| `tools/pil-extract/`              | Rust extractor from `.pilout` protobuf to Lean constraint files.                                        |
| `tools/`                          | Auxiliary repository tooling, including trust-ledger index generation.                                  |
| `docs/extraction/`                | Non-trust notes for `pil-extract`, pilout structure, and AIR inventory.                                 |
| `nix/`, `flake.nix`, `flake.lock` | Reproducible build definitions and pinned upstream inputs.                                              |
| `zisk/`                           | ZisK source submodule used as a citation surface. The pilout is built from the flake-pinned input.      |

## Pipeline

```text
flake.lock
  |
  v
nix run .#populate
  |-- build/sail-lean/                  Sail RV64 spec compiled to Lean
  |-- build/zisk.pilout                 ZisK PIL2 constraints
  `-- build/extraction/Extraction/*.lean
       ^
       |
       tools/pil-extract

lake build
  |
  v
ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

The Sail side comes from the flake-pinned Sail and sail-riscv sources. The ZisK
side comes from the flake-pinned pilout and generated Lean extraction, wrapped
by the human-readable AIR and circuit semantics under `ZiskFv/`.
