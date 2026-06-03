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

The full repository test path, including the pinned Aeneas production-backed
lowering extraction harness, is:

```bash
nix run .#test
```

The production-backed Aeneas extraction harness is pinned by `flake.lock` and
can be rerun with:

```bash
nix run .#aeneas-production-extract
```

It writes generated LLBC/Lean artifacts under `build/aeneas-production-extraction`
and rejects unexpected trust markers such as generated axioms, opaques,
sorries, string/format models, or `HashMap` models. It also checks that every
configured extraction start appears as a generated Lean definition and that the
configured start set exactly matches the Rust extraction-wrapper surface.
The trust gate additionally checks that each `extract_<op>_from_inst` wrapper
delegates through `Riscv2ZiskContext::lower_rv64im_single_row`, and that
`Riscv2ZiskContext::convert` delegates the same mnemonic to the same opcode
variant, so the wrapper surface cannot drift into a second hand-written
lowerer. By default it also stages a temporary Lake project under `build/`,
copies the pinned Aeneas Lean runtime there, and typechecks the generated
`ProductionM2.lean` without committing generated code. The temporary project executes every
configured generated start on a sample instruction and checks that all 63
return a row. It also checks concrete generated row-shape facts for the
production-backed LUI/AUIPC/JAL/ADDW helpers and the ADD `rs1 = x0` copyb
special case: the generated Lean must compute the proof-facing row-shape
projection, including opcode, external-op flag, `m32`, `store_pc`,
source/store selectors, offsets, and jump offsets.
For extraction-only timing or debugging, run
`AENEAS_CHECK_LEAN=0 nix run .#aeneas-production-extract`.

On 2026-06-03, a cold local run measured with GNU `time -v` took 3:03.88 wall
time and 5,712,564 KiB maximum RSS with generated-Lean typechecking enabled.
With `AENEAS_CHECK_LEAN=0`, the current shared-helper batch measured with
GNU `time -v` took 6.03 seconds wall time and 632,800 KiB maximum RSS; Aeneas
reported 2.242405 seconds for Lean translation of 157 declarations. The latest
full validation run reported 2.376877 seconds for Aeneas Lean translation before
the temporary Lake project typechecked the generated Lean.
The current extraction batch covers the production-backed LUI/AUIPC/JAL/JALR
helpers, FENCE/NOP, and the RV64IM single-row register, immediate, branch,
load, and store helper families.

The proof-side migration target is
`ZiskFv.Compliance.MainRowProvenance`: it ties selected Main/ROM rows to
row shapes produced by the decode/lower model. The former hand-written row-shape axiom
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
