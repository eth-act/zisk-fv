# zisk-fv

> [!CAUTION]
> ⚠️This repository is still under construction. While the work has identified bugs in ZisK v0.17.0, the formal proofs should not be taken as providing any assurances about security of ZisK's RV64IM implementation.⚠️

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
[`trust/`](trust/README.md). The current source trust ledger contains 0
Lean axiom declarations. The global compliance theorem's transitive project
axiom closure contains 0 project declarations, recorded in
[`trust/generated/baseline-zisk-riscv-compliant.txt`](trust/generated/baseline-zisk-riscv-compliant.txt).

The narrative trust ledger is
[`trust/trusted-base.md`](trust/trusted-base.md). The generated flat index is
[`trust/generated/axiom-index.md`](trust/generated/axiom-index.md).

The checked-in RV64IM acceptance-completeness surface is two honest endpoints
(see `ZiskFv/Completeness.lean`):

```lean
ZiskFv.Completeness.sail_executable_within_supported_decode_shape  -- PROVEN, unconditional
ZiskFv.Completeness.skeletal_root_completeness                             -- CONDITIONAL on the ZisK obligations
```

`sail_executable_within_supported_decode_shape` is discharged outright: every
Sail-executable RV64IM raw word lands in the hand-written `SupportedDecodeShape`
enumeration (it computes against the real generated Sail decoder; it asserts
nothing about ZisK). `skeletal_root_completeness` is the end-to-end acceptance statement,
stated *conditionally* on the decoder/lowering/row/opcode obligations — proved
for the real extracted decoder only in the separate Aeneas extraction workspace
this build cannot import — so it stays conditional on them until that bridge
lands. This is not Clean prover completeness; the demoted
`GeneralFormalCircuit.Completeness` non-claims with `ProverAssumptions := False`
remain untouched.

The abstract `Rv.Interface`-parametrized route under `ZiskFv/Completeness/Aspirational/`
is quarantined — kept built for preservation but used by none of these endpoints.
See `ZiskFv/Completeness/Aspirational/README.md`.

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
`ProductionM2.lean` without committing generated code. The temporary project
executes every configured generated start on a sample instruction and checks
that all 68 return a row. It also checks the maintained generated-bridge
manifest for production-backed row-shape facts across the covered RV64IM
opcode surfaces: the generated Lean must compute the proof-facing row-shape
projection, including opcode, external-op flag, `m32`, `store_pc`,
source/store selectors, offsets, widths, and jump offsets.
For extraction-only timing or debugging, run
`AENEAS_CHECK_LEAN=0 nix run .#aeneas-production-extract`.

On 2026-06-03, a cold local run measured with GNU `time -v` took 3:03.88 wall
time and 5,712,564 KiB maximum RSS with generated-Lean typechecking enabled.
With `AENEAS_CHECK_LEAN=0`, the current shared-helper batch measured with
GNU `time -v` took 6.03 seconds wall time and 632,800 KiB maximum RSS; Aeneas
reported 2.242405 seconds for Lean translation of 157 declarations. After
rebasing the extraction submodule onto the same upstream ZisK `v0.17.0` revision
as the flake-pinned source, the extraction-only run reported 2.267235 seconds
for Lean translation of 159 declarations.
The current extraction batch covers the production-backed U/control-flow,
Binary/BinaryExtension, load/store, branch, MUL, and DIV/REM row-shape helper
families. The full `nix run .#test` gate additionally runs this harness with
`AENEAS_CHECK_RV_COMPLETENESS=1`, checking — in that separate workspace — the
ZisK-side coverage obligations that `ZiskFv.Completeness.skeletal_root_completeness`
takes as hypotheses. The link is documentary: this build cannot import the
Aeneas workspace, so those obligations are not yet substituted into the Lean
endpoint — `skeletal_root_completeness` stays conditional on them.

The proof-side migration target is
`ZiskFv.Compliance.MainRowProvenance`: it ties selected Main/ROM rows to
row shapes produced by the decode/lower model. The former hand-written
row-shape axiom surface is now retired from the Lean source ledger; dynamic
immediate/PC and operand-lane obligations are explicit route facts, and the
Aeneas-backed bridge predicate is an explicit global theorem hypothesis until
generated Aeneas Lean is imported by main Lake. Remaining provider-lane,
memory, and promise facts are explicit theorem inputs or promise fields
documented in the caller-burden ledgers until generated or full-ensemble
artifacts export those facts into main Lake.

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
| `zisk/`                           | ZisK source submodule for the Aeneas extraction branch, based on the same upstream `v0.17.0` revision as the flake-pinned ZisK input. |

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
