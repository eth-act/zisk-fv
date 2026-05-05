# zisk-fv

Lean 4 formal verification of the [ZisK](https://github.com/0xPolygonHermez/zisk)
zkVM against the [Sail RISC-V specification](https://github.com/rems-project/sail-riscv),
via [`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean)'s
`LeanRV64D` module. This effort follows the pattern established by [openvm-fv](https://github.com/openvm-org/openvm-fv), and we are grateful to the authors of that library for their excellent work.

**Status:** all 63 RV64IM opcodes proved equivalent to the Sail spec
(0 sorries, 82 trusted axioms — see `docs/fv/trusted-base.md`). The
load-bearing claim is `lake build`: every per-opcode equivalence theorem
typechecks. Run `bin/test.sh` for the full suite (cargo + lake + trust
gate + repro hashes).

## Layout

| Path                   | Purpose                                                                                                |
| ---------------------- | ------------------------------------------------------------------------------------------------------ |
| `docs/fv/`             | Live library-reference notes: trust ledger, extractor contract, AIR inventory                          |
| `tools/pil-extract/`   | Rust CLI: decodes `.pilout` protobuf → Lean constraint definitions                                     |
| `ZiskFv/`              | Lake 4 package (mathlib + LeanZKCircuit + LeanRV, toolchain v4.26.0)                                   |
| `zisk/`                | ZisK source tree (git submodule, pinned at `48cf7ccef`)                                                |
| `trust/`               | Trust-boundary baselines + enforcement scripts. See `trust/README.md`.                                 |
| `docker/`              | Docker container that builds the pilout + Sail-Lean spec from upstream source. See `docker/README.md`. |
| `build/`               | Generated artifacts (`build/zisk.pilout`, `build/sail-lean/`). Gitignored — produced by `docker/`.     |
| `bin/`                 | Test entry point: `bin/test.sh` runs the full suite.                                                   |
| `docs/site/`           | Single-page trust-boundary explainer (run `docs/site/serve.sh`, port 4044).                            |

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

## First-time setup — build the spec + pilout

zisk-fv reads two artifacts that aren't checked into the repo: the
Sail-Lean RV64D **spec** (the Lean translation of the official Sail
RISC-V specification, which is what the proofs are _about_) and the
ZisK pilout (compiled constraint set, which is what the proofs are
_checked against_). **Both are built locally from primary source via
Docker** — nothing is pulled pre-built. Run these two commands once
after cloning, in either order:

```bash
docker/build-sail-lean.sh    # ~5 min cold; produces build/sail-lean/
docker/build-zisk-lean.sh    # ~6 min cold; produces build/zisk.pilout AND
                             # ZiskFv/Extraction/*.lean (gitignored — these
                             # are pilout → Lean constraint definitions)
```

After that, the artifacts persist under `build/` and `ZiskFv/Extraction/`,
reused on every subsequent `lake build`. Re-run only when
`docker/versions.txt` or `docker/Dockerfile.*` changes.

The lakefile points at `build/sail-lean/` via a path-based require,
so `lake build` reads the locally-built spec — there is no upstream
git dep for the spec to drift against. Pinned upstream versions live
in `docker/versions.txt`; the expected sha256 of the produced
sail-lean tree is verified there too.

## Vendored ZisK inputs

The ZisK tree is pulled in as a git submodule at `zisk/`,
pinned to `0xPolygonHermez/zisk@48cf7ccef` (`Merge pull request #875
from 0xPolygonHermez/develop`). Clone with
`git clone --recurse-submodules` or run `git submodule update --init`
after cloning. The submodule is the source-text reference for
`transpile_*` axiom rationales; it is **not** the source of the
pilout (see `docker/README.md` — the pilout is built from a personal
fork that adds the U256Delegation precompile).

## Getting started

After the first-time Docker builds (above), three commands cover everything:

```bash
docker/build-zisk-lean.sh    # regenerates ZiskFv/Extraction/*.lean from build/zisk.pilout (~seconds)
lake build                   # the FV check — every per-opcode equivalence theorem typechecks
bin/test.sh                  # full test suite: cargo + lake + trust gate + repro hashes
```

`lake build` succeeding **is** the formal-verification claim. Everything
in `bin/test.sh` past `lake build` (cargo unit tests, trust gate, repro
hashes) is auxiliary scaffolding around that core proof check.

First cold `lake build` takes roughly 10 minutes, dominated by
`native_decide` on Goldilocks primality. Requires `cargo` and the Lean
toolchain (`elan`); no other build-system dependency.
