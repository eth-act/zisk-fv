# zisk-fv

Lean 4 formal verification of the [ZisK](https://github.com/0xPolygonHermez/zisk)
zkVM against the [Sail RISC-V specification](https://github.com/rems-project/sail-riscv),
via [`sail-riscv-lean`](https://github.com/NethermindEth/sail-riscv-lean)'s
`LeanRV64D` module.

**Status:** all 63 RV64IM opcodes proved equivalent to the Sail spec
(0 sorries, 82 trusted axioms — see `docs/fv/trusted-base.md`). The
load-bearing claim is `lake build`: every per-opcode equivalence theorem
typechecks. Run `bin/test.sh` for the full suite (cargo + lake + trust
gate + flake repro check).

## Layout

| Path                   | Purpose                                                                                                |
| ---------------------- | ------------------------------------------------------------------------------------------------------ |
| `docs/fv/`             | Live library-reference notes: trust ledger, extractor contract, AIR inventory                          |
| `tools/pil-extract/`   | Rust CLI: decodes `.pilout` protobuf → Lean constraint definitions                                     |
| `ZiskFv/`              | Lake 4 package (mathlib + LeanZKCircuit + LeanRV, toolchain v4.26.0)                                   |
| `zisk/`                | ZisK source tree (git submodule, pinned at `48cf7ccef`)                                                |
| `trust/`               | Trust-boundary baselines + enforcement scripts. See `trust/README.md`.                                 |
| `flake.nix`, `nix/`    | Nix flake that builds the pilout + Sail-Lean spec + extracted Lean reproducibly. See `nix/README.md`.  |
| `build/`               | Generated artifacts (`build/zisk.pilout`, `build/sail-lean/`). Gitignored — produced by `nix run .#populate`. |
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
Nix** — nothing is pulled pre-built. Requires Nix with flakes
enabled; one-time install:

```bash
curl --proto '=https' --tlsv1.2 -sSf -L \
  https://install.determinate.systems/nix | sh -s -- install
```

Then, once after cloning:

```bash
nix run .#populate    # ~30 min cold; ~seconds warm via Nix store cache
                       # produces build/sail-lean/, build/zisk.pilout,
                       # and ZiskFv/Extraction/*.lean
```

The artifacts persist under `build/` and `ZiskFv/Extraction/`, reused
on every subsequent `lake build`. Re-run only when `flake.lock` or any
`nix/*.nix` file changes (in which case the rebuild is incremental
via the Nix store).

The lakefile points at `build/sail-lean/` via a path-based require,
so `lake build` reads the locally-built spec — there is no upstream
git dep for the spec to drift against. The audit surface for build
inputs is **`flake.lock`**: it pins every transitive dependency
(sail/sail-riscv/zisk/pil2-* sources + nixpkgs revision) by content
hash, so the build is deterministic across machines.

## Vendored ZisK inputs

The ZisK tree is pulled in as a git submodule at `zisk/`,
pinned to `0xPolygonHermez/zisk@48cf7ccef` (`Merge pull request #875
from 0xPolygonHermez/develop`). Clone with
`git clone --recurse-submodules` or run `git submodule update --init`
after cloning. The submodule is the source-text reference for
`transpile_*` axiom rationales; the pilout itself is built by the
flake from a separate pinned commit of upstream zisk (see
`flake.nix::inputs.zisk-src`).

## Getting started

After the first-time `nix run .#populate` (above), three commands cover
everything:

```bash
nix run .#populate    # refresh artifacts (cached after first build)
nix develop --command lake build       # the FV check
nix develop --command bin/test.sh      # full test suite
```

Or enter the devshell once and run commands without the `nix develop`
prefix:

```bash
nix develop
lake build
bin/test.sh
```

`lake build` succeeding **is** the formal-verification claim. Everything
in `bin/test.sh` past `lake build` (cargo unit tests, trust gate,
flake repro check) is auxiliary scaffolding around that core proof
check.

First cold `lake build` takes roughly 10 minutes, dominated by
`native_decide` on Goldilocks primality. The devshell provides
`cargo`, the Lean toolchain (`elan`), python3, and jq — everything
`bin/test.sh` needs.

## Resource requirements

Cold first-time `nix run .#populate` (no Cachix hits, empty Nix
store) is bounded by the pilout build:

| Step                              | Peak RAM   | Wall time  |
|-----------------------------------|------------|------------|
| `.#zisk-pilout` (cold rebuild)    | ~17 GiB    | ~24 min    |
| `lake build` worst process (`RV64D/sd.lean`) | ~8 GiB RSS / ~7 GiB PSS | (subset of total `lake build`) |
| Everything else                   | < 5 GiB    | minutes    |

The pilout build dominates because `pil2-compiler` (Node, V8 heap
capped at 12 GiB) composes every AIR's algebraic constraints in one
process; total RSS hits ~16 GiB plus OS overhead. **A 16 GiB machine
cannot run the cold pilout build** — 32 GiB is the practical minimum.
CI runs on `size-xl-x64` (32 GiB).

Once the pilout is in the local Nix store or Cachix, every subsequent
`nix run .#populate` is a few-second cached download (~5 MB) with
trivial RAM cost. The 17 GiB ceiling only matters when a `flake.lock`
input changes (i.e. an upstream version bump).

## Build cache architecture

Three independent cache layers, each with a different scope:

| Layer                         | Caches                              | Scope                                                                   | Eviction                                  |
| ----------------------------- | ----------------------------------- | ----------------------------------------------------------------------- | ----------------------------------------- |
| **Cachix** (`zisk-fv.cachix.org`) | Nix derivations: `sail-lean-tree`, `zisk-pilout`, `extracted-lean` | Content-addressed; visible to every machine + CI run                    | Manual; near-permanent in practice         |
| **GitHub Actions cache**      | `.lake/` (compiled oleans for ZiskFv) | Per `refs/<branch-or-PR>/` ref; PR runs read their own ref + `main`'s | 7 days idle; 10 GB total per repo         |
| **Lake's Azure cache**        | Mathlib oleans (via `lake exe cache get`) | Public; content-addressed by Mathlib commit                             | Effectively never                          |

Together these mean a steady-state PR run sees: cachix HIT on all
flake outputs (no pilout rebuild), GitHub-cache HIT on `.lake` (no
ZiskFv re-elaboration), Azure HIT on mathlib (no Mathlib compile).
Cold cost is paid only when a flake input changes (cachix miss) or
when no PR has touched main in over a week (GitHub-cache miss).

### Why not a Nix-cached `lake build`?

The community project [`lean4-nix`](https://github.com/lenianiva/lean4-nix)
provides `lake2nix.mkPackage`, which builds Lake projects as content-
addressed Nix derivations and pushes results to Cachix. This would
replace the GitHub-Actions `.lake` cache with a per-content-hash one
(no 7-day eviction, no per-ref scoping). We considered it and
deliberately stayed with stock Lake. Two reasons:

1. **It would lose Mathlib's Azure cache.** `lake exe cache get`
   pulls Mathlib's oleans (multi-GB) directly from Mathlib's CI cache;
   under `lean4-nix` we'd either have to package Mathlib as a Nix
   derivation (full rebuild on every Mathlib bump, hours) or skip the
   cache and accept ~10 min cold compile per Mathlib update. The lake
   side is the part of our pipeline that already has a working
   community cache; trading it for our own cache is net negative.
2. **Granularity.** A single `mkPackage` derivation hashes over the
   entire ZiskFv source tree, so any source edit invalidates the
   whole derivation. To approach Lake's per-file incremental rebuild,
   we'd have to split ZiskFv into many derivations and hand-encode
   the import graph — duplicating Lake's bookkeeping in Nix for
   marginal benefit over what we already have.

If we ever do hit real friction (e.g. CI gaps long enough that
`.lake` evicts every time), a much smaller move is to keep stock Lake
and just relocate the `.lake` cache off GitHub Actions to S3/GCS keyed
by `(lake-manifest, lakefile, toolchain, flake.lock)` hashes —
preserves Mathlib's Azure cache, no per-ref scoping, ~30 LoC of glue.
