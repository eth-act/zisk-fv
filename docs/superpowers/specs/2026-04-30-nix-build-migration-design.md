# Nix build migration — design

## Context

The zisk-fv build pipeline produced two artifacts via Docker
(`build/sail-lean/` and `build/zisk.pilout`) and reproducibility was
asserted via tree-hash pins in `docker/versions.txt`. CI run
[25192847660](https://github.com/eth-act/zisk-fv/actions/runs/25192847660)
exposed a real reproducibility hole: the Sail-Lean docker container's
`opam install` resolves transitive deps (`linksem`, `lem`, `dune`,
…) at build time with no version pin, so the rendered Lean tree hash
drifts whenever opam-repo serves different versions. The proofs claim
"this Sail tree is what we proved against"; that claim erodes when
the tree hash flakes.

Docker is hermetic-ish but not deterministic. Beyond the opam case,
the same Dockerfile has unpinned `apt-get install`, a moving `FROM
ubuntu:22.04` tag, `opam install` of `dune`/`sail` deps, layer
timestamps, and several other drift surfaces.

Nix's content-addressed dependency closure (via `flake.lock`) closes
this class of hole: every transitive dep is pinned by hash, the
`nixpkgs` revision pin determines exact compiler/library versions,
and the same flake produces bit-identical output across machines
modulo a small known-non-determinism set.

For an FV project whose deliverable *is* a trust boundary statement,
this matters. The migration replaces the Docker pipeline with a Nix
flake.

## Decisions made during brainstorming

1. **Replace Docker entirely.** Delete `docker/` and `versions.txt`.
   Reproducibility surface = `flake.nix` + `flake.lock`. No
   Docker-as-fallback path; one source of truth.
2. **Stop at artifacts.** The flake produces `build/sail-lean/`,
   `build/zisk.pilout`, and `ZiskFv/Extraction/*.lean`. `lake build`
   stays outside Nix (elan + mathlib's azure binary cache). Lean
   reproducibility is already nailed by the committed `lean-toolchain`
   file plus `lake-manifest.json`.
3. **No remote Nix cache (cachix) in this PR.** First-time CI runs
   will rebuild from source on the eth-act XL runner (~30 min cold).
   Cachix can layer on later as a follow-up.

## Architecture

```
flake.nix
├── inputs
│   ├── nixpkgs                       # NixOS 25.05 (latest stable)
│   ├── flake-utils
│   ├── sail-src                      # 277470b2... (was sail-commit)
│   ├── sail-riscv-src                # 04e59595... (was sail-riscv-commit)
│   ├── zisk-src                      # b3ca745b... (was pilout-zisk-commit)
│   ├── pil2-compiler-src             # tag v0.8.0
│   └── pil2-proofman-src             # tag v0.15.0
└── outputs (per system)
    ├── packages.sail-lean-tree       # Lean source tree from sail-riscv
    ├── packages.zisk-pilout          # build/zisk.pilout
    ├── packages.extracted-lean       # ZiskFv/Extraction/*.lean
    ├── packages.pil-extract          # Rust binary used at build time
    ├── apps.populate                 # cp packages → repo paths
    └── devShells.default             # elan + cargo + python3 + jq
```

User-facing flow (replaces `docker/build-*.sh`):

```bash
nix run .#populate     # produces build/sail-lean/, build/zisk.pilout,
                       # and ZiskFv/Extraction/*.lean
lake build             # FV check, unchanged
bin/test.sh            # full suite, unchanged invocation
```

## Per-package notes

- **`sail-lean-tree`**: nixpkgs already ships `sail` 0.5.2 and a
  `sail-riscv` derivation. Override the latter to use our pinned
  commits and add the `generated_lean_rv64d` cmake target. If that
  target isn't exposed via the existing derivation's args, write a
  small derivation that calls the nixpkgs `sail` compiler directly.
- **`zisk-pilout`**: builds the 3 fixed_gen Cargo binaries, runs
  them, then invokes pil2-compiler via Node. All inputs (Cargo.lock,
  npm-lock, source tarballs) are content-addressed via flake inputs.
  The `lib-float/c/lib/{libziskfloat.a,ziskfloat.elf}` mtime workaround
  carries over (creation only — no `riscv64-unknown-elf-gcc` toolchain).
- **`extracted-lean`**: depends on `pil-extract` + `zisk-pilout`. Runs
  the same `--only` filters and bus-emission extraction the existing
  shell scripts do, but inside a Nix derivation.
- **`pil-extract`**: plain `cargo build --release`. Devshell-built or
  derivation-built — both work; derivation gives content-addressing,
  devshell is simpler. Default to derivation, since it's used as a
  build input by `extracted-lean`.

## CI

`.github/workflows/proofs.yml` becomes:

```yaml
runs-on: ["self-hosted-ghr", "size-xl-x64"]
steps:
  - uses: actions/checkout@v4
  - uses: DeterminateSystems/nix-installer-action@v2
  - run: nix run .#populate
  - run: bin/test.sh
```

Caches removed from the workflow (Nix has its own model and we're not
adding a remote cache yet). The `.lake/` cache for mathlib oleans
stays — that's still elan/lake's domain.

## Trust gate

`trust/scripts/check-all.sh` is independent of the build system —
runs unchanged. The trust-gate workflow stays as-is.

## Repro check (`bin/test.sh` step 4/4)

The existing fingerprint check (`expected-zisk-pilout-fingerprint`,
`expected-sail-lean-tree-sha256` in `docker/versions.txt`) goes away.
The new audit surface is **`flake.lock`**: a single committed file
that pins every input's narHash. CI verifies the lock matches the
flake (`nix flake check`); the same way `baseline-axioms.txt` is the
audit surface for trust changes today, `flake.lock` becomes the audit
surface for build-input changes.

## Documentation refresh

- `docker/README.md` removed; replaced by a short `nix/README.md` (or
  a top-of-flake docstring).
- `CLAUDE.md`'s pipeline diagram and build/verify/test sections
  updated.
- `README.md`'s build instructions updated.
- `docs/fv/extractor-notes.md` — section about reproducibility (the
  fingerprint pin) updated to reference `flake.lock`.

## Risks

1. **`sail-riscv`'s nixpkgs derivation may not expose the Lean
   target.** Mitigation: `overrideAttrs` to add the cmake flag;
   worst case write a custom derivation using nixpkgs `sail`.
2. **First CI run is slow (~30 min cold)** because there's no remote
   cache. Acceptable for a one-PR migration; cachix is a follow-up.
3. **Nix is a new tool dependency for contributors.** Devshell
   wraps the toolchain so most users only need `nix develop` plus
   the standard `lake build`. The PR description will document the
   one-time `curl | sh` install.
4. **In-flight PRs (#1 v0.16.1 upgrade, #2 CI proofs).** Both touch
   the docker pipeline this migration deletes. Plan: land this Nix
   migration first, then rebase #1 and #2 to use the flake. Or
   merge those first and rebase this. Decision deferred to the
   implementation plan phase.

## Verification

- `nix run .#populate` populates `build/sail-lean/`, `build/zisk.pilout`,
  and `ZiskFv/Extraction/*.lean`.
- `lake build` succeeds on the populated tree (8132 jobs).
- `bin/test.sh` is green (cargo + lake + trust gate).
- `flake.lock` is committed and `nix flake check` passes.
- A fresh runner / fresh local clone produces bit-identical
  `build/sail-lean/` (same hash for the .lean tree). This was the
  property that broke under Docker.
