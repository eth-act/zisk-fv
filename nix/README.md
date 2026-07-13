# `nix/`

Reproducible-build flake replacing the previous `docker/` pipeline.

## Files

| File                | Purpose                                                  |
| ------------------- | -------------------------------------------------------- |
| `pil-extract.nix`   | Rust derivation for `tools/pil-extract`                  |
| `sail-lean-tree.nix`| Lean tree built from the pinned `sail-riscv` source      |
| `pil2-compiler.nix` | pil2-compiler with vendored npm deps                     |
| `zisk-pilout.nix`   | ZisK pilout build (cargo + Node)                         |
| `extracted-lean.nix`| Per-AIR extracted Lean files and Mem sidecar artifacts   |
| `aristotle-inputs.nix` | Git-distribution package for generated Sail + patched Aeneas inputs |
| `populate.nix`      | `apps.populate`; copies derivation outputs into repo paths |

The flake at the repo root composes these. `lake build` can run directly after
cloning: Clean is a pinned Git package, and the Nix-generated Sail/Aeneas
inputs are supplied by the pinned `eth-act/zisk-fv-lean-inputs` Git snapshot.
Run `nix run .#populate` when the generated PIL inputs are needed; it produces
`build/zisk.pilout`, `build/extraction/Extraction/*.lean`, and
`build/extraction/MemAirFacts.md`. `nix run .#check-aristotle-inputs` verifies
that the locked snapshot exactly matches `nix build .#aristotle-inputs` and
that the root Lake manifest has no local dependency.

## Updating the Lean-input snapshot

The snapshot is generated source, not a second hand-maintained Lake setup.
After changing its Nix inputs, run the following from this repository against a
clean checkout of `eth-act/zisk-fv-lean-inputs`:

```bash
nix run .#sync-aristotle-inputs -- write ../zisk-fv-lean-inputs
```

Commit and publish that checkout, then update the full commit in both
`lakefile.toml` and the `aristotle-inputs-src` flake input, refresh
`flake.lock` and `lake-manifest.json`, and run `nix run .#check-aristotle-inputs`.

For Project Closeout S2, `flake.lock` pins the immutable
`codygunton/clean@c87617d8e29386e1e9e4f98cfbfb6940c2eb63df` fork input. It
provides the all-row predecessor/current transition surface and canonical
component-owned indexed fixed-column materialization used by the live Mem and
Main components. The associated build-input trust note is maintained in
`trust/trusted-base.md`; the pin is a source dependency, not an accepted-trace
certificate.

## Why Nix and not Docker

The previous Docker pipeline used `apt-get install` (unpinned),
`opam install` (unpinned), and `FROM ubuntu:22.04` (moving tag).
That left several drift surfaces. CI run
[25192847660](https://github.com/eth-act/zisk-fv/actions/runs/25192847660)
exposed one: the Sail-Lean docker container's `opam install`
resolved to different transitive dep versions on different days,
producing different generated Lean trees.

For an FV project whose deliverable is a trust boundary statement,
the build inputs need to be content-addressed. Nix's `flake.lock`
pins every transitive dep (sail/sail-riscv/zisk/pil2-* sources +
nixpkgs revision) by narHash. The flake produces bit-identical
`sail-lean-tree`, `aristotle-inputs`, and `zisk-pilout` outputs across
machines.

Sanity check: this flake's outputs reproduce the prior
`expected-sail-lean-tree-sha256` (`aabc5b9f…`) and
`expected-zisk-pilout-fingerprint` (`504c8583…`) byte-for-byte. The
old per-artifact pins from `docker/versions.txt` are now subsumed by
`flake.lock`.

## What's NOT in Nix

By design, `lake build` runs **outside** the flake — via elan +
mathlib's azure binary cache. The Lean toolchain version is pinned
by the committed `lean-toolchain` file; mathlib oleans are
content-addressed by Lake's own cache. Going to a fully-Nix Lean
build would lose the mathlib azure cache (~10 min per cold compile)
for marginal repro gain on a graph that's already deterministic.

## Remote cache (Cachix)

Pre-built derivation outputs live at
[`zisk-fv.cachix.org`](https://zisk-fv.cachix.org). The
`.github/workflows/proofs.yml` workflow pulls cached store paths
before any build step, so steady-state CI runs in ~3 min instead of
~30 min cold. After a successful build, the workflow pushes new
outputs back to the cache.

Public read access is on by default — contributors who run
`nix run .#populate` after cloning will hit the cache on first build
without needing any auth setup. Authenticated push uses the
`CACHIX_AUTH_TOKEN` GitHub secret on the repo.

To populate the cache from a local build (e.g. when seeding after a
`flake.lock` change):

```bash
nix-env -iA cachix -f https://cachix.org/api/v1/install
cachix authtoken                       # paste account-scope token
nix run .#populate                     # builds locally
for drv in sail-lean-tree aristotle-inputs zisk-pilout extracted-lean; do
  nix build .#$drv && cachix push zisk-fv ./result
done
```

Public key (for trust verification):
`zisk-fv.cachix.org-1:hyAMf+R99XtroAcQmwqdHUlpTJdViLVC6xA4KMXxlIE=`
