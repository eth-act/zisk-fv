# `nix/`

Reproducible-build flake replacing the previous `docker/` pipeline.

## Files

| File                | Purpose                                                  |
| ------------------- | -------------------------------------------------------- |
| `pil-extract.nix`   | Rust derivation for `tools/pil-extract`                  |
| `sail-lean-tree.nix`| Lean tree built from the pinned `sail-riscv` source      |
| `pil2-compiler.nix` | pil2-compiler with vendored npm deps                     |
| `zisk-pilout.nix`   | ZisK pilout build (cargo + Node)                         |
| `extracted-lean.nix`| Per-AIR extracted Lean files                             |
| `populate.nix`      | `apps.populate`; copies derivation outputs into repo paths |

The flake at the repo root composes these. Run `nix run .#populate`
after cloning to produce `build/sail-lean/`, `build/zisk.pilout`,
and `ZiskFv/Extraction/*.lean`. Then `lake build` works as usual.

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
`sail-lean-tree` and `zisk-pilout` outputs across machines.

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

## Adding a remote cache (future)

If CI cold builds become painful, set up a binary cache (cachix or
attic) and configure CI to push/pull. The flake is shaped so a
remote cache would Just Work — every derivation is pure and
content-addressed. We deliberately deferred this in the migration
PR to keep scope tight.
