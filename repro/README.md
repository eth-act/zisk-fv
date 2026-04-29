# `repro/` — reproducibility containers for the trusted artifacts

zisk-fv's proofs are about two artifacts that aren't checked into this
repo as source: `pil/zisk.pilout` (compiled ZisK constraint set) and
the `LeanRV` Lake dependency (Sail RISC-V semantics translated into
Lean). Both are pulled in pre-built; the question this directory
answers is *what produces them, exactly*.

## What runs

| Script                     | Builds                                         | Verifier                                           |
|----------------------------|------------------------------------------------|----------------------------------------------------|
| `build-pilout.sh`          | `pil/zisk.pilout` (the ZisK constraint set)    | Structural AIR fingerprint via `tools/zisk-pil-extract` |
| `build-sail-lean.sh`       | The `LeanRV` Lake dep (`NethermindEth/sail-riscv-lean@81c8c84f` content) | sha256 of all `*.lean` file contents (sorted) |

Both wrap a Docker container build (`Dockerfile.pilout`,
`Dockerfile.sail-lean`) and a comparison step. The pinned upstream
versions live in `versions.txt`; they're forensically derived from
the local host's reflogs and confirmed by structural-fingerprint
match against the existing artifacts.

## Pinned upstreams

See `versions.txt`. Briefly:

- **Pilout** is built from the user's personal ZisK fork
  (`github.com/codygunton/zisk@zksyncos`, commit `0bfdc9582…`) on top
  of the v0.15.0 release tag, plus the v0.8.0 `pil2-compiler` and
  v0.15.0 `pil2-proofman` toolchains. The fork adds a custom
  `u256_delegation` precompile (visible as the `U256Delegation` AIR).
- **Sail-Lean** is built from `rems-project/sail @ 277470b2` and
  `riscv/sail-riscv @ 04e59595` — the upstream HEADs at the timestamp
  (`2025-12-26 06:18 UTC`) when `NethermindEth/sail-riscv-lean` cron-
  regenerated commit `81c8c84f` (the commit Lake resolves to via the
  manifest in `ZiskFv/lake-manifest.json`).

The submodule pin at `vendor/zisk` (`48cf7ccef`) is **not** the source
of the pilout — it's a separate citation surface used by
`transpile_*` axiom docstrings. Don't conflate the two.

## Running

```bash
repro/build-pilout.sh        # ~10 min cold (Rust + Node compile + node), seconds warm
repro/build-sail-lean.sh     # ~5 min cold (OCaml + Sail + sail-riscv CMake), seconds warm
```

Both produce their output under `out/repro/`. The verifier prints
either ✅ or a per-AIR / per-file diff. Cold builds are slow; the
Docker image layers cache so subsequent runs are fast.

## What "reproducible" means here

We claim two distinct properties:

1. **Pilout reproducibility**: every AIR — its name, column count,
   and constraint count — matches the vendored `pil/zisk.pilout`
   byte-for-byte. The two binary files differ by ~13 KB in embedded
   source-line-number annotations from `pil2-proofman/std/pil`'s
   library; those annotations are diagnostic strings, never read by
   `tools/zisk-pil-extract` or the proofs. The structural fingerprint
   (`sha256 of the AIR list`) IS byte-identical.

2. **Sail-Lean tree reproducibility**: every `.lean` file produced by
   the upstream Sail compiler against `riscv/sail-riscv` matches the
   Lake-resolved `LeanRV @ 81c8c84f` byte-for-byte.

If either of these regresses, the build fails and a per-AIR or per-
file diff identifies what changed. That's the load-bearing check —
not byte-equivalence of the protobuf binary.

## Why some pins are weird

- **`codygunton/zisk@zksyncos`** instead of upstream
  `0xPolygonHermez/zisk`: the vendored pilout includes a
  `U256Delegation` AIR which only exists in this fork's
  `u256_delegation` precompile. Forensic detection: protobuf
  string-table inspection found `u256_delegation/pil/u256_delegation.pil`
  references; reflog at `/home/cody/zisk` showed the user was on
  the `zksyncos` branch when the vendored was generated.
- **No commit pin for `rems-project/sail` and `riscv/sail-riscv`** in
  upstream `NethermindEth/sail-riscv-lean`: that repo's CI clones
  HEAD without a `--branch` flag and regenerates every 6 hours. We
  pin the HEADs at the regen timestamp ourselves so the chain has a
  stable reference point.

## Future hardening (not yet implemented)

- Byte-identical pilout reproduction would require pinning the exact
  `pil2-proofman` *commit* (not just tag) the user had locally — the
  v0.15.0 tag's std/pil files appear to be the right content but the
  embedded line numbers shift. Tracking this further would mean
  vendoring `pil2-proofman` as a submodule.
- A CI workflow that runs both repro scripts on every PR (very slow;
  probably gated on `[repro]` PR label rather than every push).
- Move `versions.txt` checks into `trust/scripts/check-all.sh` so
  the repro pins are part of the trust gate.
