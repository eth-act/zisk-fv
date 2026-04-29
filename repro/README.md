# `repro/` — Docker-based artifact builds

zisk-fv's proofs read two artifacts that aren't checked into the repo
as source. This directory holds the Dockerfiles + scripts that build
them from primary upstream source. **Run `repro/build-pilout.sh` once
after cloning the repo** — without it, `just verify-phase*` fails
fast with a pointer to the script.

## What runs

| Script                     | Builds                                    | Output (gitignored) |
|----------------------------|-------------------------------------------|---------------------|
| `build-pilout.sh`          | The compiled ZisK constraint set          | `build/zisk.pilout` |
| `build-sail-lean.sh`       | The `LeanRV` Lake dep (Sail-Lean tree)    | `build/sail-lean/`  |

Both wrap a Docker container build (`Dockerfile.pilout`,
`Dockerfile.sail-lean`). The pinned upstream versions live in
`versions.txt`; they're forensically derived from the local host's
reflogs and confirmed by structural-fingerprint match against the
artifacts that produced the existing extraction layer.

## Pinned upstreams

See `versions.txt`. Briefly:

- **Pilout** is built from a personal ZisK fork
  (`github.com/codygunton/zisk@zksyncos`, commit `0bfdc9582…`) on top
  of the v0.15.0 release tag, plus the v0.8.0 `pil2-compiler` and
  v0.15.0 `pil2-proofman` toolchains. The fork adds a custom
  `u256_delegation` precompile (visible as the `U256Delegation` AIR).
- **Sail-Lean** is built from `rems-project/sail @ 277470b2` and
  `riscv/sail-riscv @ 04e59595` — the upstream HEADs at the timestamp
  (`2025-12-26 06:18 UTC`) when `NethermindEth/sail-riscv-lean` cron-
  regenerated commit `81c8c84f` (the commit Lake resolves to via the
  manifest in `lake-manifest.json`).

The submodule pin at `vendor/zisk` (`48cf7ccef`) is **not** the source
of the pilout — it's a separate citation surface used by
`transpile_*` axiom docstrings. Don't conflate the two.

## Running

```bash
repro/build-pilout.sh        # ~6 min cold; seconds when image is cached
repro/build-sail-lean.sh     # ~5 min cold; seconds warm
```

Outputs land in `build/`. The Docker image layers cache so subsequent
runs are fast (the slow steps are `cargo` / `npm` / `node` / `cmake`
inside the container; once the image is built, those don't re-run).

## What "reproducible" means here

The pilout build is **structurally** reproducible: every AIR — name,
column count, and constraint count — is byte-identical to what the
checked-in `Extraction/*.hand.lean` oracles were generated from. The
extractor (`tools/zisk-pil-extract`) consumes only the AIR structure,
never the embedded source-line annotations from pil2-proofman's
std/pil library, so a structural fingerprint (sha256 of the
`--list` output) is the load-bearing check.

The Sail-Lean build is **tree-identical**: every `.lean` file matches
the Lake-resolved `LeanRV @ 81c8c84f` byte-for-byte.

## Why some pins are weird

- **`codygunton/zisk@zksyncos`** instead of upstream
  `0xPolygonHermez/zisk`: the existing extraction was produced from a
  pilout containing a `U256Delegation` AIR, which only exists in this
  fork. Forensic detection: protobuf string-table inspection found
  `u256_delegation/pil/u256_delegation.pil` references; reflog at
  `/home/cody/zisk` showed the user was on the `zksyncos` branch
  when the original pilout was generated.
- **No commit pin for `rems-project/sail` and `riscv/sail-riscv`** in
  upstream `NethermindEth/sail-riscv-lean`: that repo's CI clones
  HEAD without a `--branch` flag and regenerates every 6 hours. We
  pin the HEADs at the regen timestamp ourselves so the chain has a
  stable reference point.

## Future hardening (not yet implemented)

- Byte-identical pilout reproduction would require pinning the exact
  `pil2-proofman` *commit* (not just tag) — the v0.15.0 tag's std/pil
  files have stable content but the embedded line numbers shift
  somehow between identical-looking tag checkouts. Tracking this
  further would mean vendoring `pil2-proofman` as a submodule.
- A CI workflow that runs both repro scripts on every PR (very slow;
  probably gated on a `[repro]` PR label rather than every push).
- Move `versions.txt` checks into `trust/scripts/check-all.sh` so
  the repro pins are part of the trust gate.
