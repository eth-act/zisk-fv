#!/bin/bash
# zisk-fv test entry point. Single source of truth for "is the
# project green?" Runs every check in dependency order so a clean
# exit means: builds, has zero sorries, every theorem is the right
# shape, and the trust gate is satisfied.
#
# Bootstrap on a fresh clone — must run once before this script:
#   nix run .#populate    (~30 min cold; ~seconds warm via Nix store cache)
#
# After that, ./bin/test.sh runs in seconds (modulo lake build).
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"

overall=0

run() {
    local name=$1; shift
    echo "::: $name :::"
    if ! "$@"; then
        echo "❌ $name failed"
        overall=1
    fi
    echo
}

# 1. Tool unit tests (extractor).
run "1/4 cargo test"           bash -c '
    cargo test --manifest-path tools/pil-extract/Cargo.toml --quiet
'

# 2. Lake build — the FV check. Every theorem typechecks. This is
# the load-bearing claim: if `lake build` is green, every per-opcode
# equivalence theorem (Sail spec = ZisK circuit + bus model) holds.
run "2/4 lake build"           lake build

# 3. Trust gate (locality + baseline + forbidden tier1 params +
# floors + zero-sorry + uniformity lint). See trust/README.md.
run "3/4 trust gate"           trust/scripts/check-all.sh

# 4. Reproducibility check. The flake.lock pins every input
# (sail/sail-riscv/zisk/pil2-* sources, nixpkgs revision) by content
# hash; `nix flake check` verifies the lock matches the flake. This
# subsumes the old per-artifact fingerprint pins from docker/versions.txt
# (which we removed): if flake.lock is green, the build inputs are
# the ones we proved against.
run "4/4 flake repro"          nix flake check --no-build

if [ $overall -eq 0 ]; then
    echo "================================"
    echo "✅ ALL CHECKS PASSED"
    echo "================================"
else
    echo "================================"
    echo "❌ SOMETHING FAILED — see above"
    echo "================================"
fi
exit $overall
