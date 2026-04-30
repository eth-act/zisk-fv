#!/bin/bash
# zisk-fv test entry point. Single source of truth for "is the
# project green?" Runs every check in dependency order so a clean
# exit means: builds, has zero sorries, every theorem is the right
# shape, and the trust gate is satisfied.
#
# Bootstrap on a fresh clone — both must run before this script:
#   docker/build-sail-lean.sh    (~5 min cold)
#   docker/build-zisk-lean.sh    (~6 min cold; calls build-pilout.sh)
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

# 4. Repro hashes for the two artifacts. Verifies build/zisk.pilout
# and build/sail-lean/ haven't drifted from the pinned versions.
run "4/4 repro hashes"         bash -c '
    EXTRACT=tools/pil-extract/target/release/zisk-pil-extract
    expected_pilout=$(grep "^expected-zisk-pilout-fingerprint" docker/versions.txt 2>/dev/null | awk -F"= *" "{print \$2}")
    actual_pilout=$($EXTRACT --pilout build/zisk.pilout --list 2>/dev/null | sha256sum | awk "{print \$1}")
    if [ -n "$expected_pilout" ] && [ "$expected_pilout" != "$actual_pilout" ]; then
        echo "❌ build/zisk.pilout fingerprint drift"
        echo "   expected: $expected_pilout"
        echo "   actual:   $actual_pilout"
        exit 1
    fi
    expected_sail=$(grep "^expected-sail-lean-tree-sha256" docker/versions.txt | awk -F"= *" "{print \$2}")
    actual_sail=$( (cd build/sail-lean && find . -type f -name "*.lean" ! -path "./.lake/*" -print0 | sort -z | xargs -0 sha256sum) | sha256sum | awk "{print \$1}")
    if [ "$expected_sail" != "$actual_sail" ]; then
        echo "❌ build/sail-lean/ tree hash drift"
        echo "   expected: $expected_sail"
        echo "   actual:   $actual_sail"
        exit 1
    fi
    echo "  ✅ both artifacts match docker/versions.txt"
'

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
