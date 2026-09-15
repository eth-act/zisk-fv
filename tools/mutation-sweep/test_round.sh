#!/usr/bin/env bash
# Phase B for one round: install the mutated pilout + re-extracted Lean into
# the worktree exactly as `nix run .#populate` would, run the extractor's own
# round-trip gate, then run `lake build` and record whether it fails.
# Rounds are chained: the next round overwrites these inputs, and
# harness/restore.sh puts the pinned inputs back at the end.
set -uo pipefail
SP=${SWEEP_ROOT}
REPO=/home/cody/zisk-fv
N="$1"; R="$SP/rounds/$N"
cd "$REPO"

ST=$(cat "$R/status" 2>/dev/null || echo MISSING)
if [ "$ST" != "READY" ]; then echo "round $N: skipped ($ST)"; exit 0; fi

cp "$SP"/extraction-pristine-nix/Extraction/*.lean build/extraction/Extraction/
cp "$R/mut.pilout" build/zisk.pilout
cp "$R"/Extraction/*.lean build/extraction/Extraction/

python3 tools/pilout-roundtrip/check.py --quiet > "$R/roundtrip.log" 2>&1
echo "$?" > "$R/roundtrip.exit"

T0=$SECONDS
/home/cody/.elan/bin/lake build --log-level=warning > "$R/build.log" 2>&1
echo "$?" > "$R/build.exit"
echo "$((SECONDS-T0))" > "$R/build.time"

grep -n "error:" "$R/build.log" | head -20 > "$R/errors.txt"
if ! grep -q "Build completed successfully" "$R/build.log" && [ ! -s "$R/errors.txt" ]; then
  echo "INVALID_RUN" > "$R/build.invalid"
else rm -f "$R/build.invalid"; fi
echo "round $N: build.exit=$(cat "$R/build.exit") roundtrip.exit=$(cat "$R/roundtrip.exit") secs=$(cat "$R/build.time")"
