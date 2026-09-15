#!/usr/bin/env bash
# Phase A for one round: apply the mutation to a private copy of the pinned
# ZisK tree, recompile PIL -> pilout (if the mutated file feeds the pilout),
# then re-extract Lean. Leaves everything under $SP/rounds/NN/.
set -uo pipefail
SP=${SWEEP_ROOT}
N="$1"; SITE="$2"
R="$SP/rounds/$N"; rm -rf "$R"; mkdir -p "$R/Extraction"
echo "$SITE" > "$R/site.json"

TREE="$R/zisk"
cp -al "$SP/zisk-pristine" "$TREE"
REL=$(python3 -c "import json,sys;print(json.loads(sys.argv[1])['file'])" "$SITE")
KIND=$(python3 -c "import json,sys;print(json.loads(sys.argv[1])['kind'])" "$SITE")
rm -f "$TREE/$REL"; cp "$SP/zisk-pristine/$REL" "$TREE/$REL"   # break the hard link
python3 "$SP/harness/mutate.py" apply "$TREE" "$SITE" || { echo "APPLY_FAILED" > "$R/status"; exit 1; }
diff -u "$SP/zisk-pristine/$REL" "$TREE/$REL" > "$R/source.diff"

if [ "$KIND" = "pil" ]; then
  ( cd "$TREE" && node --max-old-space-size=16384 \
      /nix/store/l1qla9chybhkiw893rqfyj75jx61px0j-pil2-compiler-0.9.0/src/pil.js pil/zisk.pil \
      -I pil,/nix/store/zqhhhzb9rq7gcbv46c1fz4k91pk42yni-source/pil2-components/lib/std/pil,state-machines,precompiles \
      -i "$PWD" -o "$R/mut.pilout" -O fixed-to-file ) > "$R/compile.log" 2>&1
  if [ $? -ne 0 ] || [ ! -s "$R/mut.pilout" ]; then
    echo "COMPILER_REJECTED" > "$R/status"; rm -rf "$TREE"; exit 0
  fi
  if cmp -s "$R/mut.pilout" "$SP/round0.pilout"; then
    echo "PILOUT_UNCHANGED" > "$R/status"
  fi
else
  cp "$SP/round0.pilout" "$R/mut.pilout"
fi

"$SP/harness/extract.sh" "$R/mut.pilout" "$TREE" "$R/Extraction" > "$R/extract.log" 2>&1
if [ $? -ne 0 ]; then echo "EXTRACT_FAILED" > "$R/status"; rm -rf "$TREE"; exit 0; fi

diff -rq "$SP/extraction-pristine-nix/Extraction" "$R/Extraction" > "$R/extraction.changed" 2>&1
if [ ! -s "$R/extraction.changed" ]; then
  [ -f "$R/status" ] || echo "NO_EXTRACTION_DELTA" > "$R/status"
else
  diff -u -r "$SP/extraction-pristine-nix/Extraction" "$R/Extraction" > "$R/extraction.diff" 2>&1
  [ -f "$R/status" ] || echo "READY" > "$R/status"
fi
rm -rf "$TREE"
echo "round $N: $(cat "$R/status")"
