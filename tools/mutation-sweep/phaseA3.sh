#!/usr/bin/env bash
SP=${SWEEP_ROOT}
N="$1"
SITE=$(python3 -c "import json,sys;print(json.dumps(json.load(open('$SP/harness/sites_v3.json'))[int(sys.argv[1])-45]))" "$N")
"$SP/harness/compile_round.sh" "$N" "$SITE"
