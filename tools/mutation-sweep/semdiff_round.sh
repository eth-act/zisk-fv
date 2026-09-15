#!/usr/bin/env bash
SP=${SWEEP_ROOT}
N="$1"; R="$SP/rounds/$N"
[ -f "$R/mut.pilout" ] || { echo "round $N: no pilout"; exit 0; }
python3 "$SP/harness/semdiff.py" "$SP/round0.pilout" "$R/mut.pilout" > "$R/semdiff.json" 2>"$R/semdiff.err"
python3 -c "
import json,sys
d=json.load(open('$R/semdiff.json'))
ch={a:v for a,v in d['airs'].items() if v.get('changed') or v.get('dropped') or v.get('added')}
print('round $N: semantic_change=%s %s' % (d['semantic_change'], ch if ch else ''))
"
