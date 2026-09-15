#!/usr/bin/env bash
# Run phase B for every READY round with no result yet, in numeric order.
# No self-guard: the caller must ensure nothing else is driving `lake`.
SP=${SWEEP_ROOT}
rm -f "$SP/harness/SWEEP_DONE"
while :; do
  todo=""
  for n in $(ls "$SP/rounds" | grep -E '^[0-9]+$' | sort -n); do
    R="$SP/rounds/$n"
    [ -f "$R/status.invalid" ] && continue
    [ "$(cat "$R/status" 2>/dev/null)" = "READY" ] || continue
    [ -s "$R/build.exit" ] && continue
    todo="$n"; break
  done
  [ -z "$todo" ] && break
  "$SP/harness/test_round.sh" "$todo"
  [ -s "$SP/rounds/$todo/build.exit" ] || { echo "round $todo produced no exit; aborting"; break; }
done
touch "$SP/harness/SWEEP_DONE"
echo "SWEEP DONE"
