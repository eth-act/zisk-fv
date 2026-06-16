#!/usr/bin/env bash
# check-construction-theorem-binders.sh - V2: assert that the DEEP
# (recursive) binder render of the sound P4 construction theorem matches
# the committed baseline.
#
# Unlike the old blind 4-binder snapshot of `construction_beq`, this
# renders one leaf line per field reachable by recursing into every
# `ZiskFv.*` project structure in a binder type (library structures are
# leaves). Because the sound `construction_sub_sound` carries NO
# `*RowBinding` / `MainRowProvenance` deep record, the deep render is the
# flat list of its honest top-level binders — and any future attempt to
# smuggle a bucket-(a)/(c) fact inside a project structure surfaces
# immediately as new dotted leaf lines in this diff.
#
# Requires `lake build` to have run (consumes oleans).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

baseline=trust/generated/baseline-construction-theorem-binders.txt
if [ ! -f "$baseline" ]; then
  echo "trust-gate (V2): missing $baseline."
  exit 1
fi

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

lake exe trust-gate print-construction-binders-deep > "$tmp"

if diff -u "$baseline" "$tmp"; then
  echo "trust-gate (V2): DEEP construction theorem binder baseline matches."
else
  echo "trust-gate (V2): DEEP construction theorem binder baseline DIFFERS."
  echo "  Run:"
  echo "    lake exe trust-gate print-construction-binders-deep > $baseline"
  echo "  and review the diff before committing."
  exit 1
fi
