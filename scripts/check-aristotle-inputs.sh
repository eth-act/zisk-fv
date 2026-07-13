#!/usr/bin/env bash

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

generated=$(nix build --no-link --print-out-paths .#aristotle-inputs)
locked=$(nix build --no-link --print-out-paths .#aristotle-inputs-source)

for snapshot in "$generated" "$locked"; do
  if [[ -e "$snapshot/lake-manifest.json" ]]; then
    echo "The Lean-input snapshot must not contain a root lake-manifest.json: $snapshot" >&2
    echo "Its root lakefile.toml is the sole package configuration." >&2
    exit 1
  fi
done

if ! diff -ruN --exclude=.git --exclude=.lake --exclude=lake-manifest.json \
  "$generated/" "$locked/"; then
  echo "Aristotle input snapshot differs from the Nix-generated source." >&2
  echo "Regenerate it with: nix run .#sync-aristotle-inputs -- write <snapshot-checkout>" >&2
  exit 1
fi

if ! jq -e 'all(.packages[]; .type != "path")' lake-manifest.json >/dev/null; then
  echo "Lake manifest still contains local path dependencies:" >&2
  jq -r '.packages[] | select(.type == "path") | "  - \(.name): \(.dir)"' lake-manifest.json >&2
  exit 1
fi

snapshot_rev=$(jq -r '.nodes."aristotle-inputs-src".locked.rev' flake.lock)
if ! python3 - "$snapshot_rev" <<'PY'
import sys
import tomllib

snapshot_rev = sys.argv[1]
with open("lakefile.toml", "rb") as file:
    lakefile = tomllib.load(file)

requirements = lakefile.get("require", [])
if not isinstance(requirements, list):
    print("lakefile.toml has an invalid [[require]] section.", file=sys.stderr)
    raise SystemExit(1)

path_requirements = [requirement.get("name", "<unnamed>")
                     for requirement in requirements if "path" in requirement]
if path_requirements:
    print("lakefile.toml still contains local path dependencies: "
          + ", ".join(path_requirements), file=sys.stderr)
    raise SystemExit(1)

snapshots = [requirement for requirement in requirements
             if requirement.get("name") == "ZiskFvLeanInputs"]
if len(snapshots) != 1:
    print("lakefile.toml must contain exactly one ZiskFvLeanInputs requirement.", file=sys.stderr)
    raise SystemExit(1)

snapshot = snapshots[0]
if (snapshot.get("git") != "https://github.com/eth-act/zisk-fv-lean-inputs"
        or snapshot.get("rev") != snapshot_rev):
    print("lakefile.toml does not pin ZiskFvLeanInputs to flake.lock revision "
          + snapshot_rev + ".", file=sys.stderr)
    raise SystemExit(1)
PY
then
  exit 1
fi

if ! jq -e --arg rev "$snapshot_rev" '
  any(.packages[];
    .name == "ZiskFvLeanInputs" and
    .type == "git" and
    .url == "https://github.com/eth-act/zisk-fv-lean-inputs" and
    .rev == $rev)
' lake-manifest.json >/dev/null; then
  echo "Lake manifest does not pin ZiskFvLeanInputs to flake.lock revision $snapshot_rev." >&2
  exit 1
fi

echo "Aristotle inputs match the Nix snapshot and Lake has no path dependencies."
