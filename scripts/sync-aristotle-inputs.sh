#!/usr/bin/env bash

set -euo pipefail

usage() {
  cat <<'EOF'
Usage: sync-aristotle-inputs {check|write} SNAPSHOT_REPOSITORY

Compare a Git checkout of zisk-fv-lean-inputs against the Nix-generated
snapshot, or replace that checkout's generated contents. `write` refuses a
dirty checkout and preserves only its .git directory.
EOF
}

if [[ $# -ne 2 ]]; then
  usage >&2
  exit 2
fi

mode=$1
destination=$2

case "$mode" in
  check|write) ;;
  *)
    usage >&2
    exit 2
    ;;
esac

repo_root=$(cd "$(git rev-parse --show-toplevel)" && pwd -P)
destination=$(cd "$destination" && pwd -P)

if [[ ! -f "$repo_root/flake.nix" ]]; then
  echo "sync-aristotle-inputs: run this command from the zisk-fv checkout" >&2
  exit 2
fi

if ! git -C "$destination" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "sync-aristotle-inputs: $destination is not a Git checkout" >&2
  exit 2
fi

destination_root=$(cd "$(git -C "$destination" rev-parse --show-toplevel)" && pwd -P)
if [[ "$destination" != "$destination_root" ]]; then
  echo "sync-aristotle-inputs: destination must be the root of its Git checkout" >&2
  exit 2
fi

if [[ "$destination" == "$repo_root" ]]; then
  echo "sync-aristotle-inputs: refusing to overwrite the zisk-fv source checkout" >&2
  exit 2
fi

origin=$(git -C "$destination" remote get-url origin 2>/dev/null || true)
origin=${origin%.git}
origin=${origin%/}
case "$origin" in
  https://github.com/eth-act/zisk-fv-lean-inputs|git@github.com:eth-act/zisk-fv-lean-inputs|ssh://git@github.com/eth-act/zisk-fv-lean-inputs)
    ;;
  *)
    echo "sync-aristotle-inputs: destination origin must be eth-act/zisk-fv-lean-inputs" >&2
    exit 2
    ;;
esac

snapshot=$(cd "$repo_root" && nix build --no-link --print-out-paths .#aristotle-inputs)

case "$mode" in
  check)
    diff -ruN --exclude=.git --exclude=.lake --exclude=lake-manifest.json \
      "$snapshot/" "$destination/"
    ;;
  write)
    if [[ -n "$(git -C "$destination" status --porcelain)" ]]; then
      echo "sync-aristotle-inputs: refusing to overwrite dirty checkout $destination" >&2
      exit 2
    fi
    rsync -a --delete --exclude=.git --exclude=.lake "$snapshot/" "$destination/"
    # Nix store sources are intentionally read-only; a checkout generated from
    # them must still be able to create `.lake/` and be committed normally.
    chmod -R u+w "$destination"
    ;;
esac
