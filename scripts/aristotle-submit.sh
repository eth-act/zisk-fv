#!/usr/bin/env bash
# Submit the committed tree (HEAD) of the current worktree to Aristotle.
#
# Stages `git archive HEAD` into a temp directory and submits that: tracked
# files only — no .lake (can be many GB; the client gzips the whole project
# dir and appears to hang), no build/, no submodule contents. Aristotle
# resolves all dependencies itself from the pure-Git Lake graph, so the
# "no .lake folder" preflight warning is expected and harmless.
#
# Submitting HEAD (not the dirty tree) is deliberate: what Aristotle sees is
# exactly what is committed, so its base state is always reproducible.
#
# Usage: scripts/aristotle-submit.sh <prompt-file> [extra `aristotle submit` args...]
# e.g.:  scripts/aristotle-submit.sh REFACTOR_1_PROMPT.md
set -euo pipefail

prompt_file="${1:?usage: aristotle-submit.sh <prompt-file> [extra args...]}"
shift

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "warning: worktree has uncommitted changes; submitting HEAD without them." >&2
fi

# NOTE: `aristotle submit` always creates a NEW project (named after this
# staging dir's basename). To continue an existing project with its context,
# use `aristotle continue <project-id> <prompt>` instead — no staging needed,
# but beware: the continued project's server-side tree may be stale.
root="$(git rev-parse --show-toplevel)"
branch="$(git rev-parse --abbrev-ref HEAD)"
stage="$(mktemp -d "${TMPDIR:-/tmp}/zisk-fv-${branch//\//-}.XXXXXX")"
trap 'rm -rf "$stage"' EXIT

git -C "$root" archive HEAD | tar -x -C "$stage"
echo "staged $(du -sh "$stage" | cut -f1) at $stage (HEAD = $(git rev-parse --short HEAD))" >&2

aristotle submit --project-dir "$stage" "$@" "$(cat "$prompt_file")"
