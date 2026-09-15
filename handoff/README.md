# Handoff from the originating machine

This branch exists only to transport files that are gitignored or unpushable from the machine where
the mutation sweep ran. **The receiving side tracks nothing from here.** Restore what it needs into
the gitignored locations and let this branch rot.

Execution of the extraction-fidelity work moved to `extraction-fidelity-hardening` on another
machine. The plan of record is `docs/extraction-fidelity-plan.md` **revision 2** on that branch. The
revision-1 copy on `adversarial-mutation-sweep`, and the working copy at
`docs/ai/plan/PLAN_EXTRACTION_FIDELITY.md` carried here, are superseded and must not be edited.

## What is here

- **`docs/ai/**`** — force-added past `.gitignore:20`. The file the receiving side actually needs is
  `docs/ai/plan/archive/PLAN_S3_LOOKUP_WIRING.md`: it designed the `ValidatedLink` machinery the
  fidelity work consumes, and its PR 2a ruling constrains what a tie can claim. Restore it to its
  gitignored home. The rest is carried because it is small and triage risks loss. The two
  `*.superseded-2026-06-16.md` files were left out.
- **`handoff/stashes/`** — all 24 stashes from the originating machine as patches, `<n>.patch`
  matching `stash@{n}`, each with ref, date and message as a header comment. `INDEX.txt` lists them.
  `18.patch` and `19.patch` were untracked-file stashes and were captured with
  `--include-untracked`. The stashes were **not** dropped on the originating machine.

## Branches also pushed for this handover

Four local branches had diverged from their remotes — local commits the remote did not have, and
remote commits the local did not. Force-pushing would have destroyed the remote side, so their local
tips went to namespaced refs instead:

| ref | local-only commits | tip |
|---|--:|---|
| `handoff/330-phase4-bootwalk-path` | 27 | `0edc0e9c` |
| `handoff/330-phase4-value-telescope` | 9 | `4ad55947` |
| `handoff/issue-242-memalign` | 7 | `9b3513d2` |
| `handoff/fix-orphan-modules` | 3 | `ccd24c1d` |

The original `origin/<name>` branches are untouched and still hold the commits the local did not.
Reconciling the two sides is a decision for the receiving machine, not something done blind here.
