# GitHub Issue Refresh

Goal: audit the open `eth-act/zisk-fv` GitHub issues against the June 22-24 refactor window and update stale code references, declaration names, filenames, and status claims.

## Checklist

- [x] Re-orient from `STATUS.md`, repo plans, and local instructions.
- [x] Collect the open issue list and the relevant refactor commits since June 22.
- [x] Inspect issues one by one for stale references.
- [x] Verify replacement names/files against the current tree.
- [x] Edit issue bodies/comments/titles as needed on GitHub.
- [x] Re-check the resulting open issue list for remaining stale references.

## Current Notes

- Remote is `eth-act/zisk-fv`; direct issue maintenance is allowed by the repo policy.
- Main refactor facts in scope: `AcceptedTrace` is now `AcceptedZiskTrace`, `ProgramBinding` is now the `SailTrace` abbreviation, `AcceptedTrace.lean` became `OpBusProviderMatch.lean`, `TraceLevelExport.lean` and several bridge files are thin aggregators over submodules, `StrongRowConstructionData` remains live, `root_completeness` was split/collapsed on completeness branches, and #114's extraction-curation discharge landed.
- Local untracked `notes.md` pre-existed this pass and is unrelated.
- Issues needing edits: #61, #74, #75, #78, #100, #101, #108, #111, #115, #116, #118, and #119. #77, #117, #127, #128, and #141 checked out as current enough for their stated scopes.
- Recent status comments to correct in place: #61 latest status, #75 status, #100 XCAP spike status, and #118 cleanup status.
- Completed GitHub edits: #61 title/body plus three archival comments and latest status; #74 body; #75 body and status comment; #78 body; #100 body and superseded spike comment; #101 body; #108 body; #111 body; #115 body; #116 body; #118 title/body and stale cleanup comment; #119 body.
- Final stale-pattern scan over open issue bodies/comments returned no hits for the pre-refresh names/files targeted by this pass.
