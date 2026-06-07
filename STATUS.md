# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: proving source-legality from actual unified-Main row provenance after committed slice `f256fd0d` (`Split Main ROM source multiplicity burden`). The worktree has a fully verified row-indexed split ready to commit: generic ROM/source-sum eval lemmas in `ZiskFv/AirsClean/Main/Constraints.lean`, plus `MainProgramRomRowsSourceMultiplicitySound` and its bridge to the env-shaped `MainProgramRomSourceMultiplicitySound` in `ZiskFv/AirsClean/FullEnsemble/Balance.lean`.

Blocking: not blocked on the local row-indexed split; focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance` passes. The next source-legality blocker is proving `MainProgramRomRowsSourceMultiplicitySound` from actual row/source provenance. The larger global blocker remains: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: commit the verified row-indexed split, then prove `MainProgramRomRowsSourceMultiplicitySound` from actual row provenance/source facts. After that, continue toward the shared accepted full-execution memory trace plus per-envelope coverage.

Verification: current dirty row-indexed split passes focused `lake build ZiskFv.AirsClean.FullEnsemble.Balance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`. Full gates also passed for committed slice `f256fd0d`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
