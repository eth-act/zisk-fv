# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: shared accepted full-execution memory trace construction after verified direct provider-row cursor selection theorem split. The global theorem surface now has provider-shaped boundaries at the primary, shared-trace, accepted AIR/Main/Mem, and shared-row-extraction levels.

Blocking: the selected-row provenance fact is proved, but it does not by itself prove `MainProgramRomRowsSourceMultiplicitySound`: that predicate quantifies over any arbitrary `MainRowWithRom` matching opaque `program i`, and Main self-provider exclusion can involve an arbitrary provider Main row. The direct route should therefore use positive aligned mutable-Mem route evidence, or a real program-wide ROM/source provenance theorem if that becomes necessary. The larger global blocker remains: accepted full execution data still does not construct the accepted Mem row trace or selected load coverage, including duplicate-free chronological rows, prefix read soundness, initial agreement, accepted row-list construction, selected row occurrence, and selected cursor construction.

Next step: prove construction of the shared accepted full-execution memory trace and per-envelope selected provider-row/prefix coverage from accepted execution data.

Verification: current direct provider-row cursor theorem split passes focused `lake build ZiskFv.Compliance`, full `lake build`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and `nix run .#test`.

Digression: latest project-arc checkpoint: overall memory-trust closure is about 65-70% complete structurally, but the final accepted-execution memory theorem remains substantially unproved. The current direct-`LD` route work has proved two of four non-mutable exclusions, reduced Main self-provider to a named global multiplicity/source-legality invariant, and added a table-parametric compliance boundary that avoids the witness-selected-table mismatch. New finding still stands: generic MemAlign is not simply impossible for width-8 loads, because unaligned width-8 accesses use MemAlign in ZisK; no ZisK bug is indicated.
