# Status

Plan: `docs/ai/plan/PLAN_MEMORY_TRUST_GAP.md`

Current focus: the public theorem boundary now derives the accepted trace/table object from a full-ensemble Mem-table bridge that carries an accepted trace, a `fullRv64imEnsemble` witness, a concrete Mem table, and table-to-trace embedding.

Blocking: FullEnsemble/full execution still does not prove the Mem table embedding into chronological accepted rows, concrete selected Mem provider-row coverage, or split-indexed Sail prefix-state equality from accepted execution data.

Next step: prove the remaining full-ensemble Mem-table bridge fields from accepted full execution data, starting with projected Mem read-replay row embedding into the chronological accepted row trace.

Digression: none; current work is back on the memory trust gap plan.
