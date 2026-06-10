# Mem Read Discharge

Active stream to discharge the `LoadPromises.mem_read` promise hypothesis (the
"Memory load byte agreement" trust class) by replacing per-load byte promises
with a global memory-timeline evidence boundary. The load-side field removal is
done; the remaining hard work is closing `AcceptedMemoryReplayEvidence` by
proving the named `FullWitnessMemTableGeneratedRowsBridge` for the concrete
Mem table, proving the new `MemTableGeneratedRangeFacts` range-check surface,
and then proving cross-row chronological replay plus prefix-read soundness. The
stream salvages the replay core, Mem AIR segment machinery, and table-projection
lemmas from the derailed `memory-trust-gap` branch while scrapping its ~13k-line
wrapper stack.
