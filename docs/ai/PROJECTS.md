# Mem Read Discharge

Active stream to discharge the `LoadPromises.mem_read` promise hypothesis (the
"Memory load byte agreement" trust class) by replacing per-load byte promises
with a global memory-timeline evidence boundary. The load-side field removal is
done, and the global load boundary now asks for a full-witness memory-timeline
source whose accepted replay is derived from `FullWitnessMemReplayBridge`.
The current generated target is table-level raw sidecars
(`FullWitnessMemAirSourceRawSidecars`) that adapt to
`FullWitnessMemAirSourceRawFacts`; the remaining hard work is producing and
checking those sidecars from generated/full-ensemble output because the current
Clean Mem component does not represent the stage-2/global Mem AIR source
columns generically.
The stream salvages the replay core, Mem AIR segment machinery, and
table-projection lemmas from the derailed `memory-trust-gap` branch while
scrapping its ~13k-line wrapper stack.
