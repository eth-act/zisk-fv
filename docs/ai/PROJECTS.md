# Mem Read Discharge

Active stream to discharge the `LoadPromises.mem_read` promise hypothesis (the
"Memory load byte agreement" trust class) by replacing per-load byte promises
with a global memory-timeline evidence boundary. The load-side field removal is
done, and load arms now consume the public `MemoryTimelineEvidence` API while
generated full-witness artifacts can construct it through
`FullWitnessGeneratedTimelineEvidence`. This plan's completion route treats
`FullWitnessMemAirSourceProverDataWitnessFacts` as the explicit
generated-artifact producer, with `FullWitnessGeneratedTimelineEvidence` as the
checked generated wrapper and Clean component broadening left as the retirement
path.
The stream salvages the replay core, Mem AIR segment machinery, and
table-projection lemmas from the derailed `memory-trust-gap` branch while
scrapping its ~13k-line wrapper stack.
