# Mem Read Discharge

Active stream to discharge the `LoadPromises.mem_read` promise hypothesis (the
"Memory load byte agreement" trust class) by replacing per-load byte promises
with a global memory-timeline evidence boundary. The load-side field removal is
done; the remaining hard work is closing `AcceptedMemoryReplayEvidence` by
proving the named concrete Mem table bridge/range facts and then lifting the
gate-verified adjacent same-address order plus zero-preloaded, row-chunked
read/write replay steps to full cross-row chronological replay and prefix-read
soundness.
The stream salvages the replay core, Mem AIR segment machinery, and
table-projection lemmas from the derailed `memory-trust-gap` branch while
scrapping its ~13k-line wrapper stack.
