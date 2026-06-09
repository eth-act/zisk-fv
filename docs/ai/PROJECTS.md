# Mem Read Discharge

Active stream to discharge the `LoadPromises.mem_read` promise hypothesis (the
"Memory load byte agreement" trust class): prove circuit-side memory replay
soundness from extracted Mem AIR continuity/ordering constraints, leaving one
narrow visible Sail-memory-timeline hypothesis on the global theorem in the
`aeneasBridgeTrust` idiom. Salvages the replay core, Mem AIR segment machinery,
and table-projection lemmas from the derailed `memory-trust-gap` branch while
scrapping its ~13k-line `AcceptedFullExecutionMemory*` wrapper stack; supersedes
that branch's `PLAN_MEMORY_TRUST_GAP{,_CLOSURE}.md`. Work lands from the
`mem-read-discharge` worktree in reviewable slices: setup/docs cleanup, port
core, prove the Mem-table side, then swap the boundary.
