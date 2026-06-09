# Mem Read Discharge

Active stream to discharge the `LoadPromises.mem_read` promise hypothesis (the "Memory load byte agreement" trust class): prove circuit-side memory replay soundness from extracted Mem AIR continuity/ordering constraints, leaving one narrow visible Sail-memory-timeline hypothesis on the global theorem in the `aeneasBridgeTrust` idiom. Salvages the replay core, Mem AIR segment machinery, and table-projection lemmas from the derailed `memory-trust-gap` branch while scrapping its ~13k-line `AcceptedFullExecutionMemory*` wrapper stack; supersedes that branch's `PLAN_MEMORY_TRUST_GAP{,_CLOSURE}.md`. Work lands from a fresh `mem-read-discharge` worktree in three reviewable PRs: port core, prove the Mem-table side, swap the boundary.

# Op Envelope Gap

Depth-first stream for closing the `witness rows -> OpEnvelope` evidence gap across the opcode families while keeping generated Aeneas Lean untracked. The branch derives Main row-shape/pin/control evidence for the covered families through `MainRowProvenance`, staged production extraction checks, and extracted-shape `OpEnvelope` constructors/bridge theorems. `bus_shape` caller burden is zero, generated row-shape checks are guarded by a checked manifest, and the remaining bridge/row-shape/promise entries are documented generated/full-ensemble integration boundaries. This later repair makes `ZiskFv.Compliance.aeneas_bridge_trust` explicit again as a global trust axiom rather than hidden constructor-field trust.

# Explicit Trust Boundary Repair

Follow-on plan to undo the trust-boundary laundering introduced when explicit axioms were replaced by harder-to-spot hypotheses and fields. Scope is intentionally narrow: restore the six Clean completeness placeholders as named source-ledger axioms, restore `ZiskFv.Compliance.aeneas_bridge_trust` as a load-bearing global axiom, and update the allowlists/generated ledgers/docs to match. This is not a trust-gap-closing plan and does not restore the stale hand-written transpiler model. Verification passed with `lake build ZiskFv`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and the global closure print.
