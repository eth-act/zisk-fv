# Op Envelope Gap

Depth-first stream for closing the `witness rows -> OpEnvelope` evidence gap across the opcode families while keeping generated Aeneas Lean untracked. The branch derives Main row-shape/pin/control evidence for the covered families through `MainRowProvenance`, staged production extraction checks, and extracted-shape `OpEnvelope` constructors/bridge theorems. `bus_shape` caller burden is zero, generated row-shape checks are guarded by a checked manifest, and the remaining bridge/row-shape/promise entries are documented generated/full-ensemble integration boundaries. This later repair makes `ZiskFv.Compliance.aeneas_bridge_trust` explicit again as a global trust axiom rather than hidden constructor-field trust.

# Explicit Trust Boundary Repair

Follow-on plan to undo the trust-boundary laundering introduced when explicit axioms were replaced by harder-to-spot hypotheses and fields. Scope is intentionally narrow: restore the six Clean completeness placeholders as named source-ledger axioms, restore `ZiskFv.Compliance.aeneas_bridge_trust` as a load-bearing global axiom, and update the allowlists/generated ledgers/docs to match. This is not a trust-gap-closing plan and does not restore the stale hand-written transpiler model. Verification passed with `lake build ZiskFv`, `trust/scripts/check-all.sh`, `trust/scripts/check-all-semantic.sh`, and the global closure print.

# Axiom Weakening

Plan to restore consistency by weakening the two blanket project axioms in the global compliance closure instead of hiding or proving new ZisK claims. Step 1 demotes `aeneas_bridge_trust` and `row_models_sail_state_load` to visible hypotheses, verifies the global closure drops from two project axioms to zero, rejects the `False` probe, updates trust ledgers/docs, and leaves proof discharge to later work. Step 2 is explicitly deferred to the Aeneas extracted-shape provenance thread and the memory replay relation in `PLAN_MEMORY_TRUST_GAP_CLOSURE`.
