# Op Envelope Gap

Depth-first stream for closing the `witness rows -> OpEnvelope` evidence gap across the opcode families while keeping generated Aeneas Lean untracked. The branch now derives Main row-shape/pin/control evidence for the covered families through `MainRowProvenance`, staged production extraction checks, and extracted-shape `OpEnvelope` constructors/bridge theorems. The local `OpEnvelope.aeneasBridgeTrust` predicate is exhaustive with no wildcard branch, while the broader `aeneas_bridge_trust` axiom remains until generated evidence is imported into main Lake.
