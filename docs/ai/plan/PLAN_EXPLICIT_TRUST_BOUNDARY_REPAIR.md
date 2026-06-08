# Plan: Explicit Trust Boundary Repair

## Summary

Restore explicit trust declarations that were hidden behind caller/prover
hypotheses after PRs #55, #56, and #58. This stream does not close trust gaps,
add accepted-execution abstractions, or restore the stale hand-written
transpiler model. It keeps the useful extraction/provenance/audit machinery
while making the remaining trust visible in source and generated ledgers.

## Checklist

- [x] Narrow scope to axiom-launder revert only.
- [x] Restore the six Clean component completeness axioms in
  `ZiskFv/AirsClean/Completeness.lean`.
- [x] Rewire the affected Clean components to use the restored completeness
  axioms instead of `h_assumptions`-based prover-side completeness proofs.
- [x] Restore `ZiskFv.Compliance.aeneas_bridge_trust` as an explicit axiom.
- [x] Make `aeneas_bridge_trust` load-bearing in
  `ZiskFv.Compliance.zisk_riscv_compliant_program_bus` by adding
  `env.aeneasBridgeTrust` back to `OpEnvelope.exec_eq`.
- [x] Update trust allowlists, tolerated completeness entries, docs, and
  generated ledgers.
- [x] Run the required Lean build and trust-gate checks.
- [x] Commit the completed semantic chunk.

## Intended Trust Shape

The global theorem closure should contain exactly the soundness-relevant
project axioms:

- `ZiskFv.Compliance.aeneas_bridge_trust`
- `ZiskFv.ZiskCircuit.MemModel.row_models_sail_state_load`

The source ledger should also contain the six Clean completeness axioms. Those
are completeness-direction placeholders and should remain listed in
`trust/tolerated-completeness-axioms.txt`, not in the global soundness closure.

## Verification

Run:

```bash
lake build ZiskFv.Compliance
lake build ZiskFv
trust/scripts/regenerate.sh
trust/scripts/check-all.sh
trust/scripts/check-all-semantic.sh
lake exe trust-gate print-axiom-closure ZiskFv.Compliance.zisk_riscv_compliant_program_bus
```

If the trust gates require it, update `trust/.shrinkage-floor` to the restored
source axiom count in the same trust-boundary commit.
