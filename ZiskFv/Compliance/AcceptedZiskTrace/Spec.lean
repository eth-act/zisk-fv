import ZiskFv.Compliance.AcceptedZiskTrace

/-!
# Derived per-AIR spec accessor

`AcceptedZiskTrace` carries only the two genuine accepted-trace fields
(`constraints_hold`, `channels_balanced`). The per-AIR *spec* — that each table
really computes its intended relation — is **derived**, not assumed, and lives
here as the accessor `AcceptedZiskTrace.spec_holds`.
-/

namespace ZiskFv.Compliance

/-- `spec_holds` is **derived**, not assumed: the spec each AIR encodes follows
    from the accepted `constraints_hold` and `channels_balanced` via the
    ensemble's table-soundness (`witness_spec_of_constraints`). It is
    `@[reducible]` so every consumer (and the trust gate's `whnfR`) sees through
    it exactly as it did the former struct field. -/
@[reducible] def AcceptedZiskTrace.spec_holds (trace : AcceptedZiskTrace) : trace.witness.Spec :=
  ZiskFv.AirsClean.FullEnsemble.witness_spec_of_constraints
    trace.witness trace.constraints_hold trace.channels_balanced

end ZiskFv.Compliance
