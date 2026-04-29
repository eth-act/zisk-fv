● Track R fully closed. All 5 Sail-equivalence axioms retired (FENCE + DIVUW + REMUW + DIVW +
REMW).

The blocker turned out to be a HPow typeclass instance mismatch: LeanRV64D defines its own
^i : HPow Int Int Int operator (in Sail.lean), while the bridge lemma used Mathlib's ^ :
HPow Int Nat Int. They rendered identically in normal pretty-printing — same numeric value,
same characters — but set_option pp.all true exposed instHPowInt_leanRV64D vs
Monoid.toNatPow. rw's pattern unifier correctly rejects them as distinct terms. Once the
bridge was rewritten using ^i, plain rw worked.

Trust base: 73 axioms. Build green (8138 jobs).

Phase 6 status:
