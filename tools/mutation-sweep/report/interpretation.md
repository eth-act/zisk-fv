
---

## What a passing build does and does not mean

A missed round does not mean the mutated circuit was re-verified and found sound.
Nothing read it.

**The two obligations.** A green `lake build` attests two things, and only one of
them is a Lean theorem.

1. **`model ⟹ Sail`.** This is `ZiskFv.Compliance.root_soundness`. It is proved,
   and no mutation touches it.
2. **`ZisK ⟹ model`.** This is not a theorem. It is the mirror welds, the wiring
   modules, the trust ledger and human review. **All eleven misses are in
   obligation 2.**

Mutating ZisK changes `build/extraction/Extraction/*.lean`. It does not change
`ZiskFv/**`. `root_soundness` is stated over the hand-written model, so after a
mutation it proves exactly what it proved before, from inputs that never included
the mutated constraint.

**Which way the failure runs.** The theorem does not become false — it silently
stops applying. `root_soundness` takes an `AcceptedZiskTrace`, and the model keeps
demanding the original constraint after ZisK has stopped enforcing it. So traces
the mutated machine accepts are no longer `AcceptedZiskTrace`s, the hypothesis is
unfulfillable for exactly the behaviour the mutation introduced, and the theorem
says nothing about it while continuing to look like it does. Loss of
applicability, not a false conclusion, and no signal either way.

**The narrow sense in which the mutant is “still a validly constrained circuit”.**
The model remains a coherent constraint system that implies Sail. But no new
circuit was verified: the *old* circuit kept being verified while the deployed one
drifted away from it. That distinction is the entire content of obligation 2.

**Worked example — round 32.** Mutated ZisK's `BinaryAdd` rows announce `OP_SUB`
on the 5000 bus while computing `a + b`, so a prover could discharge a `SUB`
request with an addition — and the `Binary` AIR is a second, correct `SUB`
provider, so this is an extra wrong provider for a live opcode rather than merely
an unsatisfiable circuit. On the Lean side `AirsClean/BinaryAdd/Bridge.lean:62`
still reads `op := 10`, the channel-balance argument still matches Main's `SUB`
against the `Binary` AIR, and `root_soundness` goes through — describing a machine
that no longer exists.

**What was demonstrated, and what was not.** Each missed round demonstrates that
the model stopped describing ZisK: the polynomial normal form of the named
constraint changed, `tools/pilout-roundtrip/check.py` confirms the extractor
carried that change into Lean faithfully, the build log shows Lean re-elaborated
the affected modules, and the build stayed green. **No forged proof was built
against a mutated ZisK.** That needs the prover, the way
`ZISK-DEFECT-ARITH-MUL-SIGNED-WITNESS-SOUNDNESS` was demonstrated end to end under
Docker. The unsoundness of each mutant here is an argument from its constraint
change, not an executed forgery.

**The controls invert the point.** Rounds 6, 21 and 51 rewrite one term into a
commutative image of itself. The polynomial is identical — the project's own
normal form says so — and all three turn the build **red**, because the welds are
`Iff.rfl` equalities against the generated term. So the build's sensitivity
currently tracks *syntactic identity of a 52 % subset* of the extracted
constraints, not soundness. Both directions of that mismatch are worth closing:
the false negatives cost fidelity, the false positives cost maintenance every time
ZisK reorders a product.
