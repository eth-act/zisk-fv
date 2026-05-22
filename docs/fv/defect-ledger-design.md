# Defect ledger design

This document defines how zisk-fv should handle known ZisK defects while
still making precise formal claims. It is separate from the trust ledger:
the trust ledger records assumptions we accept as part of the proof
boundary; the defect ledger records known places where the implementation,
model, or current proof architecture does not justify the unqualified
compliance claim.

The target is not to exclude awkward opcodes silently. The target is to
prove the strongest true theorem we can state:

```lean
zisk_riscv_compliant_program_bus_except_known_defects
```

and to recover the unqualified theorem only when the defect ledger has no
open defect that weakens the claim.

## Design rule

Every known defect must be visible in three places:

1. a human-readable ledger entry in `docs/fv/defects.md`;
2. a Lean predicate under `ZiskFv/Compliance/Defects.lean` naming the exact
   excluded behavior or blocked witness shape;
3. a top-level theorem statement whose name and hypotheses make the
   exception explicit.

The theorem must exclude the smallest behavior we can justify. Excluding an
entire opcode is allowed only when the defect really covers the whole opcode.

## What belongs in the ledger

The ledger is for defects, not for ordinary scope decisions.

| Kind | Meaning | Theorem treatment |
|------|---------|-------------------|
| `implementation-semantic` | ZisK intentionally or accidentally implements less than the RV64IM Sail behavior for an in-scope opcode. | Prove compliance on the complement of a precise defect predicate. |
| `circuit-soundness` | A malicious witness can satisfy the constraints while disagreeing with the intended execution relation. | Do not advertise an unqualified compliance theorem for affected cases. Either prove a precise exclusion theorem or mark the claim blocked. |
| `trust-shape` | An axiom states an opcode-level conclusion that should instead be derived from a shared trust boundary plus finite proofs. | Replace with a shared boundary and derived projection theorems. The defect is closed only when the bad axiom disappears from the global theorem closure. |
| `modeling-gap` | The Lean model deliberately abstracts something required for the real implementation claim. | Either move it to the scope document if it is out of scope, or express it as an explicit theorem hypothesis. |

Ordinary out-of-scope items, such as precompiles or non-RV64IM extensions,
do not need defect predicates. They belong in scope documentation because
the theorem never claimed them.

## Lean shape

The defect layer should be a small semantic filter, not a new source of
trusted facts.

```lean
namespace ZiskFv.Compliance.Defects

inductive DefectId
  | fenceIncomplete
  | arithMulSignedWitnessSoundness
  | arithTableTrustShape

def Blocks (id : DefectId) (env : OpEnvelope) : Prop := ...

def NoKnownDefect (env : OpEnvelope) : Prop :=
  ∀ id, ¬ Blocks id env

end ZiskFv.Compliance.Defects
```

The global theorem should then state the qualification directly:

```lean
theorem zisk_riscv_compliant_program_bus_except_known_defects
    (env : OpEnvelope)
    (h_no_defect : Defects.NoKnownDefect env)
    ... :
    execute_instruction ... = (bus_effect ...).2
```

In the current `OpEnvelope` design there is no separate global
`h_valid : ValidTrace ...` binder: each constructor already carries the
`Valid_*` witnesses, row pins, and promise bundles needed by its wrapper.
`h_no_defect` / `h_known_bugs` is orthogonal to those fields.

If the ledger is empty, a corollary may recover the old public name:

```lean
theorem zisk_riscv_compliant_program_bus ... := ...
```

If the ledger is not empty, the unqualified theorem name should not be used
as the public final claim. Keeping an old theorem green under known-false
or knowingly incomplete assumptions is useful as an engineering checkpoint,
but it is not the verification claim.

## Before / after pseudocode

The current bad pattern is that an opcode can look fully covered while the
limitation is hidden in comments, scope prose, or an over-strong axiom:

```lean
-- BEFORE: public name looks unqualified.
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope)
    (h_promises : PromiseBundle env) :
    execute_instruction env.instr env.state =
      (bus_effect env.execRow env.memRows env.state).2 := by
  cases env with
  | fence fenceEnv =>
      -- Hidden limitation: proof only covers the no-op FENCE subset.
      exact equiv_FENCE_noop fenceEnv ...
  | mul mulEnv =>
      -- Hidden limitation: this proof may consume a false or wrong-shaped
      -- ArithTable fact that a malicious witness can exploit.
      have h_table : ArithTableOpMulFacts mulEnv.row :=
        arith_table_op_mul_axiom mulEnv.row
      exact equiv_MUL_from_table_fact mulEnv h_table ...
```

That is bad because the theorem name says "compliant", while the proof is
only true under extra facts the theorem statement does not honestly expose.

The replacement is to state the qualified theorem first:

```lean
namespace Defects

inductive DefectId
  | fenceIncomplete
  | arithMulSignedWitnessSoundness
  | arithTableTrustShape

def FenceNopEquivalent (env : FenceEnvelope) : Prop :=
  -- Exact predicate to be filled in by the FENCE triage:
  -- the current platform/model makes Sail FENCE observationally equal to
  -- PC += 4 with no register or memory effect.
  ...

def Blocks : DefectId → OpEnvelope → Prop
  | .fenceIncomplete, .fence fenceEnv =>
      ¬ FenceNopEquivalent fenceEnv
  | .arithMulSignedWitnessSoundness, .mul mulEnv =>
      MaliciousSignedMulWitnessShape mulEnv
  | .arithTableTrustShape, .mul mulEnv =>
      UsesOpcodeSpecificArithTableAxiom mulEnv
  | .arithTableTrustShape, .div divEnv =>
      UsesOpcodeSpecificArithTableAxiom divEnv
  | _, _ =>
      False

def NoKnownDefect (env : OpEnvelope) : Prop :=
  ∀ id, ¬ Blocks id env

end Defects

theorem zisk_riscv_compliant_program_bus_except_known_defects
    (env : OpEnvelope)
    (h_no_defect : Defects.NoKnownDefect env) :
    execute_instruction env.instr env.state =
      (bus_effect env.execRow env.memRows env.state).2 := by
  cases env with
  | fence fenceEnv =>
      have h_fence : Defects.FenceNopEquivalent fenceEnv := by
        -- Derived from h_no_defect, not assumed silently.
        exact not_not.mp (by
          intro h_not
          exact h_no_defect .fenceIncomplete h_not)
      exact equiv_FENCE_noop fenceEnv h_fence ...
  | mul mulEnv =>
      have h_not_bad_witness :
          ¬ Defects.MaliciousSignedMulWitnessShape mulEnv := by
        intro h_bad
        exact h_no_defect .arithMulSignedWitnessSoundness h_bad

      -- Correct direction: derive opcode facts from a shared table boundary.
      have h_member : ArithTableSpec mulEnv.arithRow :=
        arith_mul_table_lookup_sound mulEnv ...
      have h_mode : MulModeFacts mulEnv.arithRow :=
        ArithTableProjections.Mul.mul_basic_mode_pin h_member

      exact equiv_MUL_from_projected_table_facts
        mulEnv h_not_bad_witness h_member h_mode ...
```

Once a defect is retired, the corresponding `Blocks` arm disappears. If all
claim-weakening defects disappear, the old theorem name can be restored as
a corollary:

```lean
theorem zisk_riscv_compliant_program_bus
    (env : OpEnvelope) :
    execute_instruction env.instr env.state =
      (bus_effect env.execRow env.memRows env.state).2 := by
  apply zisk_riscv_compliant_program_bus_except_known_defects
  · intro id h_blocks
    cases id <;> cases h_blocks
```

## FENCE example

FENCE should remain in the 63-opcode coverage set. If ZisK only implements
the no-op subset, the defect predicate should describe exactly the missing
behavior rather than dropping FENCE from compliance.

Current code proves FENCE as a no-op under Machine mode and the Sail
concurrency stub:

- `ZiskFv/SailSpec/fence.lean` reduces Sail FENCE to `nextPC := PC + 4`;
- `ZiskFv/EquivCore/Fence.lean` connects that pure result to the Main row;
- `ZiskFv/Compliance/Wrappers/Fence.lean` exposes the canonical wrapper.

That may be a valid modeled subset, but it should be named as such. A
ledgered defect would look like:

```lean
def FenceNopEquivalent (...) : Prop := ...

def Blocks : DefectId → OpEnvelope → Prop
  | .fenceIncomplete, .fence env => ¬ FenceNopEquivalent env
  | _, _ => False
```

The FENCE wrapper would prove compliance under `FenceNopEquivalent`, and
the global theorem would carry `NoKnownDefect env`. When ZisK implements
the full FENCE behavior, the defect entry and predicate are removed, and
the unqualified theorem is restored by proof, not by prose.

## Arith examples

The ArithTable issue is not an opcode semantic exception. It is a
trust-shape defect: old `arith_table_op_*` axioms asserted opcode-specific
facts that should be theorems from shared ArithTable lookup membership plus
finite-table projections. The correct close condition is mechanical:

- the bad opcode-shaped axioms are gone from `#print axioms
  ZiskFv.Compliance.zisk_riscv_compliant_program_bus`;
- replacement facts are proved from `ArithTableSpec` or equivalent
  table-membership predicates;
- the only remaining external boundary is the shared lookup/permutation
  statement.

The malicious signed-multiply witness issue is a circuit-soundness defect,
not a normal “program input” exception. If a row can satisfy the circuit and
disagree with the intended signed multiply result, the affected compliance
claim is blocked until the row relation is repaired or the theorem
explicitly excludes that witness shape. It should not be hidden by adding
or renaming table axioms.

## Ledger fields

Each entry in `docs/fv/defects.md` should have these fields:

| Field | Requirement |
|-------|-------------|
| `id` | Stable identifier, e.g. `ZISK-DEFECT-FENCE-INCOMPLETE`. |
| `kind` | One of the four kinds above. |
| `status` | `open-needs-triage`, `open`, `mitigated`, `fixed-upstream`, or `retired`. |
| `affected` | Opcodes, AIRs, theorem names, and trust classes affected. |
| `condition` | The exact Lean predicate or planned predicate that captures the defect. |
| `evidence` | Upstream issue, source citation, repro branch, test, or proof note. |
| `claim impact` | What theorem name or hypothesis changes while this defect is open. |
| `retirement condition` | The exact build/proof/closure condition that lets us delete the entry. |

`retired` entries should stay in the ledger for one release cycle or major
branch phase, then move to an archive section if useful.

## Gate

The ledger should get a lightweight syntactic gate once the Lean predicates
exist:

1. every open-needs-triage, open, or mitigated ledger `id` appears in
   `ZiskFv/Compliance/Defects.lean`;
2. every constructor of `DefectId` appears in the ledger;
3. the public global theorem name contains `except_known_defects` whenever
   any open or mitigated defect has `claim impact = weakens theorem`;
4. no new trust-ledger axiom may cite a defect as its justification.

This gate is deliberately separate from the trust gate. A defect is not a
trusted fact; it is a visible weakening or blocker on the claim.
