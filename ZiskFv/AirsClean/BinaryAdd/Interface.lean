import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.Channels.OperationBus

/-!
# Consumer-facing BinaryAdd interface

This module contains the row-local API consumed by the equivalence and
compliance layers.  It is stated entirely in terms of the Clean row and
`GeneralFormalCircuit.Spec`; no legacy named-column validator is involved.

## Q2 constraint correspondence

The four legacy predicates and the four Clean assertions agree exactly after
projecting the same ten row columns (the only notation difference is
`x - y = 0` versus `x + -y = 0` after circuit elaboration):

| Legacy predicate | Clean assertion in `BinaryAdd.main` |
|---|---|
| `boolean_cout_0` | `assertZero (cout_0 * (1 - cout_0))` |
| `carry_chain_0` | `assertZero ((a_0 + b_0) - (cout_0 * 2^32 + c_chunks_1 * 2^16 + c_chunks_0))` |
| `boolean_cout_1` | `assertZero (cout_1 * (1 - cout_1))` |
| `carry_chain_1` | `assertZero ((a_1 + b_1 + cout_0) - (cout_1 * 2^32 + c_chunks_3 * 2^16 + c_chunks_2))` |

The Clean circuit additionally performs eight static range lookups: 32-bit
lookups for `a_0`, `a_1`, `b_0`, and `b_1`, and 16-bit lookups for
`c_chunks_0` through `c_chunks_3`.  On the legacy side these were the
separate `a_chunks_in_range`, `b_chunks_in_range`, and `c_chunks_in_range`
predicates, supplied by the range-table soundness path rather than included
in `core_every_row`.  The Clean `OpBusChannel.push (opBusMessageExpr row)`
corresponds to the legacy `opBus_row_BinaryAdd` projection and its
operation-bus permutation/balance proof; it likewise was not one of the four
legacy algebraic predicates.  Thus there is no constraint divergence: the
four algebraic constraints coincide, while the extra Clean operations make
explicit the same range and operation-bus obligations previously carried by
separate legacy layers.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus

/-- The concrete operation-bus message emitted by a Clean BinaryAdd row. -/
@[reducible]
def opBusMessage (row : BinaryAddRow FGL) : OpBusMessage FGL :=
  { op := 10
    a_lo := row.a_0
    a_hi := row.a_1
    b_lo := row.b_0
    b_hi := row.b_1
    c_lo := row.c_chunks_1 * 65536 + row.c_chunks_0
    c_hi := row.c_chunks_3 * 65536 + row.c_chunks_2
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Evaluation commutes with the BinaryAdd operation-bus row projection. -/
theorem eval_opBusMessageExpr
    (env : Environment FGL) (row : Var BinaryAddRow FGL) :
    eval env (opBusMessageExpr row) = opBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [opBusMessageExpr, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, Expression.eval]
  repeat constructor

/-- Component-specialized form of `eval_opBusMessageExpr`. -/
theorem component_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr component.rowInputVar) =
      opBusMessage (component.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env))

/-- The semantic `Spec`, together with its lookup-derived range facts, gives
exactly the RV64 wrapping-add equation needed by instruction equivalence. -/
theorem binary_add_chunks_eq_bv_add
    (row : BinaryAddRow FGL)
    (h_spec : Spec row)
    (h_range : RangeFacts row) :
    BitVec.ofNat 64 (row.a_0.val + row.a_1.val * 4294967296)
      + BitVec.ofNat 64 (row.b_0.val + row.b_1.val * 4294967296)
      = BitVec.ofNat 64
          (row.c_chunks_0.val
            + row.c_chunks_1.val * 65536
            + row.c_chunks_2.val * 4294967296
            + row.c_chunks_3.val * 281474976710656) := by
  simp only [Spec, cPacked, packed32, Nat.reducePow] at h_spec
  obtain ⟨h_a0, h_a1, h_b0, h_b1, h_c0, h_c1, h_c2, h_c3⟩ := h_range
  have h_av : row.a_0.val + row.a_1.val * 4294967296 < 18446744073709551616 := by omega
  have h_bv : row.b_0.val + row.b_1.val * 4294967296 < 18446744073709551616 := by omega
  have h_cv : row.c_chunks_0.val + row.c_chunks_1.val * 65536
      + row.c_chunks_2.val * 4294967296
      + row.c_chunks_3.val * 281474976710656 < 18446744073709551616 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h_av, Nat.mod_eq_of_lt h_bv, Nat.mod_eq_of_lt h_cv, ← h_spec]
  ring

/-- A component `Spec` packages both the semantic addition equation and all
lookup-derived range bounds required by `binary_add_chunks_eq_bv_add`. -/
theorem binary_add_chunks_eq_bv_add_of_component_spec
    (row : BinaryAddRow FGL) (h : ComponentSpecFacts row) :
    BitVec.ofNat 64 (row.a_0.val + row.a_1.val * 4294967296)
      + BitVec.ofNat 64 (row.b_0.val + row.b_1.val * 4294967296)
      = BitVec.ofNat 64
          (row.c_chunks_0.val
            + row.c_chunks_1.val * 65536
            + row.c_chunks_2.val * 4294967296
            + row.c_chunks_3.val * 281474976710656) := by
  exact binary_add_chunks_eq_bv_add row h.1 h.2.2

end ZiskFv.AirsClean.BinaryAdd
