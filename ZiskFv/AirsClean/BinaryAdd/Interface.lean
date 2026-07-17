import ZiskFv.AirsClean.BinaryAdd.Circuit
import ZiskFv.Channels.OperationBus

/-!
# Consumer-facing BinaryAdd interface

This module contains the row-local API consumed by the equivalence and
compliance layers.  It is stated entirely in terms of the Clean row and
`GeneralFormalCircuit.Spec`; no legacy named-column validator is involved.
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
