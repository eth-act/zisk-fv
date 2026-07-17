import ZiskFv.AirsClean.Binary.Circuit
import ZiskFv.Channels.OperationBus

/-!
# Consumer-facing Binary interface

This module is the Clean-row API for Binary consumers.  It contains no
`Valid_Binary` projection.

## Q2 constraint correspondence

| Legacy `core_every_row` predicate | Clean operation in `Binary.main` |
|---|---|
| `boolean_mode32` | `assertZero (mode32 * (1 - mode32))` |
| `boolean_carry_7` | `assertZero (carry_7 * (1 - carry_7))` |
| `boolean_result_is_a` | `assertZero (result_is_a * (1 - result_is_a))` |
| `boolean_use_first_byte` | `assertZero (use_first_byte * (1 - use_first_byte))` |
| `boolean_c_is_signed` | `assertZero (c_is_signed * (1 - c_is_signed))` |
| `b_op_or_sext_def_holds` | `assertZero (b_op_or_sext - (mode32 * (c_is_signed + 512 - b_op) + b_op))` |
| `mode32_and_c_is_signed_def_holds` | `assertZero (mode32_and_c_is_signed - mode32 * c_is_signed)` |

The eight legacy BinaryTable permutation rows correspond, byte for byte, to
`lookupMessage0` through `lookupMessage7` in `mainWithBinaryTable` and to the
eight direct static lookups in `mainWithStaticBinaryTable`.  The operation-bus
row corresponds to `OpBusChannel.push (opBusMessageExpr row)`.  Those nine
interactions were outside legacy `core_every_row`; Clean makes the same split
between `main` and its lookup-aware variants.  There is no constraint
semantic divergence.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open ZiskFv.Channels.OperationBus

@[reducible] def cleanALoValue (row : BinaryRow FGL) : FGL :=
  row.aBytes.free_in_a_0 + 256 * row.aBytes.free_in_a_1
    + 65536 * row.aBytes.free_in_a_2 + 16777216 * row.aBytes.free_in_a_3
@[reducible] def cleanAHiValue (row : BinaryRow FGL) : FGL :=
  row.aBytes.free_in_a_4 + 256 * row.aBytes.free_in_a_5
    + 65536 * row.aBytes.free_in_a_6 + 16777216 * row.aBytes.free_in_a_7
@[reducible] def cleanBLoValue (row : BinaryRow FGL) : FGL :=
  row.bBytes.free_in_b_0 + 256 * row.bBytes.free_in_b_1
    + 65536 * row.bBytes.free_in_b_2 + 16777216 * row.bBytes.free_in_b_3
@[reducible] def cleanBHiValue (row : BinaryRow FGL) : FGL :=
  row.bBytes.free_in_b_4 + 256 * row.bBytes.free_in_b_5
    + 65536 * row.bBytes.free_in_b_6 + 16777216 * row.bBytes.free_in_b_7
@[reducible] def cleanCLoValue (row : BinaryRow FGL) : FGL :=
  row.cBytes.free_in_c_0 + 256 * row.cBytes.free_in_c_1
    + 65536 * row.cBytes.free_in_c_2 + 16777216 * row.cBytes.free_in_c_3
    + row.chain.carry_7
@[reducible] def cleanCHiValue (row : BinaryRow FGL) : FGL :=
  row.cBytes.free_in_c_4 + 256 * row.cBytes.free_in_c_5
    + 65536 * row.cBytes.free_in_c_6 + 16777216 * row.cBytes.free_in_c_7

/-- The concrete operation-bus message emitted by a Clean Binary row. -/
@[reducible] def cleanOpBusMessage (row : BinaryRow FGL) : OpBusMessage FGL :=
  { op := row.chain.b_op + 16 * row.mode.mode32
    a_lo := cleanALoValue row, a_hi := cleanAHiValue row
    b_lo := cleanBLoValue row, b_hi := cleanBHiValue row
    c_lo := cleanCLoValue row, c_hi := cleanCHiValue row
    flag := row.chain.carry_7, main_step := 0, extended_arg := 0, extra_args_0 := 0 }

/-- Evaluation commutes with the Binary operation-bus projection. -/
theorem eval_cleanOpBusMessageExpr
    (env : Environment FGL) (row : Var BinaryRow FGL) :
    eval env (opBusMessageExpr row) = cleanOpBusMessage (eval env row) := by
  rw [OpBusMessage.mk.injEq]
  simp only [opBusMessageExpr, cleanALoValue, cleanAHiValue, cleanBLoValue,
    cleanBHiValue, cleanCLoValue, cleanCHiValue, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
    Expression.eval]
  repeat constructor

/-- Component-specialized operation-bus projection. -/
theorem staticLookupComponent_eval_cleanOpBusMessageExpr (env : Environment FGL) :
    eval env (opBusMessageExpr staticLookupComponent.rowInputVar) =
      cleanOpBusMessage (staticLookupComponent.rowInput env) := by
  rw [eval_cleanOpBusMessageExpr]
  exact congrArg cleanOpBusMessage (by
    simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
      (eval_varFromOffset_valueFromOffset staticLookupComponent.Input 0 env))

end ZiskFv.AirsClean.Binary
