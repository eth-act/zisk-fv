import ZiskFv.AirsClean.BinaryExtension.Circuit
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Channels.OperationBus

/-!
# `Valid_BinaryExtension` ↔ `BinaryExtensionRow` compatibility

Post-D3 Bridge: all 30 columns reached via named accessors on
`Valid_BinaryExtension FGL FGL`. No `Circuit.main`/`v.circuit` left.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open ZiskFv.Channels.OperationBus

@[reducible]
def rowAt (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ) :
    BinaryExtensionRow FGL where
  aCols := {
    free_in_a_0 := v.free_in_a_0 r
    free_in_a_1 := v.free_in_a_1 r
    free_in_a_2 := v.free_in_a_2 r
    free_in_a_3 := v.free_in_a_3 r
    free_in_a_4 := v.free_in_a_4 r
    free_in_a_5 := v.free_in_a_5 r
    free_in_a_6 := v.free_in_a_6 r
    free_in_a_7 := v.free_in_a_7 r
  }
  cColsLo := {
    free_in_c_0 := v.free_in_c_0 r
    free_in_c_1 := v.free_in_c_1 r
    free_in_c_2 := v.free_in_c_2 r
    free_in_c_3 := v.free_in_c_3 r
    free_in_c_4 := v.free_in_c_4 r
    free_in_c_5 := v.free_in_c_5 r
    free_in_c_6 := v.free_in_c_6 r
    free_in_c_7 := v.free_in_c_7 r
  }
  cColsHi := {
    free_in_c_8 := v.free_in_c_8 r
    free_in_c_9 := v.free_in_c_9 r
    free_in_c_10 := v.free_in_c_10 r
    free_in_c_11 := v.free_in_c_11 r
    free_in_c_12 := v.free_in_c_12 r
    free_in_c_13 := v.free_in_c_13 r
    free_in_c_14 := v.free_in_c_14 r
    free_in_c_15 := v.free_in_c_15 r
  }
  flags := {
    op := v.op r
    free_in_b := v.free_in_b r
    op_is_shift := v.op_is_shift r
    b_0 := v.b_0 r
    b_1 := v.b_1 r
  }

/-- BinaryExtension has zero F-typed per-row constraints. -/
def constraints_at
    (_v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (_r : ℕ) :
    Prop := True

/-!
## Operation-bus bridge

The Clean component emits an `OpBusMessage`; the pre-Clean equivalence layer
still consumes `OperationBusEntry`. These definitions and theorems are the
provider-side bridge C7 will use when replacing the consolidated
operation-bus permutation axiom with Clean channel balancing.
-/

@[reducible]
def aLoValue (row : BinaryExtensionRow FGL) : FGL :=
  row.aCols.free_in_a_0 + 256 * row.aCols.free_in_a_1
    + 65536 * row.aCols.free_in_a_2 + 16777216 * row.aCols.free_in_a_3

@[reducible]
def aHiValue (row : BinaryExtensionRow FGL) : FGL :=
  row.aCols.free_in_a_4 + 256 * row.aCols.free_in_a_5
    + 65536 * row.aCols.free_in_a_6 + 16777216 * row.aCols.free_in_a_7

@[reducible]
def opBusMessage (row : BinaryExtensionRow FGL) : OpBusMessage FGL :=
  { op := row.flags.op
    a_lo := row.flags.op_is_shift * (aLoValue row - row.flags.b_0) + row.flags.b_0
    a_hi := row.flags.op_is_shift * (aHiValue row - row.flags.b_1) + row.flags.b_1
    b_lo :=
      row.flags.op_is_shift * (row.flags.free_in_b + 256 * row.flags.b_0 - aLoValue row)
        + aLoValue row
    b_hi := row.flags.op_is_shift * (row.flags.b_1 - aHiValue row) + aHiValue row
    c_lo :=
      row.cColsLo.free_in_c_0 + row.cColsLo.free_in_c_2
        + row.cColsLo.free_in_c_4 + row.cColsLo.free_in_c_6
        + row.cColsHi.free_in_c_8 + row.cColsHi.free_in_c_10
        + row.cColsHi.free_in_c_12 + row.cColsHi.free_in_c_14
    c_hi :=
      row.cColsLo.free_in_c_1 + row.cColsLo.free_in_c_3
        + row.cColsLo.free_in_c_5 + row.cColsLo.free_in_c_7
        + row.cColsHi.free_in_c_9 + row.cColsHi.free_in_c_11
        + row.cColsHi.free_in_c_13 + row.cColsHi.free_in_c_15
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

theorem opBusMessage_toEntry_rowAt_eq_opBus_row
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ) :
    OpBusMessage.toEntry (opBusMessage (rowAt v r)) 1 =
      ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension v r := by
  rfl

theorem spec_of_valid
    (v : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL) (r : ℕ)
    (_h_assumptions : Assumptions (rowAt v r))
    (_h_constraints : constraints_at v r) :
    Spec (rowAt v r) :=
  spec_via_component (rowAt v r)

end ZiskFv.AirsClean.BinaryExtension
