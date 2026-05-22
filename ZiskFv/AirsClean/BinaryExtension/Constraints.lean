import ZiskFv.AirsClean.BinaryExtension.Spec
import Clean.Circuit.Basic
import ZiskFv.Channels.OperationBus

/-!
# BinaryExtension circuit operations

BinaryExtension has zero F-typed per-row `assertZero` constraints. It does,
however, push its operation-bus tuple. The table-lookup semantics against
`BinaryExtensionTable` are still represented by the existing table-soundness
boundary and are composed at the Binary-family terminal phase.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- BinaryExtension row's low 32-bit `a` packing. -/
@[reducible]
def aLo (row : Var BinaryExtensionRow FGL) : Expression FGL :=
  row.aCols.free_in_a_0 + 256 * row.aCols.free_in_a_1
    + 65536 * row.aCols.free_in_a_2 + 16777216 * row.aCols.free_in_a_3

/-- BinaryExtension row's high 32-bit `a` packing. -/
@[reducible]
def aHi (row : Var BinaryExtensionRow FGL) : Expression FGL :=
  row.aCols.free_in_a_4 + 256 * row.aCols.free_in_a_5
    + 65536 * row.aCols.free_in_a_6 + 16777216 * row.aCols.free_in_a_7

/-- BinaryExtension operation-bus push. There are no F-only assertions. -/
@[circuit_norm]
def main (row : Var BinaryExtensionRow FGL) : Circuit FGL Unit := do
  let alo := aLo row
  let ahi := aHi row
  OpBusChannel.push
    { op := row.flags.op
      a_lo := row.flags.op_is_shift * (alo - row.flags.b_0) + row.flags.b_0
      a_hi := row.flags.op_is_shift * (ahi - row.flags.b_1) + row.flags.b_1
      b_lo :=
        row.flags.op_is_shift * (row.flags.free_in_b + 256 * row.flags.b_0 - alo)
          + alo
      b_hi := row.flags.op_is_shift * (row.flags.b_1 - ahi) + ahi
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

/-- Elaborated BinaryExtension circuit: no local witnesses, one
    operation-bus push. -/
@[reducible] def binaryExtensionElaborated :
    ElaboratedCircuit FGL BinaryExtensionRow unit where
  name := "BinaryExtension"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]

end ZiskFv.AirsClean.BinaryExtension
