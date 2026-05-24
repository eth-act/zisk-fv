import ZiskFv.AirsClean.Main.Spec
import ZiskFv.Channels.OperationBus
import Clean.Circuit.Basic

/-!
# Main circuit operations

The 9 F-typed per-row constraints of ZisK's Main AIR. Cross-row
pc_handshake stays in Bridge as a separate adjacency theorem.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Circuit (assertZero)
open ZiskFv.Channels.OperationBus (OpBusChannel OpBusMessage)

@[circuit_norm]
def main (row : Var MainRow FGL) : Circuit FGL Unit := do
  assertZero (row.flag * (1 - row.flag))
  assertZero (row.is_external_op * (1 - row.is_external_op))
  assertZero ((1 - row.is_external_op) * (1 - row.op) * row.c_0)
  assertZero ((1 - row.is_external_op) * (1 - row.op) * row.c_1)
  assertZero ((1 - row.is_external_op) * row.op * (row.b_0 - row.c_0))
  assertZero ((1 - row.is_external_op) * row.op * (row.b_1 - row.c_1))
  assertZero ((1 - row.is_external_op) * (1 - row.op) * (1 - row.flag))
  assertZero ((1 - row.is_external_op) * row.op * row.flag)
  assertZero (row.flag * row.set_pc)

/-- Main's operation-bus message, without multiplicity.

The multiplicity is supplied separately by `mainWithOpBus` as
`-row.is_external_op`, matching ZisK's assume-side operation-bus emission. -/
@[reducible]
def opBusMessageExpr (row : Var MainRow FGL) : OpBusMessage (Expression FGL) :=
  { op := row.op
    a_lo := row.a_0
    a_hi := (1 - row.m32) * row.a_1
    b_lo := row.b_0
    b_hi := (1 - row.m32) * row.b_1
    c_lo := row.c_0
    c_hi := row.c_1
    flag := row.flag
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Main constraints plus the operation-bus assume-side emission.

Clean's `pull` has fixed multiplicity `-1`; Main needs the PIL-faithful
row selector, so this uses `emit (-row.is_external_op)` directly. -/
@[circuit_norm]
def mainWithOpBus (row : Var MainRow FGL) : Circuit FGL Unit := do
  main row
  OpBusChannel.emit (-row.is_external_op) (opBusMessageExpr row)

@[reducible] def mainWithOpBusElaborated :
    ElaboratedCircuit FGL MainRow unit where
  main := mainWithOpBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]

end ZiskFv.AirsClean.Main
