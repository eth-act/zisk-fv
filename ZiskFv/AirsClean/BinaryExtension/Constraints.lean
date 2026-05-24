import ZiskFv.AirsClean.BinaryExtension.Spec
import Clean.Circuit.Basic
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.BinaryExtensionTable
import ZiskFv.AirsClean.BinaryExtensionTable

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
open Circuit (lookup)
open ZiskFv.Channels.OperationBus (OpBusChannel OpBusMessage)
open ZiskFv.Channels.BinaryExtensionTable (BinaryExtensionTableChannel)

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

@[reducible]
def opBusMessageExpr (row : Var BinaryExtensionRow FGL) :
    OpBusMessage (Expression FGL) :=
  let alo := aLo row
  let ahi := aHi row
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

/-- BinaryExtension operation-bus push. There are no F-only assertions. -/
@[circuit_norm]
def main (row : Var BinaryExtensionRow FGL) : Circuit FGL Unit := do
  OpBusChannel.push (opBusMessageExpr row)

/-- Elaborated BinaryExtension circuit: no local witnesses, one
    operation-bus push. -/
@[reducible] def binaryExtensionElaborated :
    ElaboratedCircuit FGL BinaryExtensionRow unit where
  name := "BinaryExtension"
  main := main
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels row _ :=
    expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, main, opBusMessageExpr, aLo, aHi, OpBusChannel]

/-- Lookup-aware BinaryExtension circuit path. This appends the eight
    per-byte BinaryExtensionTable pulls after the existing op-bus push. It
    is intentionally separate from `binaryExtensionElaborated`: the current
    load-bearing C5 bridge keeps using the op-bus component until C7 supplies
    the balanced BinaryExtensionTable provider side. -/
@[circuit_norm]
def mainWithBinaryExtensionTable (row : Var BinaryExtensionRow FGL) :
    Circuit FGL Unit := do
  main row
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 0
      a_byte := row.aCols.free_in_a_0
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_0
      c_hi_byte := row.cColsLo.free_in_c_1
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 1
      a_byte := row.aCols.free_in_a_1
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_2
      c_hi_byte := row.cColsLo.free_in_c_3
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 2
      a_byte := row.aCols.free_in_a_2
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_4
      c_hi_byte := row.cColsLo.free_in_c_5
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 3
      a_byte := row.aCols.free_in_a_3
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_6
      c_hi_byte := row.cColsLo.free_in_c_7
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 4
      a_byte := row.aCols.free_in_a_4
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_8
      c_hi_byte := row.cColsHi.free_in_c_9
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 5
      a_byte := row.aCols.free_in_a_5
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_10
      c_hi_byte := row.cColsHi.free_in_c_11
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 6
      a_byte := row.aCols.free_in_a_6
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_12
      c_hi_byte := row.cColsHi.free_in_c_13
      op_is_shift := row.flags.op_is_shift }
  BinaryExtensionTableChannel.pull
    { op := row.flags.op
      byte_index := 7
      a_byte := row.aCols.free_in_a_7
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_14
      c_hi_byte := row.cColsHi.free_in_c_15
      op_is_shift := row.flags.op_is_shift }

@[reducible] def binaryExtensionWithTableElaborated :
    ElaboratedCircuit FGL BinaryExtensionRow unit where
  name := "BinaryExtensionWithTable"
  main := mainWithBinaryExtensionTable
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]
  channelsWithGuarantees := [BinaryExtensionTableChannel.toRaw]

/-- Static-provider lookup-aware BinaryExtension circuit path. This is the
    same eight BinaryExtensionTable rows as `mainWithBinaryExtensionTable`,
    but expressed as direct Clean lookups against
    `AirsClean.BinaryExtensionTable.binaryExtensionTable`.

    Soundness of this circuit yields exact decoded-row membership in the
    static provider. Retiring `bin_ext_table_consumer_wf` still requires
    projecting that membership to the semantic `wf_properties` clauses and
    threading the result into the opcode proofs. -/
@[circuit_norm]
def mainWithStaticBinaryExtensionTable (row : Var BinaryExtensionRow FGL) :
    Circuit FGL Unit := do
  main row
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 0
      a_byte := row.aCols.free_in_a_0
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_0
      c_hi_byte := row.cColsLo.free_in_c_1
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 1
      a_byte := row.aCols.free_in_a_1
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_2
      c_hi_byte := row.cColsLo.free_in_c_3
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 2
      a_byte := row.aCols.free_in_a_2
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_4
      c_hi_byte := row.cColsLo.free_in_c_5
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 3
      a_byte := row.aCols.free_in_a_3
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsLo.free_in_c_6
      c_hi_byte := row.cColsLo.free_in_c_7
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 4
      a_byte := row.aCols.free_in_a_4
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_8
      c_hi_byte := row.cColsHi.free_in_c_9
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 5
      a_byte := row.aCols.free_in_a_5
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_10
      c_hi_byte := row.cColsHi.free_in_c_11
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 6
      a_byte := row.aCols.free_in_a_6
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_12
      c_hi_byte := row.cColsHi.free_in_c_13
      op_is_shift := row.flags.op_is_shift }
  lookup (Table.fromStatic ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable)
    { op := row.flags.op
      byte_index := 7
      a_byte := row.aCols.free_in_a_7
      shift_amount := row.flags.free_in_b
      c_lo_byte := row.cColsHi.free_in_c_14
      c_hi_byte := row.cColsHi.free_in_c_15
      op_is_shift := row.flags.op_is_shift }

@[reducible] def binaryExtensionWithStaticTableElaborated :
    ElaboratedCircuit FGL BinaryExtensionRow unit where
  name := "BinaryExtensionWithStaticTable"
  main := mainWithStaticBinaryExtensionTable
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]

end ZiskFv.AirsClean.BinaryExtension
