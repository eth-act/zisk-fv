import ZiskFv.AirsClean.ArithDiv.Spec
import ZiskFv.AirsClean.ArithTable
import ZiskFv.AirsClean.RangeTables
import Clean.Circuit.Basic
import ZiskFv.Channels.OperationBus

/-!
# ArithDiv circuit operations (the `main` field of the Component)

The 11 DIV carry-chain constraints of the Arith AIR, expressed as a
Clean circuit do-block — one `assertZero` per F-only constraint:

  * 3 sign-product witness pins (constraints 6, 7, 8 —
    arith.pil:58-60): `fab`, `na_fb`, `nb_fa`.
  * 8 chunk-level carry equations (constraints 31-38 —
    arith.pil:205-209): the 4-limb packed-product / division
    relation with signed-flag dispatch.

ArithDiv is a pure assertion — no fresh witnesses, no channel
interaction (the Arith op-bus is a shared channel wired family-
terminal, plan phase C7/CZ). The DIV carry-chain sub-circuit has no
range-lookup or ROM interaction of its own.

**Scope note.** The 9 AIR-global flag-booleanity `assertZero`s
(`na/nb/...` boolean) are *not* emitted here: per `Spec.lean`'s scope
note, they belong to the Arith AIR's flag-validation sub-circuit, on
which the DIV carry-chain relation is independent — the per-opcode DIV
verification pins flag *values* through `arith_table` axioms, never the
boolean `assertZero`s. This `main` renders the DIV carry-chain
sub-circuit faithfully (the curated constraint subset the verification
consumes).

## Trust note

No axioms. Pure operational declaration.
-/

namespace ZiskFv.AirsClean.ArithDiv

open Goldilocks
open Circuit (assertZero lookup)
open ZiskFv.AirsClean.RangeTables
open ZiskFv.Channels.OperationBus (OpBusChannel OpBusMessage)

/-- The 11 DIV carry-chain F-constraints, taking the row's slot values
    as `Expression FGL`s. Returns `Unit` (ArithDiv is a pure assertion —
    no fresh witnesses introduced inside the circuit). -/
@[circuit_norm]
def main (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  -- 3 sign-product witness pins (constraints 6, 7, 8 — arith.pil:58-60).
  assertZero (row.aux.fab
              - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
                  + 4 * row.flags.na * row.flags.nb))
  assertZero (row.aux.na_fb - row.flags.na * (1 - 2 * row.flags.nb))
  assertZero (row.aux.nb_fa - row.flags.nb * (1 - 2 * row.flags.na))
  -- 8 chunk equations (constraints 31-38 — arith.pil:205-209).
  -- 31: (eq[0]) - carry[0] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_0 * row.chunks.b_0
              - row.chunks.c_0
              + 2 * row.flags.np * row.chunks.c_0
              + row.flags.div * row.chunks.d_0
              - 2 * row.flags.nr * row.chunks.d_0
              - row.aux.carry_0 * 65536)
  -- 32: (eq[1]) + carry[0] - carry[1] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_1 * row.chunks.b_0
              + row.aux.fab * row.chunks.a_0 * row.chunks.b_1
              - row.chunks.c_1
              + 2 * row.flags.np * row.chunks.c_1
              + row.flags.div * row.chunks.d_1
              - 2 * row.flags.nr * row.chunks.d_1
              + row.aux.carry_0
              - row.aux.carry_1 * 65536)
  -- 33: (eq[2]) + carry[1] - carry[2] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_2 * row.chunks.b_0
              + row.aux.fab * row.chunks.a_1 * row.chunks.b_1
              + row.aux.fab * row.chunks.a_0 * row.chunks.b_2
              + row.chunks.a_0 * row.aux.nb_fa * row.flags.m32
              + row.chunks.b_0 * row.aux.na_fb * row.flags.m32
              - row.chunks.c_2
              + 2 * row.flags.np * row.chunks.c_2
              + row.flags.div * row.chunks.d_2
              - 2 * row.flags.nr * row.chunks.d_2
              - row.flags.np * row.flags.div * row.flags.m32
              + row.flags.nr * row.flags.m32
              + row.aux.carry_1
              - row.aux.carry_2 * 65536)
  -- 34: (eq[3]) + carry[2] - carry[3] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_0
              + row.aux.fab * row.chunks.a_2 * row.chunks.b_1
              + row.aux.fab * row.chunks.a_1 * row.chunks.b_2
              + row.aux.fab * row.chunks.a_0 * row.chunks.b_3
              + row.chunks.a_1 * row.aux.nb_fa * row.flags.m32
              + row.chunks.b_1 * row.aux.na_fb * row.flags.m32
              - row.chunks.c_3
              + 2 * row.flags.np * row.chunks.c_3
              + row.flags.div * row.chunks.d_3
              - 2 * row.flags.nr * row.chunks.d_3
              + row.aux.carry_2
              - row.aux.carry_3 * 65536)
  -- 35: (eq[4]) + carry[3] - carry[4] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_1
              + row.aux.fab * row.chunks.a_2 * row.chunks.b_2
              + row.aux.fab * row.chunks.a_1 * row.chunks.b_3
              + row.flags.na * row.flags.nb * row.flags.m32
              + row.chunks.b_0 * row.aux.na_fb * (1 - row.flags.m32)
              + row.chunks.a_0 * row.aux.nb_fa * (1 - row.flags.m32)
              - row.flags.np * row.flags.m32 * (1 - row.flags.div)
              - row.flags.np * (1 - row.flags.m32) * row.flags.div
              + row.flags.nr * (1 - row.flags.m32)
              - row.chunks.d_0 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_0 * (1 - row.flags.div)
              + row.aux.carry_3
              - row.aux.carry_4 * 65536)
  -- 36: (eq[5]) + carry[4] - carry[5] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_2
              + row.aux.fab * row.chunks.a_2 * row.chunks.b_3
              + row.chunks.a_1 * row.aux.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_1 * row.aux.na_fb * (1 - row.flags.m32)
              - row.chunks.d_1 * (1 - row.flags.div)
              + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
              + row.aux.carry_4
              - row.aux.carry_5 * 65536)
  -- 37: (eq[6]) + carry[5] - carry[6] * 65536 = 0
  assertZero (row.aux.fab * row.chunks.a_3 * row.chunks.b_3
              + row.chunks.a_2 * row.aux.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_2 * row.aux.na_fb * (1 - row.flags.m32)
              - row.chunks.d_2 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
              + row.aux.carry_5
              - row.aux.carry_6 * 65536)
  -- 38: (eq[7]) + carry[6] = 0
  assertZero (65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
              + row.chunks.a_3 * row.aux.nb_fa * (1 - row.flags.m32)
              + row.chunks.b_3 * row.aux.na_fb * (1 - row.flags.m32)
              - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
              - row.chunks.d_3 * (1 - row.flags.div)
              + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
              + row.aux.carry_6)

/-! ## Operation-bus variants

The original `main` above intentionally stayed as the carry-chain-only
component while C4 was being staged. T5 needs the same row to provide the
operation-bus provider interaction, so the op-bus emission is layered as
separate variants rather than changing the existing component in place.
-/

/-- Primary DIV/DIVU op-bus message: quotient result in the `a[]` chunks. -/
@[reducible]
def primaryOpBusMessageExpr (row : Var ArithDivRow FGL) :
    OpBusMessage (Expression FGL) :=
  { op := row.flags.op
    a_lo := row.chunks.c_0 + row.chunks.c_1 * 65536
    a_hi := row.chunks.c_2 + row.chunks.c_3 * 65536
    b_lo := row.chunks.b_0 + row.chunks.b_1 * 65536
    b_hi := row.chunks.b_2 + row.chunks.b_3 * 65536
    c_lo := row.chunks.a_0 + row.chunks.a_1 * 65536
    c_hi := row.flags.bus_res1
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

/-- Secondary REM/REMU op-bus message: remainder result in the `d[]` chunks. -/
@[reducible]
def secondaryOpBusMessageExpr (row : Var ArithDivRow FGL) :
    OpBusMessage (Expression FGL) :=
  { op := row.flags.op
    a_lo := row.chunks.c_0 + row.chunks.c_1 * 65536
    a_hi := row.chunks.c_2 + row.chunks.c_3 * 65536
    b_lo := row.chunks.b_0 + row.chunks.b_1 * 65536
    b_hi := row.chunks.b_2 + row.chunks.b_3 * 65536
    c_lo := row.chunks.d_0 + row.chunks.d_1 * 65536
    c_hi := row.flags.bus_res1
    flag := 0
    main_step := 0
    extended_arg := 0
    extra_args_0 := 0 }

@[circuit_norm]
def mainWithPrimaryOpBus (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  main row
  OpBusChannel.push (primaryOpBusMessageExpr row)

@[circuit_norm]
def mainWithSecondaryOpBus (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  main row
  OpBusChannel.push (secondaryOpBusMessageExpr row)

@[circuit_norm]
def mainWithPrimaryOpBusAndArithTable (row : Var ArithDivRow FGL) :
    Circuit FGL Unit := do
  mainWithPrimaryOpBus row
  lookup (Table.fromStatic ArithTable.arithTable) (arithTableRow row)
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 26, row.chunks.a_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 9, row.chunks.b_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 26, row.chunks.c_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 9, row.chunks.d_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab, row.chunks.a_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 17, row.chunks.b_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd, row.chunks.c_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 17, row.chunks.d_3]

@[circuit_norm]
def mainWithSecondaryOpBusAndArithTable (row : Var ArithDivRow FGL) :
    Circuit FGL Unit := do
  mainWithSecondaryOpBus row
  lookup (Table.fromStatic ArithTable.arithTable) (arithTableRow row)
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 26, row.chunks.a_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 9, row.chunks.b_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 26, row.chunks.c_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 9, row.chunks.d_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab, row.chunks.a_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 17, row.chunks.b_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd, row.chunks.c_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 17, row.chunks.d_3]

/-- Lookup-aware ArithDiv circuit path. This appends the full 15-column
    `arith_table_assumes` ROM lookup after the existing carry-chain
    component body. The current load-bearing carry-chain component remains
    unchanged until Compliance supplies this lookup evidence globally. -/
@[circuit_norm]
def mainWithArithTable (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  main row
  lookup (Table.fromStatic ArithTable.arithTable) (arithTableRow row)
  -- Eight indexed `arith_range_table_assumes(range_*, chunk)` lookups
  -- (`arith.pil:299-306`), in upstream PIL order.
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 26, row.chunks.a_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 9, row.chunks.b_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 26, row.chunks.c_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 9, row.chunks.d_1]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab, row.chunks.a_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_ab + 17, row.chunks.b_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd, row.chunks.c_3]
  lookup (Table.fromStatic arithRangeTable) #v[row.flags.range_cd + 17, row.chunks.d_3]

/-- Lookup-aware ArithDiv path for the sixteen `bits(16)` chunk columns.
    This is the Div-family counterpart of ArithMul's chunk range view. -/
@[circuit_norm]
def mainWithChunkRanges (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  main row
  lookup (Table.fromStatic rangeTable16) row.chunks.a_0
  lookup (Table.fromStatic rangeTable16) row.chunks.a_1
  lookup (Table.fromStatic rangeTable16) row.chunks.a_2
  lookup (Table.fromStatic rangeTable16) row.chunks.a_3
  lookup (Table.fromStatic rangeTable16) row.chunks.b_0
  lookup (Table.fromStatic rangeTable16) row.chunks.b_1
  lookup (Table.fromStatic rangeTable16) row.chunks.b_2
  lookup (Table.fromStatic rangeTable16) row.chunks.b_3
  lookup (Table.fromStatic rangeTable16) row.chunks.c_0
  lookup (Table.fromStatic rangeTable16) row.chunks.c_1
  lookup (Table.fromStatic rangeTable16) row.chunks.c_2
  lookup (Table.fromStatic rangeTable16) row.chunks.c_3
  lookup (Table.fromStatic rangeTable16) row.chunks.d_0
  lookup (Table.fromStatic rangeTable16) row.chunks.d_1
  lookup (Table.fromStatic rangeTable16) row.chunks.d_2
  lookup (Table.fromStatic rangeTable16) row.chunks.d_3

/-- Lookup-aware ArithDiv path for unsigned carry `bits(17)` checks. -/
@[circuit_norm]
def mainWithUnsignedCarryRanges (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  main row
  lookup (Table.fromStatic rangeTable17) row.aux.carry_0
  lookup (Table.fromStatic rangeTable17) row.aux.carry_1
  lookup (Table.fromStatic rangeTable17) row.aux.carry_2
  lookup (Table.fromStatic rangeTable17) row.aux.carry_3
  lookup (Table.fromStatic rangeTable17) row.aux.carry_4
  lookup (Table.fromStatic rangeTable17) row.aux.carry_5
  lookup (Table.fromStatic rangeTable17) row.aux.carry_6

/-- Lookup-aware ArithDiv path for signed/W carry range checks. -/
@[circuit_norm]
def mainWithSignedCarryRanges (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  main row
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_0
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_1
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_2
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_3
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_4
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_5
  lookup (Table.fromStatic signedCarryRangeTable) row.aux.carry_6

/-- Lookup-aware elaboration for the next C3/C4 stage. It is intentionally
    separate from `arithDivElaborated` so existing carry-chain consumers do
    not acquire a new caller-supplied lookup promise before Compliance has
    a global source for it. -/
@[reducible] def arithDivWithArithTableElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivWithArithTable"
  main := mainWithArithTable
  localLength _ := 0
  output _ _ := ()

@[reducible] def arithDivWithChunkRangesElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivWithChunkRanges"
  main := mainWithChunkRanges
  localLength _ := 0
  output _ _ := ()

@[reducible] def arithDivWithUnsignedCarryRangesElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivWithUnsignedCarryRanges"
  main := mainWithUnsignedCarryRanges
  localLength _ := 0
  output _ _ := ()

@[reducible] def arithDivWithSignedCarryRangesElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivWithSignedCarryRanges"
  main := mainWithSignedCarryRanges
  localLength _ := 0
  output _ _ := ()

@[reducible] def arithDivPrimaryOpBusElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivPrimaryOpBus"
  main := mainWithPrimaryOpBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels row _ :=
    expose OpBusChannel [OpBusChannel.pushed (primaryOpBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, mainWithPrimaryOpBus, main, primaryOpBusMessageExpr,
      OpBusChannel]

@[reducible] def arithDivSecondaryOpBusElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivSecondaryOpBus"
  main := mainWithSecondaryOpBus
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels row _ :=
    expose OpBusChannel [OpBusChannel.pushed (secondaryOpBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, mainWithSecondaryOpBus, main, secondaryOpBusMessageExpr,
      OpBusChannel]

@[reducible] def arithDivPrimaryOpBusWithArithTableElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivPrimaryOpBusWithArithTable"
  main := mainWithPrimaryOpBusAndArithTable
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels row _ :=
    expose OpBusChannel [OpBusChannel.pushed (primaryOpBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, mainWithPrimaryOpBusAndArithTable,
      mainWithPrimaryOpBus, main, primaryOpBusMessageExpr, OpBusChannel]

@[reducible] def arithDivSecondaryOpBusWithArithTableElaborated :
    ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDivSecondaryOpBusWithArithTable"
  main := mainWithSecondaryOpBusAndArithTable
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [OpBusChannel.toRaw]
  exposedChannels row _ :=
    expose OpBusChannel [OpBusChannel.pushed (secondaryOpBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, mainWithSecondaryOpBusAndArithTable,
      mainWithSecondaryOpBus, main, secondaryOpBusMessageExpr, OpBusChannel]

/-- The elaborated circuit for ArithDiv's `main` — 11 `assertZero`
    constraints, no fresh witnesses (`localLength = 0`, `unit` output)
    and no channel interactions. Lives here (next to `main`) so the
    `Circuit.lean` wrapper can reuse it without an import cycle. -/
@[reducible] def arithDivElaborated : ElaboratedCircuit FGL ArithDivRow unit where
  name := "ArithDiv"
  main := main
  localLength _ := 0
  output _ _ := ()

end ZiskFv.AirsClean.ArithDiv
