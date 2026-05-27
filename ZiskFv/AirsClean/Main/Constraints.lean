import ZiskFv.AirsClean.Main.Spec
import ZiskFv.AirsClean.ZiskInstructionRom
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.ZiskRomBus
import Clean.Circuit.Basic
import Clean.Circuit.Lookup

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
  exposedChannels row _ :=
    expose OpBusChannel [OpBusChannel.emitted (-row.is_external_op) (opBusMessageExpr row)]
  channelsLawful := by
    simp only [circuit_norm, mainWithOpBus, main, opBusMessageExpr, OpBusChannel]

/-! ## T4.0 — ROM lookup extension

`mainWithRom` extends the per-row Main circuit with:

1. The 14 boolean assertions on `rom_flags` components not already
   constrained by `main` (which only handles `is_external_op` and
   `flag` itself). The remaining 14 booleans (3 from `MainRow.core` —
   `m32`, `set_pc`, `store_pc` — and 11 from `MainRow.rom`) are pinned
   here.

2. The PIL-faithful ZisK instruction ROM lookup at
   `main.pil:490-491`, emitting the 11-slot
   `[pc, a_offset_imm0, a_imm1, b_offset_imm0, b_imm1, ind_width, op,
   store_offset, jmp_offset1, jmp_offset2, rom_flags]` tuple against
   the program-parameterised `romStaticTable`.

The `rom_flags` slot is computed inline from the 15 boolean witnesses
per the PIL packing equation at `main.pil:483-486`. -/

open ZiskFv.Channels.ZiskRomBus (ZiskRomBusChannel ZiskRomMessage)
open ZiskFv.AirsClean.ZiskInstructionRom (Program romStaticTable)

/-- The packed `rom_flags` expression, per `main.pil:483-486`:
    `rom_flags = 1 + 2*a_src_imm + 4*a_src_mem + 8*is_precompiled
              + 16*b_src_imm + 32*b_src_mem + 64*is_external_op
              + 128*store_pc + 256*store_mem + 512*store_ind
              + 1024*set_pc + 2048*m32 + 4096*b_src_ind
              + 8192*a_src_reg + 16384*b_src_reg + 32768*store_reg` -/
@[reducible]
def romFlagsExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  1
  + 2 * row.rom.a_src_imm
  + 4 * row.rom.a_src_mem
  + 8 * row.rom.is_precompiled
  + 16 * row.rom.b_src_imm
  + 32 * row.rom.b_src_mem
  + 64 * row.core.is_external_op
  + 128 * row.core.store_pc
  + 256 * row.rom.store_mem
  + 512 * row.rom.store_ind
  + 1024 * row.core.set_pc
  + 2048 * row.core.m32
  + 4096 * row.rom.b_src_ind
  + 8192 * row.rom.a_src_reg
  + 16384 * row.rom.b_src_reg
  + 32768 * row.rom.store_reg

/-- Main's per-row ROM lookup tuple, as the typed `ZiskRomMessage`. -/
@[reducible]
def romMessageExpr (row : Var MainRowWithRom FGL) :
    ZiskRomMessage (Expression FGL) :=
  { line := row.core.pc
    a_offset_imm0 := row.rom.a_offset_imm0
    a_imm1 := row.rom.a_imm1
    b_offset_imm0 := row.rom.b_offset_imm0
    b_imm1 := row.rom.b_imm1
    ind_width := row.core.ind_width
    op := row.core.op
    store_offset := row.rom.store_offset
    jmp_offset1 := row.core.jmp_offset1
    jmp_offset2 := row.core.jmp_offset2
    flags := romFlagsExpr row }

/-- Main constraints + ROM-flag booleanity + instruction ROM lookup.

The 14 boolean assertions are split between `MainRow.core` and
`MainRow.rom` per the split-row layout (see `Row.lean`). The ROM
lookup pushes the 11-slot `ZiskRomMessage` against the program-
parameterised `romStaticTable`. -/
@[circuit_norm]
def mainWithRom (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) : Circuit FGL Unit := do
  main row.core
  -- 14 boolean assertions on `rom_flags` components.
  -- 3 in `MainRow.core`:
  assertZero (row.core.m32 * (1 - row.core.m32))
  assertZero (row.core.set_pc * (1 - row.core.set_pc))
  assertZero (row.core.store_pc * (1 - row.core.store_pc))
  -- 11 in `MainRow.rom`:
  assertZero (row.rom.a_src_imm * (1 - row.rom.a_src_imm))
  assertZero (row.rom.a_src_mem * (1 - row.rom.a_src_mem))
  assertZero (row.rom.is_precompiled * (1 - row.rom.is_precompiled))
  assertZero (row.rom.b_src_imm * (1 - row.rom.b_src_imm))
  assertZero (row.rom.b_src_mem * (1 - row.rom.b_src_mem))
  assertZero (row.rom.store_mem * (1 - row.rom.store_mem))
  assertZero (row.rom.store_ind * (1 - row.rom.store_ind))
  assertZero (row.rom.b_src_ind * (1 - row.rom.b_src_ind))
  assertZero (row.rom.a_src_reg * (1 - row.rom.a_src_reg))
  assertZero (row.rom.b_src_reg * (1 - row.rom.b_src_reg))
  assertZero (row.rom.store_reg * (1 - row.rom.store_reg))
  -- ROM lookup.
  lookup (Table.fromStatic (romStaticTable length program)) (romMessageExpr row)

/-- Elaborated `mainWithRom` circuit, ready for use in a Clean
    `Component` / `Ensemble`. Mirrors `mainWithOpBusElaborated`'s
    structure but on `MainRowWithRom` and with the ROM lookup wired
    via the static-table `Table.fromStatic` consumer path. -/
@[reducible] def mainWithRomElaborated (length : ℕ) (program : Program length) :
    ElaboratedCircuit FGL MainRowWithRom unit where
  main := mainWithRom length program
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := []
  exposedChannels _ _ := []
  channelsLawful := by
    simp only [circuit_norm, mainWithRom, main, romMessageExpr,
      romFlagsExpr, romStaticTable]

end ZiskFv.AirsClean.Main
