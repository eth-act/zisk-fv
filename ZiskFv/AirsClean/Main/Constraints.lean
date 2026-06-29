import ZiskFv.AirsClean.Main.Spec
import ZiskFv.AirsClean.ZiskInstructionRom
import ZiskFv.Channels.OperationBus
import ZiskFv.Channels.MemoryBus
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

3. The non-SP address-placement constraints at `main.pil:188-197`:
   `addr0 = a_offset_imm0`,
   `addr1 === b_offset_imm0 + b_src_ind * a[0]`,
   `addr2 = store_offset + store_ind * a[0]`, and
   `(store_ind + b_src_ind) * a[1] === 0`.

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

/-- Concrete counterpart of `romFlagsExpr`. Useful for future honest-prover
    completeness work, but not part of the current soundness-only endpoint. -/
@[reducible]
def romFlags (row : MainRowWithRom FGL) : FGL :=
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

/-- Concrete counterpart of `romMessageExpr`. -/
@[reducible]
def romMessage (row : MainRowWithRom FGL) :
    ZiskRomMessage FGL :=
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
    flags := romFlags row }

theorem eval_romFlagsExpr (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    eval env (romFlagsExpr row) = romFlags (eval env row) := by
  simp only [romFlagsExpr, romFlags, ProvableStruct.eval_eq_eval,
    ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field, circuit_norm]

theorem eval_romMessageExpr (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
  eval env (romMessageExpr row) = romMessage (eval env row) := by
  rw [ZiskRomMessage.mk.injEq]
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, circuit_norm]

theorem eval_aSourceSumExpr (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    env (row.rom.a_src_mem + row.rom.a_src_reg) =
      (eval env row).rom.a_src_mem + (eval env row).rom.a_src_reg := by
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, circuit_norm]

theorem eval_bSourceSumExpr (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    env (row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg) =
      (eval env row).rom.b_src_mem + (eval env row).rom.b_src_ind
        + (eval env row).rom.b_src_reg := by
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, circuit_norm]

theorem eval_cSourceSumExpr (env : Environment FGL)
    (row : Var MainRowWithRom FGL) :
    env (row.rom.store_mem + row.rom.store_ind + row.rom.store_reg) =
      (eval env row).rom.store_mem + (eval env row).rom.store_ind
        + (eval env row).rom.store_reg := by
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, circuit_norm]

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
  -- Non-SP address-placement equations from `main.pil:188-197`.
  assertZero (row.rom.addr0 - row.rom.a_offset_imm0)
  assertZero (row.rom.addr1 - (row.rom.b_offset_imm0 + row.rom.b_src_ind * row.core.a_0))
  assertZero (row.rom.addr2 - (row.rom.store_offset + row.rom.store_ind * row.core.a_0))
  assertZero ((row.rom.store_ind + row.rom.b_src_ind) * row.core.a_1)
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

/-! ## T4.0.6 — memory-bus emission extension

`mainWithMemBus` extends `mainWithRom` with the 3 per-row memory-bus
consumer emissions matching `main.pil:284,300,323`:

1. **a-side** (`main.pil:284-288`) — register read of rs1 (`a_src_reg`)
   or memory read at `addr0` (`a_src_mem`).
2. **b-side** (`main.pil:300-305`) — register read of rs2 (`b_src_reg`)
   or memory access at `addr1` (`b_src_mem + b_src_ind`).
3. **c-side / store** (`main.pil:323-328`) — register write to rd
   (`store_reg`) or memory write at `addr2` (`store_mem + store_ind`).

Each `mem_op` PIL macro lowers to a `permutation_assumes(MEMORY_ID,
[mem_op, addr, mem_step, bytes, value_0, value_1], sel: …)` push.
Modelled here as a `MemBusChannel.emit` with multiplicity `-sel`
(consumer side) using the unified 6-slot PIL `MemBusMessage`.

Memory operation codes (`mem.pil:71-73`):
* `MEMORY_LOAD_OP = 1`
* `MEMORY_STORE_OP = 2`
* `MEMORY_REG_OP = 3`

`mem_step` values per `main.pil:271-273` and the
`main_step_to_mem_step` macro at `main.pil:209-210`:
* `a_mem_step = 1 + main_step * 4 + 0`
* `b_mem_step = 1 + main_step * 4 + 1`
* `store_mem_step = 1 + main_step * 4 + 2` -/

open ZiskFv.Channels.MemoryBus (MemBusChannel MemBusMessage)

/-- `mem_op` literal for the a-side push: `MEMORY_LOAD_OP * a_src_mem +
    MEMORY_REG_OP * a_src_reg = a_src_mem + 3 * a_src_reg`. -/
@[reducible]
def aMemOpExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  row.rom.a_src_mem + 3 * row.rom.a_src_reg

/-- `mem_op` literal for the b-side push: PIL's `MEMORY_LOAD_OP *
    sel_mem_b + MEMORY_REG_OP * b_src_reg` where
    `sel_mem_b = b_src_mem + b_src_ind`. -/
@[reducible]
def bMemOpExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  (row.rom.b_src_mem + row.rom.b_src_ind) + 3 * row.rom.b_src_reg

/-- `mem_op` literal for the c-side push: `MEMORY_STORE_OP *
    (store_mem + store_ind) + MEMORY_REG_OP * store_reg`. -/
@[reducible]
def cMemOpExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  2 * (row.rom.store_mem + row.rom.store_ind) + 3 * row.rom.store_reg

/-- `store_value[0]` per `main.pil:311`:
    `store_pc * (pc + jmp_offset2 - c_0) + c_0`. -/
@[reducible]
def storeValueLoExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  row.core.store_pc * (row.core.pc + row.core.jmp_offset2 - row.core.c_0)
    + row.core.c_0

/-- `store_value[1]` per `main.pil:312`: `(1 - store_pc) * c_1`. -/
@[reducible]
def storeValueHiExpr (row : Var MainRowWithRom FGL) : Expression FGL :=
  (1 - row.core.store_pc) * row.core.c_1

/-- a-side memory-bus consumer message: register read of rs1 (or memory
    read of addr0). `mem_op` carries the PIL operation literal;
    `ptr = addr0`; `width = 8`; `value` is the a-lane pair;
    `timestamp = 1 + main_step * 4`. -/
@[reducible]
def aMemMessageExpr (row : Var MainRowWithRom FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := aMemOpExpr row
    ptr := row.rom.addr0
    timestamp := 1 + row.rom.main_step * 4
    width := 8
    value_0 := row.core.a_0
    value_1 := row.core.a_1 }

/-- b-side memory-bus consumer message. The width expression is the PIL
    `b_src_ind * (ind_width - 8) + 8`, which is `ind_width` for
    indirect memory access and `8` for register / direct memory reads. -/
@[reducible]
def bMemMessageExpr (row : Var MainRowWithRom FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := bMemOpExpr row
    ptr := row.rom.addr1
    timestamp := 2 + row.rom.main_step * 4
    width := row.rom.b_src_ind * (row.core.ind_width - 8) + 8
    value_0 := row.core.b_0
    value_1 := row.core.b_1 }

/-- c-side / store memory-bus consumer message. The value lanes are
    PIL's `store_value`, which collapses to `(c_0, c_1)` for
    `store_pc = 0` and to `(pc + jmp_offset2, 0)` for `store_pc = 1`. -/
@[reducible]
def cMemMessageExpr (row : Var MainRowWithRom FGL) :
    MemBusMessage (Expression FGL) :=
  { mem_op := cMemOpExpr row
    ptr := row.rom.addr2
    timestamp := 3 + row.rom.main_step * 4
    width := row.rom.store_ind * (row.core.ind_width - 8) + 8
    value_0 := storeValueLoExpr row
    value_1 := storeValueHiExpr row }

/-- Main constraints + ROM lookup + 3 memory-bus consumer emissions.
    Composes `mainWithRom` with the 3 `MemBusChannel.emit` pushes
    matching `main.pil:284,300,323`. -/
@[circuit_norm]
def mainWithRomAndMemBus (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) : Circuit FGL Unit := do
  mainWithRom length program row
  -- a-side push (active when a_src_mem ∨ a_src_reg).
  MemBusChannel.emit (-(row.rom.a_src_mem + row.rom.a_src_reg))
    (aMemMessageExpr row)
  -- b-side push (active when b_src_mem ∨ b_src_ind ∨ b_src_reg).
  MemBusChannel.emit (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
    (bMemMessageExpr row)
  -- c-side push (active when store_mem ∨ store_ind ∨ store_reg).
  MemBusChannel.emit (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
    (cMemMessageExpr row)

/-- Elaborated `mainWithRomAndMemBus` circuit. Exposes the 3 mem-bus
    consumer interactions as channel emissions; the ROM lookup is an
    internal `Table.fromStatic` consumer push and does not surface as
    a channel interaction. -/
@[reducible] def mainWithRomAndMemBusElaborated
    (length : ℕ) (program : Program length) :
    ElaboratedCircuit FGL MainRowWithRom unit where
  main := mainWithRomAndMemBus length program
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted (-(row.rom.a_src_mem + row.rom.a_src_reg))
          (aMemMessageExpr row)
      , MemBusChannel.emitted (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
          (bMemMessageExpr row)
      , MemBusChannel.emitted (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
          (cMemMessageExpr row) ]
  channelsLawful := by
    simp only [circuit_norm, mainWithRomAndMemBus, mainWithRom, main,
      romMessageExpr, romFlagsExpr, romStaticTable,
      aMemMessageExpr, bMemMessageExpr, cMemMessageExpr,
      aMemOpExpr, bMemOpExpr, cMemOpExpr,
      storeValueLoExpr, storeValueHiExpr, MemBusChannel]

/-! ## T7.2 — unified Main row for operation and memory channels

The first full-ensemble skeleton used two separate Main components: one
over `MainRow` for the operation bus and one over `MainRowWithRom` for
ROM/memory.  That was useful while the channels were migrated separately,
but it leaves T7 with no structural statement that both channel surfaces are
the same Main row.  This combined circuit exposes both channels from the
single `MainRowWithRom.core`.
-/

/-- Main constraints + ROM lookup + memory-bus consumer emissions +
    operation-bus consumer emission, all from one `MainRowWithRom`.

The operation-bus message is exactly `opBusMessageExpr row.core`, so the
T7 full ensemble can use one Main table instead of separate op-bus and
ROM/memory Main tables. -/
@[circuit_norm]
def mainWithRomMemAndOpBus (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) : Circuit FGL Unit := do
  mainWithRomAndMemBus length program row
  OpBusChannel.emit (-row.core.is_external_op) (opBusMessageExpr row.core)

/-- Elaborated unified Main circuit for the full Clean ensemble. -/
@[reducible] def mainWithRomMemAndOpBusElaborated
    (length : ℕ) (program : Program length) :
    ElaboratedCircuit FGL MainRowWithRom unit where
  main := mainWithRomMemAndOpBus length program
  localLength _ := 0
  output _ _ := ()
  channelsWithRequirements := [MemBusChannel.toRaw, OpBusChannel.toRaw]
  exposedChannels row _ :=
    expose MemBusChannel
      [ MemBusChannel.emitted (-(row.rom.a_src_mem + row.rom.a_src_reg))
          (aMemMessageExpr row)
      , MemBusChannel.emitted (-(row.rom.b_src_mem + row.rom.b_src_ind + row.rom.b_src_reg))
          (bMemMessageExpr row)
      , MemBusChannel.emitted (-(row.rom.store_mem + row.rom.store_ind + row.rom.store_reg))
          (cMemMessageExpr row) ]
    ++ expose OpBusChannel
      [ OpBusChannel.emitted (-row.core.is_external_op)
          (opBusMessageExpr row.core) ]
  channelsLawful := by
    simp [circuit_norm, mainWithRomMemAndOpBus, mainWithRomAndMemBus,
      mainWithRom, main, romMessageExpr, romFlagsExpr, romStaticTable,
      aMemMessageExpr, bMemMessageExpr, cMemMessageExpr,
      aMemOpExpr, bMemOpExpr, cMemOpExpr,
      storeValueLoExpr, storeValueHiExpr, opBusMessageExpr,
      MemBusChannel, OpBusChannel]

end ZiskFv.AirsClean.Main
