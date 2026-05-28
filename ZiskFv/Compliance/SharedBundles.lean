import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.MemAlignByte
import ZiskFv.Airs.MemAlignReadByte
import ZiskFv.Airs.MemAlign
import ZiskFv.Airs.MemoryBus.MemAlignBridge
import ZiskFv.AirsClean.MemAlignByte.Bridge
import ZiskFv.AirsClean.MemAlignReadByte.Bridge
import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.Channels.MemoryBusBytes

/-!
# `SharedBundles` — small structural bundles shared across opcode shapes

Companions to `Equivalence/Promises/*` (per-shape promise bundles
shipped in PR #34): these are smaller, opcode-shape-uniform bundles
that absorb the remaining loose recurring binders on canonical
`equiv_<OP>` theorems, `equiv_<OP>` Compliance wrappers, and
`OpEnvelope` arms.

Each bundle is a thin record of already-existing fields — no derivation
is hidden, no premise is reified. Refactor-only.
-/

namespace ZiskFv.Compliance

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd


/-! ## Bus rows: shared by ~52 OpEnvelope arms / wrappers / canonicals -/

/-- Three memory-bus rows + the execution-bus row. Recurs across every
    R-type/I-type/shift/mul/div/load/store opcode in the same shape:
    `e0` is the rs1 consumer, `e1` is the rs2 consumer, `e2` is the rd
    producer (with the per-arm's exec-bus producer/consumer pair). -/
structure BusRows where
  exec_row : List (Interaction.ExecutionBusEntry FGL)
  e0 : Interaction.MemoryBusEntry FGL
  e1 : Interaction.MemoryBusEntry FGL
  e2 : Interaction.MemoryBusEntry FGL

/-! ## Branch instruction operands -/

/-- The five loose operands that recur in every branch opcode's
    canonical theorem, wrapper, and `OpEnvelope` arm. Branches have no
    `e0/e1/e2` (no memory operations), so `BusRows` doesn't fit; this
    smaller bundle absorbs the branch-shape loose binders. -/
structure BranchInstrOperands where
  imm : BitVec 13
  r1 : regidx
  r2 : regidx
  misa_val : RegisterType Register.misa
  exec_row : List (Interaction.ExecutionBusEntry FGL)

/-! ## Main-row activation + opcode pins -/

/-- The two pins every opcode lands on `Valid_Main`: the activation
    bit (`is_external_op r_main = active`) and the opcode literal
    (`op r_main = opKind`). Type-indexed on the FGL literals so each
    caller pins its own `active`/`opKind`. -/
structure MainRowPins (m : Valid_Main FGL FGL) (r_main : ℕ)
    (active : FGL) (opKind : FGL) where
  main_active : m.is_external_op r_main = active
  main_op : m.op r_main = opKind

/-! ## Main structural memory witnesses -/

/-- Structural witness for an external-arithmetic rd-write on Main's
    unified memory channel.

The witness ties the existing `Valid_Main` row to a Clean
`MainRowWithRom`, pins the arithmetic `store_pc = 0` case, and carries
the legacy-entry match against Main's real PIL-shaped `c` memory
message. It replaces the lane portion of
`main_external_arith_emission_bundle` without assuming that a Clean PIL
message is definitionally a legacy `MemoryBusEntry`. -/
structure ExternalArithMemoryWitness
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (e_rd : Interaction.MemoryBusEntry FGL) where
  row : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row_eq : row.core = ZiskFv.AirsClean.Main.rowAt main r_main
  store_pc_zero : row.core.store_pc = 0
  rd_write_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry e_rd
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage row) 1 1)

theorem ExternalArithMemoryWitness.c_lanes
    {main : Valid_Main FGL FGL} {r_main : ℕ}
    {e_rd : Interaction.MemoryBusEntry FGL}
    (w : ExternalArithMemoryWitness main r_main e_rd) :
    main.c_0 r_main = ZiskFv.Airs.MemoryBus.memory_entry_lo e_rd
    ∧ main.c_1 r_main = ZiskFv.Airs.MemoryBus.memory_entry_hi e_rd :=
  ZiskFv.AirsClean.Main.external_arith_register_write_lanes_of_message_match_valid
    main r_main w.row e_rd w.row_eq w.store_pc_zero w.rd_write_match

theorem ExternalArithMemoryWitness.c_lane_vals
    {main : Valid_Main FGL FGL} {r_main : ℕ}
    {e_rd : Interaction.MemoryBusEntry FGL}
    (w : ExternalArithMemoryWitness main r_main e_rd) :
    (main.c_0 r_main).val = e_rd.value_0.val
    ∧ (main.c_1 r_main).val = e_rd.value_1.val := by
  obtain ⟨h0, h1⟩ := w.c_lanes
  exact ⟨by simpa [ZiskFv.Airs.MemoryBus.memory_entry_lo] using congrArg Fin.val h0,
    by simpa [ZiskFv.Airs.MemoryBus.memory_entry_hi] using congrArg Fin.val h1⟩

/-- Structural witness for an internal store-PC rd-write on Main's unified
memory channel.

This exposes the selected Clean Main `c` memory row and its legacy-entry
match. It is the structural-unpacking replacement for
`main_store_pc_emission_bundle` on LUI/AUIPC/JAL/JALR-style rows; opcode
mode pins still live outside this witness. -/
structure StorePcMemoryWitness
    (main : Valid_Main FGL FGL) (r_main : ℕ)
    (e_rd : Interaction.MemoryBusEntry FGL) where
  row : ZiskFv.AirsClean.Main.MainRowWithRom FGL
  row_eq : row.core = ZiskFv.AirsClean.Main.rowAt main r_main
  rd_write_match :
    ZiskFv.Airs.MemoryBus.matches_memory_entry e_rd
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage row) 1 1)

theorem StorePcMemoryWitness.lanes
    {main : Valid_Main FGL FGL} {r_main : ℕ}
    {e_rd : Interaction.MemoryBusEntry FGL}
    (w : StorePcMemoryWitness main r_main e_rd) :
    ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo main r_main e_rd
    ∧ ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi main r_main e_rd :=
  ZiskFv.AirsClean.Main.store_pc_lanes_of_message_match_valid
    main r_main w.row e_rd w.row_eq w.rd_write_match

/-! ## ArithTable lookup witnesses -/

/-- Lookup-aware Clean witness for a selected ArithMul row's
    `arith_table_assumes` tuple.

This is structural unpacking of the former raw
`ArithTableSpec (rowAt v r)` binder: callers expose the Clean operation
soundness proof for `mainWithArithTable`, and the table membership is
derived by `AirsClean.ArithMul.Bridge`. -/
structure ArithMulTableWitness
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
        (ZiskFv.AirsClean.ArithMul.constVar
          (ZiskFv.AirsClean.ArithMul.rowAt v r))).operations offset)

theorem ArithMulTableWitness.spec
    {v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL} {r : ℕ}
    (w : ArithMulTableWitness v r) :
    ZiskFv.AirsClean.ArithMul.ArithTableSpec
      (ZiskFv.AirsClean.ArithMul.rowAt v r) :=
  ZiskFv.AirsClean.ArithMul.arith_table_spec_of_lookup_aware_const_soundness
    w.offset w.env (ZiskFv.AirsClean.ArithMul.rowAt v r) w.holds

/-- Lookup-aware Clean witness for a selected ArithMul row's sixteen
    `bits(16)` chunk checks.

This is the T6 structural source for replacing
`arith_mul_columns_in_range` on MUL-family paths: callers expose the Clean
operation soundness proof for `mainWithChunkRanges`, and the actual
`a/b/c/d` chunk bounds are derived by `AirsClean.ArithMul.Bridge`. -/
abbrev ArithMulChunkRangeWitness
    (v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL) (r : ℕ) :=
  ZiskFv.AirsClean.ArithMul.ChunkRangeLookupWitness v r

theorem ArithMulChunkRangeWitness.ranges
    {v : ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL} {r : ℕ}
    (w : ArithMulChunkRangeWitness v r) :
    (v.a_0 r).val < 2 ^ 16 ∧ (v.a_1 r).val < 2 ^ 16
  ∧ (v.a_2 r).val < 2 ^ 16 ∧ (v.a_3 r).val < 2 ^ 16
  ∧ (v.b_0 r).val < 2 ^ 16 ∧ (v.b_1 r).val < 2 ^ 16
  ∧ (v.b_2 r).val < 2 ^ 16 ∧ (v.b_3 r).val < 2 ^ 16
  ∧ (v.c_0 r).val < 2 ^ 16 ∧ (v.c_1 r).val < 2 ^ 16
  ∧ (v.c_2 r).val < 2 ^ 16 ∧ (v.c_3 r).val < 2 ^ 16
  ∧ (v.d_0 r).val < 2 ^ 16 ∧ (v.d_1 r).val < 2 ^ 16
  ∧ (v.d_2 r).val < 2 ^ 16 ∧ (v.d_3 r).val < 2 ^ 16 :=
  ZiskFv.AirsClean.ArithMul.chunk_ranges_of_lookup_aware_const_soundness w

/-- Lookup-aware Clean witness for a selected ArithDiv row's
    `arith_table_assumes` tuple. Same shape as `ArithMulTableWitness`,
    specialized to the Div view of the Arith AIR. -/
structure ArithDivTableWitness
    (v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL) (r : ℕ) where
  offset : ℕ
  env : Environment FGL
  holds :
    ConstraintsHold.Soundness env
      ((ZiskFv.AirsClean.ArithDiv.mainWithArithTable
        (ZiskFv.AirsClean.ArithDiv.constVar
          (ZiskFv.AirsClean.ArithDiv.rowAt v r))).operations offset)

theorem ArithDivTableWitness.spec
    {v : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL} {r : ℕ}
    (w : ArithDivTableWitness v r) :
    ZiskFv.AirsClean.ArithDiv.ArithTableSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt v r) :=
  ZiskFv.AirsClean.ArithDiv.arith_table_spec_of_lookup_aware_const_soundness
    w.offset w.env (ZiskFv.AirsClean.ArithDiv.rowAt v r) w.holds

/-! ## BinaryAdd validator + universal core constraint -/

/-- `Valid_BinaryAdd` provider + the universal-row core-constraint
    quantifier that canonical theorems and wrappers consume together.
    Shared by ADD, ADDI. -/
structure BinaryAddWitness where
  validator : Valid_BinaryAdd FGL FGL
  core : ∀ r, ZiskFv.Airs.BinaryAdd.core_every_row validator r

/-! ## Full mode-register set -/

/-- Four M-mode register snapshots that loads, stores, and JALR all
    take as a quadruple. Branches use only `misa` and do NOT use this
    bundle. -/
structure ModeRegsFull where
  mstatus : RegisterType Register.mstatus
  pmaRegion : PMA_Region
  misa : RegisterType Register.misa
  mseccfg : RegisterType Register.mseccfg

/-! ## MemAlign witness triple + structural provider pinning -/

/-- The three MemAlign-family provider witnesses plus the low-byte
    pinning bridge they jointly support. Shared by LBU, LHU, LWU.

    **C1 re-root.** `mab_core` is the MemAlignByte AIR's own
    `core_every_row` PIL constraints — a *constructibility* fact (a
    real ZisK MemAlignByte trace satisfies its PIL). It replaces the
    former free-floating `bus_byte < 256` promise (`byte_value_lt`,
    removed from the MemAlign provider witness): the narrow loads
    now *derive* that range bound from `mab_core` **through the Clean
    `memAlignByteComponent`** (`bus_byte_in_range_via_component`),
    rather than accept it as a caller promise. Same validator-bundled
    universal-row-constraint shape as `BinaryAddWitness.core`.

    **C2 re-root.** `marb_core` is the MemAlignReadByte AIR's own
    `core_every_row` PIL constraints — the analogous *constructibility*
    fact. It replaces the former free-floating `byte_value < 256`
    promise (`read_byte_value_lt`, removed from
    `SubdoublewordLoadLowBytePinning`): the narrow loads now *derive*
    that range bound from `marb_core` **through the Clean
    `memAlignReadByteComponent`** (`byte_value_in_range_via_component`),
    rather than accept it as a caller promise.

    **T4 structural unpacking.** `provider` replaces the former
    MemAlign-family permutation and MemAlignRom trust-ledger axioms with
    an explicit selected-provider-row witness. The general MemAlign
    branch carries the ROM-derived row facts because `MemAlignRom` is not
    currently extracted as a first-class Lean table.

    **T7 range re-root.** `mab_lookup` / `marb_lookup` expose
    lookup-aware Clean `ConstraintsHold.Soundness` for the selected
    MemAlignByte / MemAlignReadByte rows. The byte bounds now come from
    those concrete `lookup rangeTable*` operations instead of
    `range_bus_sound`. -/
structure MemAlignWitness
    (main : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (r_main : ℕ)
    (e : Interaction.MemoryBusEntry FGL) where
  mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte FGL FGL
  marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte FGL FGL
  ma : ZiskFv.Airs.MemAlign.Valid_MemAlign FGL FGL
  mab_core : ∀ r, ZiskFv.Airs.MemAlignByte.core_every_row mab r
  marb_core : ∀ r, ZiskFv.Airs.MemAlignReadByte.core_every_row marb r
  mab_lookup :
    ∀ r, ZiskFv.AirsClean.MemAlignByte.RangeLookupWitness mab r
  marb_lookup :
    ∀ r, ZiskFv.AirsClean.MemAlignReadByte.RangeLookupWitness marb r
  provider :
    ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadProviderWitness
      main mab marb ma r_main e

/-! ## Byte-range bounds on a memory-bus entry -/

/-- The 8-tuple `e.xᵢ.val < 256` that recurs in every canonical that
    range-bounds its rd-producer's lanes (ADD's `equiv_ADD`, the 5 Mul
    canonicals, the Div/Rem opcodes, etc.). Type-indexed on the entry
    so each caller pins its own `e`. -/
structure ByteBounds (e : Interaction.MemoryBusEntry FGL) where
  x0_lt : (byteAt e 0).val < 256
  x1_lt : (byteAt e 1).val < 256
  x2_lt : (byteAt e 2).val < 256
  x3_lt : (byteAt e 3).val < 256
  x4_lt : (byteAt e 4).val < 256
  x5_lt : (byteAt e 5).val < 256
  x6_lt : (byteAt e 6).val < 256
  x7_lt : (byteAt e 7).val < 256

end ZiskFv.Compliance
