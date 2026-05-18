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
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.BinaryAdd

variable {C : Type → Type → Type} [Circuit FGL FGL C]

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
structure MainRowPins (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (active : FGL) (opKind : FGL) where
  main_active : m.is_external_op r_main = active
  main_op : m.op r_main = opKind

/-! ## BinaryAdd validator + universal core constraint -/

/-- `Valid_BinaryAdd` provider + the universal-row core-constraint
    quantifier that canonical theorems and wrappers consume together.
    Shared by ADD, ADDI. Takes the circuit functor `C` explicitly so
    type ascription is unambiguous at callers; the `[Circuit FGL FGL C]`
    instance is inferred from the surrounding scope. -/
structure BinaryAddWitness (C : Type → Type → Type) [Circuit FGL FGL C] where
  validator : Valid_BinaryAdd C FGL FGL
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

/-! ## MemAlign witness triple + low-byte pinning -/

/-- The three MemAlign-family provider witnesses plus the low-byte
    pinning bridge they jointly support. Shared by LBU, LHU, LWU.
    Takes the circuit functor `C` explicitly so type ascription is
    unambiguous at callers; the `[Circuit FGL FGL C]` instance is
    inferred from the surrounding scope. -/
structure MemAlignWitness (C : Type → Type → Type) [Circuit FGL FGL C] where
  mab : ZiskFv.Airs.MemAlignByte.Valid_MemAlignByte C FGL FGL
  marb : ZiskFv.Airs.MemAlignReadByte.Valid_MemAlignReadByte C FGL FGL
  ma : ZiskFv.Airs.MemAlign.Valid_MemAlign C FGL FGL
  h_low : ZiskFv.Airs.MemoryBus.MemAlignBridge.SubdoublewordLoadLowBytePinning mab marb ma

/-! ## Byte-range bounds on a memory-bus entry -/

/-- The 8-tuple `e.xᵢ.val < 256` that recurs in every canonical that
    range-bounds its rd-producer's lanes (ADD's `equiv_ADD`, the 5 Mul
    canonicals, the Div/Rem opcodes, etc.). Type-indexed on the entry
    so each caller pins its own `e`. -/
structure ByteBounds (e : Interaction.MemoryBusEntry FGL) where
  x0_lt : e.x0.val < 256
  x1_lt : e.x1.val < 256
  x2_lt : e.x2.val < 256
  x3_lt : e.x3.val < 256
  x4_lt : e.x4.val < 256
  x5_lt : e.x5.val < 256
  x6_lt : e.x6.val < 256
  x7_lt : e.x7.val < 256

end ZiskFv.Compliance
