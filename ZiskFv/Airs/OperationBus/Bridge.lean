import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
# OperationBus permutation soundness — trusted axioms

Mirrors `Airs/MemoryBus/MemBridge.lean` for `OPERATION_BUS_ID = 5000`
(`zisk/pil/opids.pil:2`).

The Main AIR consumes from the operation bus on every
`is_external_op = 1` row (`zisk/state-machines/main/pil/main.pil:367-374`).
The actual computation is performed by one of the secondary state
machines (BinaryAdd / Binary / BinaryExtension / Arith / ArithDiv),
each of which `proves_operation` on the bus for the subset of opcodes
it implements. PLONK-style permutation soundness for that protocol is
project-trusted — all-rows multiplicity-summed equality on the assumes
side forces, for every consumer row, the existence of a matching
provider row across the union of provider AIRs. This file packages
that consequence as one axiom per provider AIR.

Each axiom is parameterized on a disjunction of `m.op` literals
characterizing the opcodes that the named provider AIR is responsible
for. Citations next to each axiom point at the PIL file that defines
the provider's opcode coverage.

Trust class: PLONK / logUp permutation-argument soundness on
`OPERATION_BUS_ID = 5000`. Same scope as
`lookup_consumer_matches_provider_load` (`MemBridge.lean:161`).
-/

namespace ZiskFv.Airs.OperationBus

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **OperationBus permutation soundness — BinaryAdd provider.**
    Provider AIR: `BinaryAdd` (`zisk/state-machines/binary/pil/binary_add.pil`).
    Opcode coverage: `OP_ADD = 0x0a` only — see `binary_add.pil:25`
    `proves_operation(op: OP_ADD, ...)`.

    Concretely: any active Main row whose `op` selector reads as the
    BinaryAdd opcode is matched by some BinaryAdd row whose bus
    projection equals Main's. -/
axiom op_bus_perm_sound_BinaryAdd
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (b : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 10) :
    ∃ r_b : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_b)

/-- **OperationBus permutation soundness — Binary provider.**
    Provider AIR: `Binary` (`zisk/state-machines/binary/pil/binary.pil`).
    Opcode coverage: the union of 64-bit and 32-bit opcodes plus the
    Arith-private comparison helpers per the PIL operation table at
    `binary.pil:6-49`. The provider emits
    `op = b_op + 0x10 * mode32`, so the disjunction below enumerates
    the resulting on-bus opcode literals (mode32=0 ⇒ b_op, mode32=1
    ⇒ b_op + 0x10).

    Coverage:
    * 64-bit (mode32=0): MINU/MIN/MAXU/MAX/LTU/LT/GT/EQ/ADD/SUB/LEU/LE/AND/OR/XOR
      ⇒ 0x02..0x10;
    * 32-bit (mode32=1): same ops with `_W` suffix ⇒ 0x12..0x1d;
    * Arith helpers: LT_ABS_NP=0x50, LT_ABS_PN=0x51. -/
axiom op_bus_perm_sound_Binary
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (b : ZiskFv.Airs.Binary.Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0x02 ∨ m.op r_main = 0x03 ∨ m.op r_main = 0x04
          ∨ m.op r_main = 0x05 ∨ m.op r_main = 0x06 ∨ m.op r_main = 0x07
          ∨ m.op r_main = 0x08 ∨ m.op r_main = 0x09 ∨ m.op r_main = 0x0a
          ∨ m.op r_main = 0x0b ∨ m.op r_main = 0x0c ∨ m.op r_main = 0x0d
          ∨ m.op r_main = 0x0e ∨ m.op r_main = 0x0f ∨ m.op r_main = 0x10
          ∨ m.op r_main = 0x12 ∨ m.op r_main = 0x13 ∨ m.op r_main = 0x14
          ∨ m.op r_main = 0x15 ∨ m.op r_main = 0x16 ∨ m.op r_main = 0x17
          ∨ m.op r_main = 0x18 ∨ m.op r_main = 0x19 ∨ m.op r_main = 0x1a
          ∨ m.op r_main = 0x1b ∨ m.op r_main = 0x1c ∨ m.op r_main = 0x1d
          ∨ m.op r_main = 0x50 ∨ m.op r_main = 0x51) :
    ∃ r_b : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_Binary b r_b)

/-- **OperationBus permutation soundness — BinaryExtension provider.**
    Provider AIR: `BinaryExtension`
    (`zisk/state-machines/binary/pil/binary_extension.pil`). Opcode
    coverage from the table at `binary_extension.pil:11-21`:
    SLL=0x21, SRL=0x22, SRA=0x23, SLL_W=0x24, SRL_W=0x25, SRA_W=0x26,
    SEXT_B=0x27, SEXT_H=0x28, SEXT_W=0x29. -/
axiom op_bus_perm_sound_BinaryExtension
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (e : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0x21 ∨ m.op r_main = 0x22 ∨ m.op r_main = 0x23
          ∨ m.op r_main = 0x24 ∨ m.op r_main = 0x25 ∨ m.op r_main = 0x26
          ∨ m.op r_main = 0x27 ∨ m.op r_main = 0x28 ∨ m.op r_main = 0x29) :
    ∃ r_e : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension e r_e)

/-- **OperationBus permutation soundness — ArithMul provider.**
    Provider AIR: `Arith` (`zisk/state-machines/arith/pil/arith.pil`),
    multiplication-mode rows (`main_mul = 1`, `main_div = 0`). Opcode
    coverage per `state-machines/arith/src/arith_table_data.rs`:
    MULU=0x90, MULUH=0x91, MULSUH=0x92, MUL_W=0xb0
    (RV64IM mappings: MUL/MULH/MULHU/MULHSU/MULW). -/
axiom op_bus_perm_sound_ArithMul
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0x90 ∨ m.op r_main = 0x91 ∨ m.op r_main = 0x92
          ∨ m.op r_main = 0xb0) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main) (ZiskFv.Airs.ArithMul.opBus_row_Arith a r_a)

/-- **OperationBus permutation soundness — ArithDiv provider.**
    Provider AIR: `Arith` (`zisk/state-machines/arith/pil/arith.pil`),
    division-mode rows (`main_div = 1`). Opcode coverage:
    DIVU=0xa0, REMU=0xa1, DIV=0xa2, REM=0xa3, DIV_W=0xa4 .. REM_W=0xa7
    plus the W-mode counterparts at 0xb*.

    Two emissions are involved per division: the primary tuple
    (modeled by `opBus_row_ArithDiv`) and the secondary remainder/
    quotient tuple (`opBus_row_ArithDivSecondary`). The axiom delivers
    a witness for the primary tuple; the secondary handshake is
    covered separately by
    `op_bus_perm_sound_ArithDivSecondary` below. -/
axiom op_bus_perm_sound_ArithDiv
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0xa0 ∨ m.op r_main = 0xa1 ∨ m.op r_main = 0xa2
          ∨ m.op r_main = 0xa3 ∨ m.op r_main = 0xa4 ∨ m.op r_main = 0xa5
          ∨ m.op r_main = 0xa6 ∨ m.op r_main = 0xa7) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv a r_a)

/-- **OperationBus permutation soundness — ArithDivSecondary provider.**
    Same provider AIR as `op_bus_perm_sound_ArithDiv`, but for the
    secondary bus emission (remainder/quotient companion tuple). -/
axiom op_bus_perm_sound_ArithDivSecondary
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0xa0 ∨ m.op r_main = 0xa1 ∨ m.op r_main = 0xa2
          ∨ m.op r_main = 0xa3 ∨ m.op r_main = 0xa4 ∨ m.op r_main = 0xa5
          ∨ m.op r_main = 0xa6 ∨ m.op r_main = 0xa7) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary a r_a)

end ZiskFv.Airs.OperationBus
