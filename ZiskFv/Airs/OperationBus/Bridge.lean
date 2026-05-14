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
    coverage per `zisk/pil/operations.pil:71-78`:
    MULU=0xb0, MULUH=0xb1, MULSUH=0xb3, MUL=0xb4, MULH=0xb5, MUL_W=0xb6.
    (0xb2 and 0xb7 are reserved-but-unused holes in upstream
    `operations.pil` and are excluded from the disjunction.)
    RV64IM mappings: MUL=0xb4, MULH=0xb5, MULHU=0xb0, MULHSU=0xb3, MULW=0xb6. -/
axiom op_bus_perm_sound_ArithMul
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0xb0 ∨ m.op r_main = 0xb1 ∨ m.op r_main = 0xb3
          ∨ m.op r_main = 0xb4 ∨ m.op r_main = 0xb5 ∨ m.op r_main = 0xb6) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main) (ZiskFv.Airs.ArithMul.opBus_row_Arith a r_a)

/-- **OperationBus permutation soundness — ArithMulSecondary provider.**
    Same provider AIR as `op_bus_perm_sound_ArithMul`, but for the
    secondary bus emission. On MUL-family rows whose result lane is the
    high 64 bits of the 128-bit product (MULH / MULHU / MULHSU), Arith's
    `proves_operation` invocation packs `bus_c0` from the `d[]` chunks
    rather than from `c[]`. PLONK-style permutation soundness on
    `OPERATION_BUS_ID = 5000` gives, for every Main-side consumer row
    pinned to MULH/MULHU/MULHSU, the existence of a matching Arith row
    whose `opBus_row_ArithMulSecondary` projection matches Main's
    `opBus_row_Main`.

    Opcode coverage per `zisk/pil/operations.pil:71-78`:
    MULUH = 0xb1 (= MULHU), MULSUH = 0xb3 (= MULHSU), MULH = 0xb5.
    (0xb0 = MULU/MUL produces a low-half result on the primary lane;
    its secondary lane carries the high half but is not consumed by
    any RV64IM opcode that takes the high half — see
    `core/src/riscv2zisk_context.rs` MULH-family lowering. The high
    half is *only* observed on rows whose `op ∈ {0xb1, 0xb3, 0xb5}`,
    where the primary `c[]` lane would carry a discarded low half.
    For the formal proof's purposes, however, only the three MULH
    family opcodes need the secondary handshake — they are the only
    ones whose canonical `equiv_<OP>` consumes `v.d_*` chunks in the
    `h_byte_lo` / `h_byte_hi` lane-match equation.)

    Trust class #4 (operation-bus permutation soundness on
    `OPERATION_BUS_ID = 5000`) — same class as
    `op_bus_perm_sound_ArithMul` and
    `op_bus_perm_sound_ArithDivSecondary`. -/
axiom op_bus_perm_sound_ArithMulSecondary
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (a : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0xb1 ∨ m.op r_main = 0xb3 ∨ m.op r_main = 0xb5) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary a r_a)

/-- **OperationBus permutation soundness — ArithDiv provider.**
    Provider AIR: `Arith` (`zisk/state-machines/arith/pil/arith.pil`),
    division-mode rows (`main_div = 1`). Opcode coverage per
    `zisk/pil/operations.pil:79-86`:
    DIVU=0xb8, REMU=0xb9, DIV=0xba, REM=0xbb,
    DIVU_W=0xbc, REMU_W=0xbd, DIV_W=0xbe, REM_W=0xbf.

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
    (h_op : m.op r_main = 0xb8 ∨ m.op r_main = 0xb9 ∨ m.op r_main = 0xba
          ∨ m.op r_main = 0xbb ∨ m.op r_main = 0xbc ∨ m.op r_main = 0xbd
          ∨ m.op r_main = 0xbe ∨ m.op r_main = 0xbf) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv a r_a)

/-- **OperationBus permutation soundness — ArithDivSecondary provider.**
    Same provider AIR as `op_bus_perm_sound_ArithDiv`, but for the
    secondary bus emission (remainder/quotient companion tuple).
    Opcode coverage: same as `op_bus_perm_sound_ArithDiv`. -/
axiom op_bus_perm_sound_ArithDivSecondary
    (m : ZiskFv.Airs.Main.Valid_Main C FGL FGL)
    (a : ZiskFv.Airs.ArithDiv.Valid_ArithDiv C FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0xb8 ∨ m.op r_main = 0xb9 ∨ m.op r_main = 0xba
          ∨ m.op r_main = 0xbb ∨ m.op r_main = 0xbc ∨ m.op r_main = 0xbd
          ∨ m.op r_main = 0xbe ∨ m.op r_main = 0xbf) :
    ∃ r_a : ℕ,
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary a r_a)

end ZiskFv.Airs.OperationBus
