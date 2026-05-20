import Mathlib

import ZiskFv.Circuit
import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Consolidated
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.Binary.BinaryAdd
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryExtension
import ZiskFv.Airs.Arith.Mul
import ZiskFv.Airs.Arith.Div

/-!
# OperationBus permutation soundness — per-provider derived theorems

This file used to host three per-provider axioms
(`op_bus_perm_sound_BinaryAdd`, `op_bus_perm_sound_Binary`,
`op_bus_perm_sound_BinaryExtension`). They are now **theorems**
derived from the consolidated bus-level axiom
`op_bus_permutation_sound` in `Consolidated.lean`.

The three per-provider names + signatures are preserved exactly so
downstream consumers (per-AIR discharge bridges, Compliance
wrappers) require no changes. Net trust ledger delta: 3 axioms → 1
axiom (the bus-level `op_bus_permutation_sound`).

Trust class: PLONK / logUp permutation-argument soundness on
`OPERATION_BUS_ID = 5000`. Same scope as
`lookup_consumer_matches_provider_load` (`MemBridge.lean:161`).
-/

namespace ZiskFv.Airs.OperationBus

open Goldilocks


/-- **OperationBus permutation soundness — BinaryAdd provider.**
    Now a theorem: specialization of `op_bus_permutation_sound`
    (`Consolidated.lean`) to the BinaryAdd provider.

    Provider AIR: `BinaryAdd` (`zisk/state-machines/binary/pil/binary_add.pil`).
    Opcode coverage: `OP_ADD = 0x0a` only — see `binary_add.pil:25`
    `proves_operation(op: OP_ADD, ...)`. -/
theorem op_bus_perm_sound_BinaryAdd
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (b : ZiskFv.Airs.BinaryAdd.Valid_BinaryAdd FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 10) :
    ∃ r_b : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryAdd b r_b) :=
  op_bus_permutation_sound m (.binaryAdd b : OpBusProvider) r_main h_active h_op

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
theorem op_bus_perm_sound_Binary
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (b : ZiskFv.Airs.Binary.Valid_Binary FGL FGL)
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
      matches_entry (opBus_row_Main m r_main) (opBus_row_Binary b r_b) :=
  op_bus_permutation_sound m (.binary b) r_main h_active h_op

/-- **OperationBus permutation soundness — BinaryExtension provider.**
    Provider AIR: `BinaryExtension`
    (`zisk/state-machines/binary/pil/binary_extension.pil`). Opcode
    coverage from the table at `binary_extension.pil:11-21`:
    SLL=0x21, SRL=0x22, SRA=0x23, SLL_W=0x24, SRL_W=0x25, SRA_W=0x26,
    SEXT_B=0x27, SEXT_H=0x28, SEXT_W=0x29. -/
theorem op_bus_perm_sound_BinaryExtension
    (m : ZiskFv.Airs.Main.Valid_Main FGL FGL)
    (e : ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL)
    (r_main : ℕ)
    (h_active : m.is_external_op r_main = 1)
    (h_op : m.op r_main = 0x21 ∨ m.op r_main = 0x22 ∨ m.op r_main = 0x23
          ∨ m.op r_main = 0x24 ∨ m.op r_main = 0x25 ∨ m.op r_main = 0x26
          ∨ m.op r_main = 0x27 ∨ m.op r_main = 0x28 ∨ m.op r_main = 0x29) :
    ∃ r_e : ℕ,
      matches_entry (opBus_row_Main m r_main) (opBus_row_BinaryExtension e r_e) :=
  op_bus_permutation_sound m (.binaryExtension e : OpBusProvider) r_main h_active h_op

end ZiskFv.Airs.OperationBus
