import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.LoadUpperImmediate

/-!
Phase 3C Track T-U1 golden-trace fixture: one canonical LUI row
covering the load-upper-immediate case with a non-zero rd.

LUI emits **no** operation-bus entry (`is_external_op = 0`, Internal
op `copyb`), so there is no secondary-SM row to co-validate. The
fixture exercises:

* the Main-AIR's internal-op-1 constraints: `c = b`, `flag = 0`;
* the `store_value[0] = store_pc * (pc + jmp_offset2 - c_0) + c_0`
  expression with `store_pc = 0, c_0 = b_0`: rd-low ← `b_0 = imm_lo`;
* the PC-handshake formula for `set_pc = 0, flag = 0`:
  `next_pc = pc + jmp_offset2 = pc + 4`;
* the Zisk-opcode-ID literal `OP_COPYB = 1` that `transpile_LUI` emits.

Concrete witness: LUI `x1, 0xABCDE` at `pc = 100`. Expected results:
`next_pc = 104`, `x1 = 0xABCDE000` (= `0xABCDE << 12`, which fits in
the low 32-bit lane).

All `example`s use `decide` — the trace is fully concrete, no free
variables. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.LUI

open Goldilocks
open ZiskFv.Trusted

section LuiWitness

/- Witness row: LUI `x1, 0xABCDE` against `pc = 100`.
   Immediate = 0xABCDE, shifted left by 12: 0xABCDE000.
   Fits entirely in the low 32-bit lane (b_hi = 0). -/

@[simp] def lui_pc : FGL := 100
@[simp] def lui_a_lo : FGL := 0                -- src_a = imm 0
@[simp] def lui_a_hi : FGL := 0
@[simp] def lui_b_lo : FGL := 0xABCDE000       -- imm shifted left by 12 (low lane)
@[simp] def lui_b_hi : FGL := 0                -- high lane (positive imm)
@[simp] def lui_c_lo : FGL := 0xABCDE000       -- op=copyb → c = b
@[simp] def lui_c_hi : FGL := 0
@[simp] def lui_flag : FGL := 0                -- op=copyb → flag = 0 (constraint 18)
@[simp] def lui_set_pc : FGL := 0
@[simp] def lui_store_pc : FGL := 0            -- rd ← c (not pc + offset)
@[simp] def lui_jmp_offset1 : FGL := 4
@[simp] def lui_jmp_offset2 : FGL := 4
@[simp] def lui_is_external_op : FGL := 0      -- Internal
@[simp] def lui_op : FGL := 1                  -- OP_COPYB
@[simp] def lui_m32 : FGL := 0

/-- Consistency with `OP_COPYB` literal. -/
example : lui_op = OP_COPYB := by decide

/-- Next-pc from the handshake formula (set_pc = 0, flag = 0):
    `pc + jmp_offset2 + 0 = 104`. -/
example :
    lui_pc + lui_jmp_offset2
      + lui_flag * (lui_jmp_offset1 - lui_jmp_offset2)
      = (104 : FGL) := by decide

/-- Direct PC-advance form: `next_pc = pc + jmp_offset2 = 104`. -/
example : lui_pc + lui_jmp_offset2 = (104 : FGL) := by decide

/-- Store-value (low lane, `main.pil:311`):
    `store_pc * (pc + jmp_offset2 - c_0) + c_0 = 0 + c_0 = c_0 = b_0 = 0xABCDE000`. -/
example :
    lui_store_pc * (lui_pc + lui_jmp_offset2 - lui_c_lo) + lui_c_lo
      = (0xABCDE000 : FGL) := by decide

/-- Store-value (high lane, `main.pil:312`):
    `(1 - store_pc) * c_1 = 1 * c_1 = b_1 = 0`. -/
example :
    (1 - lui_store_pc) * lui_c_hi = (0 : FGL) := by decide

/-- `flag` boolean-ness. -/
example : lui_flag * (1 - lui_flag) = (0 : FGL) := by decide

/-- `is_external_op` boolean-ness. -/
example :
    lui_is_external_op * (1 - lui_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness. -/
example : lui_flag * lui_set_pc = (0 : FGL) := by decide

/-- Constraint 9 (internal op=1 copies b_0 to c_0):
    `(1 - ext) * op * (b_0 - c_0) = 0`. -/
example :
    (1 - lui_is_external_op) * lui_op * (lui_b_lo - lui_c_lo)
      = (0 : FGL) := by decide

/-- Constraint 16 (internal op=1 copies b_1 to c_1):
    `(1 - ext) * op * (b_1 - c_1) = 0`. -/
example :
    (1 - lui_is_external_op) * lui_op * (lui_b_hi - lui_c_hi)
      = (0 : FGL) := by decide

/-- Constraint 18 (internal op=1 clears flag):
    `(1 - ext) * op * flag = 0`. -/
example :
    (1 - lui_is_external_op) * lui_op * lui_flag
      = (0 : FGL) := by decide

end LuiWitness

-- Phase 4.5 Track D: additional edge-case fixture.

section ZeroImm

/- Witness row: LUI `x1, 0` — imm = 0 ⇒ rd = 0. Smallest corner case. -/

@[simp] def lui_pc : FGL := 100
@[simp] def lui_b_lo : FGL := 0
@[simp] def lui_b_hi : FGL := 0
@[simp] def lui_c_lo : FGL := 0
@[simp] def lui_c_hi : FGL := 0
@[simp] def lui_flag : FGL := 0
@[simp] def lui_set_pc : FGL := 0
@[simp] def lui_store_pc : FGL := 0
@[simp] def lui_jmp_offset1 : FGL := 4
@[simp] def lui_jmp_offset2 : FGL := 4

/-- rd = c_0 = 0. -/
example :
    lui_store_pc * (lui_pc + lui_jmp_offset2 - lui_c_lo) + lui_c_lo
      = (0 : FGL) := by decide

/-- High lane zero. -/
example : (1 - lui_store_pc) * lui_c_hi = (0 : FGL) := by decide

/-- Next-pc = 104. -/
example :
    lui_pc + lui_jmp_offset2
      + lui_flag * (lui_jmp_offset1 - lui_jmp_offset2)
      = (104 : FGL) := by decide

end ZeroImm

end ZiskFv.GoldenTraces.LUI
