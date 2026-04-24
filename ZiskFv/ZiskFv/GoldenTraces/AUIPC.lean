import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.AddUpperImmediatePC

/-!
Phase 3C Track T-U2 golden-trace fixture: one canonical AUIPC row
covering the add-upper-immediate-PC case with a non-zero rd.

AUIPC emits **no** operation-bus entry (`is_external_op = 0`,
Internal op `flag`), so there is no secondary-SM row to co-validate.
The fixture exercises:

* the Main-AIR's internal-op-0 constraints: `c = 0`, `flag = 1`;
* the `store_value[0] = store_pc * (pc + jmp_offset2 - c_0) + c_0`
  expression with `store_pc = 1, c_0 = 0`:
  rd-low ← `pc + jmp_offset2 = pc + imm`;
* the PC-handshake formula for `set_pc = 0, flag = 1`:
  `next_pc = pc + jmp_offset2 + (jmp_offset1 - jmp_offset2)
          = pc + jmp_offset1 = pc + 4`;
* the Zisk-opcode-ID literal `OP_FLAG = 0` that `transpile_AUIPC`
  emits.

Concrete witness: AUIPC `x1, 0x20000` at `pc = 100`. Immediate
(shifted left by 12) = 0x20000000 = 536870912. Expected:
`next_pc = 104` (= 100 + jmp_offset1 = 100 + 4),
`x1 = 536871012` (= 100 + 0x20000000).

All `example`s use `decide` — the trace is fully concrete, no free
variables.
-/

namespace ZiskFv.GoldenTraces.AUIPC

open Goldilocks
open ZiskFv.Trusted

section AuipcWitness

/- Witness row: AUIPC `x1, 0x20000` against `pc = 100`.
   imm = 0x20000, shifted left by 12: 0x20000000 = 536870912.
   jmp_offset2 = 0x20000000 (AUIPC routes imm through jmp_offset2).
   jmp_offset1 = 4 (fall-through). -/

@[simp] def auipc_pc : FGL := 100
@[simp] def auipc_a_lo : FGL := 0              -- src_a = imm 0
@[simp] def auipc_a_hi : FGL := 0
@[simp] def auipc_b_lo : FGL := 0              -- src_b = imm 0
@[simp] def auipc_b_hi : FGL := 0
@[simp] def auipc_c_lo : FGL := 0              -- op=flag → c = 0
@[simp] def auipc_c_hi : FGL := 0
@[simp] def auipc_flag : FGL := 1              -- op=flag → flag = 1 (constraint 17)
@[simp] def auipc_set_pc : FGL := 0
@[simp] def auipc_store_pc : FGL := 1          -- rd ← pc + jmp_offset2
@[simp] def auipc_jmp_offset1 : FGL := 4       -- fall-through
@[simp] def auipc_jmp_offset2 : FGL := 536870912 -- imm = 0x20000 << 12
@[simp] def auipc_is_external_op : FGL := 0    -- Internal
@[simp] def auipc_op : FGL := 0                -- OP_FLAG
@[simp] def auipc_m32 : FGL := 0

/-- Consistency with `OP_FLAG` literal. -/
example : auipc_op = OP_FLAG := by decide

/-- Next-pc from the handshake formula (set_pc = 0, flag = 1):
    `pc + jmp_offset2 + 1 * (jmp_offset1 - jmp_offset2)
    = pc + jmp_offset1 = 100 + 4 = 104`. -/
example :
    auipc_pc + auipc_jmp_offset2
      + auipc_flag * (auipc_jmp_offset1 - auipc_jmp_offset2)
      = (104 : FGL) := by decide

/-- Direct PC-advance form: `next_pc = pc + jmp_offset1 = 104`. -/
example :
    auipc_pc + auipc_jmp_offset1 = (104 : FGL) := by decide

/-- Store-value (low lane, `main.pil:311`):
    `store_pc * (pc + jmp_offset2 - c_0) + c_0`
    = 1 * (100 + 536870912 - 0) + 0 = 536871012.
    This is the `pc + imm` value written to rd. -/
example :
    auipc_store_pc * (auipc_pc + auipc_jmp_offset2 - auipc_c_lo)
      + auipc_c_lo
      = (536871012 : FGL) := by decide

/-- Store-value (high lane): `(1 - store_pc) * c_1 = 0 * 0 = 0`. -/
example :
    (1 - auipc_store_pc) * auipc_c_hi = (0 : FGL) := by decide

/-- `flag` boolean-ness. -/
example : auipc_flag * (1 - auipc_flag) = (0 : FGL) := by decide

/-- `is_external_op` boolean-ness. -/
example :
    auipc_is_external_op * (1 - auipc_is_external_op)
      = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness. -/
example : auipc_flag * auipc_set_pc = (0 : FGL) := by decide

/-- Constraint 8 (internal op=0 zeroes c_0):
    `(1 - ext) * (1 - op) * c_0 = 0`. -/
example :
    (1 - auipc_is_external_op) * (1 - auipc_op) * auipc_c_lo
      = (0 : FGL) := by decide

/-- Constraint 15 (internal op=0 zeroes c_1):
    `(1 - ext) * (1 - op) * c_1 = 0`. -/
example :
    (1 - auipc_is_external_op) * (1 - auipc_op) * auipc_c_hi
      = (0 : FGL) := by decide

/-- Constraint 17 (internal op=0 sets flag = 1):
    `(1 - ext) * (1 - op) * (1 - flag) = 0`. -/
example :
    (1 - auipc_is_external_op) * (1 - auipc_op) * (1 - auipc_flag)
      = (0 : FGL) := by decide

end AuipcWitness

-- Phase 4.5 Track D: additional edge-case fixture.

section ZeroPC

/- Witness row: AUIPC `x1, 0` at `pc = 0`. Immediate = 0, so the
   rd-write is `pc + 0 = 0`. Tests the degenerate PC-origin case. -/

@[simp] def auipc_pc : FGL := 0
@[simp] def auipc_c_lo : FGL := 0
@[simp] def auipc_c_hi : FGL := 0
@[simp] def auipc_flag : FGL := 1
@[simp] def auipc_set_pc : FGL := 0
@[simp] def auipc_store_pc : FGL := 1
@[simp] def auipc_jmp_offset1 : FGL := 4
@[simp] def auipc_jmp_offset2 : FGL := 0         -- zero imm
@[simp] def auipc_is_external_op : FGL := 0
@[simp] def auipc_op : FGL := 0

/-- rd-write: `pc + imm = 0 + 0 = 0`. -/
example :
    auipc_store_pc * (auipc_pc + auipc_jmp_offset2 - auipc_c_lo)
      + auipc_c_lo
      = (0 : FGL) := by decide

/-- Next-pc: `pc + jmp_offset1 = 0 + 4 = 4`. -/
example :
    auipc_pc + auipc_jmp_offset2
      + auipc_flag * (auipc_jmp_offset1 - auipc_jmp_offset2)
      = (4 : FGL) := by decide

end ZeroPC

end ZiskFv.GoldenTraces.AUIPC
