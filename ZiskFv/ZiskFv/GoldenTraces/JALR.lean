import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Jalr

/-!
Phase 2.5 D4 archetype-validation golden-trace fixture: one canonical
JALR row covering the register-relative unconditional-jump case with a
non-zero rd (link-address write).

Unlike `GoldenTraces.JAL` (same archetype family) this fixture
exercises the JALR archetype's distinctive invariants:

* the Main-AIR's `set_pc = 1` PC-handshake formula: `next_pc = c[0] +
  jmp_offset1`, where `c[0] = b[0]` from internal-op-1 constraint 9;
* the `store_value[0] = store_pc * (pc + jmp_offset2 - c_0) + c_0`
  expression with `store_pc = 1`: rd ← `pc + jmp_offset2 = pc + 4`
  (independent of `c_0`);
* the Zisk-opcode-ID literal `OP_COPYB = 1` that `transpile_JALR`
  emits;
* internal-op-1 constraints 9/16/18 that force `c = b` and `flag = 0`;
* constraint 19 (`flag * set_pc = 0`) consistency: with `set_pc = 1`,
  this forces `flag = 0`, reinforcing constraint 18's conclusion.

Concrete witness: `JALR x1, x2, +20` at `pc = 100`, with
`x2 = 0x80` (= 128). Expected results: `next_pc = 128 + 20 = 148`,
`x1 = 104` (= 100 + 4).

All `example`s use `decide` — the trace is fully concrete, no free
variables. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.JALR

open Goldilocks
open ZiskFv.Trusted

section TakenJump

/- Witness row: JALR x1, x2, +20 at pc = 100, x2 = 128. The row is
   internal-op-1 (copyb): `c = b = x2 = 128`. With `set_pc = 1`, the PC
   handshake yields `next_pc = c_0 + jmp_offset1 = 128 + 20 = 148`.
   With `store_pc = 1`, rd (= x1) receives `pc + 4 = 104`.  -/

@[simp] def jalr_pc : FGL := 100
@[simp] def jalr_a_lo : FGL := 0xFFFFFFFE       -- JALR_MASK low lane (cosmetic)
@[simp] def jalr_a_hi : FGL := 0xFFFFFFFF
@[simp] def jalr_b_lo : FGL := 128              -- rs1 = x2 low lane
@[simp] def jalr_b_hi : FGL := 0
@[simp] def jalr_c_lo : FGL := 128              -- c = b via constraint 9
@[simp] def jalr_c_hi : FGL := 0
@[simp] def jalr_flag : FGL := 0                -- flag = 0 via constraint 18
@[simp] def jalr_set_pc : FGL := 1              -- JALR routes next-pc via c
@[simp] def jalr_store_pc : FGL := 1            -- rd ← pc + 4
@[simp] def jalr_jmp_offset1 : FGL := 20        -- imm12
@[simp] def jalr_jmp_offset2 : FGL := 4         -- link offset
@[simp] def jalr_is_external_op : FGL := 0      -- Internal
@[simp] def jalr_op : FGL := 1                  -- OP_COPYB
@[simp] def jalr_m32 : FGL := 0

/-- Next-pc from the handshake formula (set_pc = 1, flag = 0):
    `set_pc * (c_0 + jmp_offset1) + (1 - set_pc) * (pc + jmp_offset2)
    + flag * (jmp_offset1 - jmp_offset2)
    = 1 * (128 + 20) + 0 + 0 * (20 - 4) = 148`. -/
example :
    jalr_set_pc * (jalr_c_lo + jalr_jmp_offset1)
      + (1 - jalr_set_pc) * (jalr_pc + jalr_jmp_offset2)
      + jalr_flag * (jalr_jmp_offset1 - jalr_jmp_offset2)
      = (148 : FGL) := by decide

/-- Direct PC-advance form: `next_pc = b_0 + jmp_offset1 = 128 + 20 = 148`. -/
example :
    jalr_b_lo + jalr_jmp_offset1 = (148 : FGL) := by decide

/-- Store-value expression (`main.pil:311`): `store_pc * (pc + jmp_offset2
    - c_0) + c_0 = 1 * (100 + 4 - 128) + 128 = 104`. The `c_0` cancels
    thanks to `store_pc = 1`, leaving `pc + jmp_offset2 = 104`. This is
    the link address written to rd. -/
example :
    jalr_store_pc * (jalr_pc + jalr_jmp_offset2 - jalr_c_lo) + jalr_c_lo
      = (104 : FGL) := by decide

/-- Consistency with `OP_COPYB` literal. -/
example : jalr_op = OP_COPYB := by decide

/-- `flag` boolean-ness. -/
example : jalr_flag * (1 - jalr_flag) = (0 : FGL) := by decide

/-- `is_external_op` boolean-ness. -/
example : jalr_is_external_op * (1 - jalr_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness (constraint 19): with `set_pc = 1`,
    this forces `flag = 0`. -/
example : jalr_flag * jalr_set_pc = (0 : FGL) := by decide

/-- Constraint 9 (internal op=1 copies b_0 to c_0):
    `(1 - ext) * op * (b_0 - c_0) = 0`. -/
example :
    (1 - jalr_is_external_op) * jalr_op * (jalr_b_lo - jalr_c_lo)
      = (0 : FGL) := by decide

/-- Constraint 16 (internal op=1 copies b_1 to c_1):
    `(1 - ext) * op * (b_1 - c_1) = 0`. -/
example :
    (1 - jalr_is_external_op) * jalr_op * (jalr_b_hi - jalr_c_hi)
      = (0 : FGL) := by decide

/-- Constraint 18 (internal op=1 clears flag):
    `(1 - ext) * op * flag = 0`. -/
example :
    (1 - jalr_is_external_op) * jalr_op * jalr_flag = (0 : FGL) := by decide

end TakenJump

-- Phase 4.5 Track D: additional edge-case fixture.

section ZeroBase

/- Witness row: JALR x1, x0, +0 at pc = 100. rs1 = 0, imm = 0 ⇒
   next_pc = 0 (zeros the PC). Link write: rd = pc + 4 = 104. -/

@[simp] def jalr_pc : FGL := 100
@[simp] def jalr_b_lo : FGL := 0
@[simp] def jalr_b_hi : FGL := 0
@[simp] def jalr_c_lo : FGL := 0
@[simp] def jalr_c_hi : FGL := 0
@[simp] def jalr_flag : FGL := 0
@[simp] def jalr_set_pc : FGL := 1
@[simp] def jalr_store_pc : FGL := 1
@[simp] def jalr_jmp_offset1 : FGL := 0
@[simp] def jalr_jmp_offset2 : FGL := 4

/-- `next_pc = c_0 + jmp_offset1 = 0 + 0 = 0`. -/
example :
    jalr_set_pc * (jalr_c_lo + jalr_jmp_offset1)
      + (1 - jalr_set_pc) * (jalr_pc + jalr_jmp_offset2)
      + jalr_flag * (jalr_jmp_offset1 - jalr_jmp_offset2)
      = (0 : FGL) := by decide

/-- Link write: `pc + jmp_offset2 = 104`, independent of `c_0`. -/
example :
    jalr_store_pc * (jalr_pc + jalr_jmp_offset2 - jalr_c_lo) + jalr_c_lo
      = (104 : FGL) := by decide

end ZeroBase

end ZiskFv.GoldenTraces.JALR
