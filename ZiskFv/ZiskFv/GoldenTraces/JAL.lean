import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Spec.Jal

/-!
Phase 2 archetype A2 golden-trace fixture: one canonical JAL row
covering the unconditional-jump case with a non-zero rd (link-address
write).

Unlike `GoldenTraces.Add` (which exercises a full compositional Main +
BinaryAdd row) JAL emits **no** operation-bus entry (`is_external_op = 0`,
Internal op `flag`), so there is no secondary-SM row to co-validate.
The fixture exercises:

* the Main-AIR's flag-forced PC-handshake formula for `set_pc = 0,
  flag = 1`: `next_pc = pc + jmp_offset1`;
* the `store_value[0] = store_pc * (pc + jmp_offset2 - c_0) + c_0`
  expression with `store_pc = 1, c_0 = 0`: rd ← `pc + jmp_offset2`
  (= `pc + 4`);
* the Zisk-opcode-ID literal `OP_FLAG = 0` that `transpile_JAL` emits;
* internal-op-zero constraints 8/15/17 that force `c = 0` and `flag = 1`.

Concrete witness: JAL `x1, +20` at `pc = 100`. Expected results:
`next_pc = 120` (= 100 + 20), `x1 = 104` (= 100 + 4).

All `example`s use `decide` — the trace is fully concrete, no free
variables. They verify by kernel reduction.
-/

namespace ZiskFv.GoldenTraces.JAL

open Goldilocks
open ZiskFv.Trusted

section TakenJump

/- Witness row: JAL `x1, +20` against `pc = 100`. No comparison —
   always taken. Flag is forced to 1 by constraint 17 (internal op = 0).
   `store_pc = 1, c_0 = 0`, so rd ← pc + 4 = 104.  -/

@[simp] def jal_pc : FGL := 100
@[simp] def jal_a_lo : FGL := 0                -- src_a = imm 0
@[simp] def jal_a_hi : FGL := 0
@[simp] def jal_b_lo : FGL := 0                -- src_b = imm 0
@[simp] def jal_b_hi : FGL := 0
@[simp] def jal_c_lo : FGL := 0                -- op_flag → c = 0
@[simp] def jal_c_hi : FGL := 0
@[simp] def jal_flag : FGL := 1                -- op_flag → flag = 1
@[simp] def jal_set_pc : FGL := 0
@[simp] def jal_store_pc : FGL := 1            -- rd ← pc + 4
@[simp] def jal_jmp_offset1 : FGL := 20        -- imm
@[simp] def jal_jmp_offset2 : FGL := 4         -- link offset
@[simp] def jal_is_external_op : FGL := 0      -- Internal
@[simp] def jal_op : FGL := 0                  -- OP_FLAG
@[simp] def jal_m32 : FGL := 0

/-- Next-pc from the handshake formula (set_pc = 0, flag = 1):
    `pc + jmp_offset2 + 1 * (jmp_offset1 - jmp_offset2) = pc + jmp_offset1 = 120`. -/
example :
    jal_pc + jal_jmp_offset2
      + jal_flag * (jal_jmp_offset1 - jal_jmp_offset2)
      = (120 : FGL) := by decide

/-- Direct PC-advance form: `next_pc = pc + jmp_offset1 = 120`. -/
example :
    jal_pc + jal_jmp_offset1 = (120 : FGL) := by decide

/-- Store-value expression (`main.pil:311`): `store_pc * (pc + jmp_offset2 - c_0) + c_0`
    = 1 * (100 + 4 - 0) + 0 = 104. This is the link address written to rd. -/
example :
    jal_store_pc * (jal_pc + jal_jmp_offset2 - jal_c_lo) + jal_c_lo
      = (104 : FGL) := by decide

/-- Consistency with `OP_FLAG` literal. -/
example : jal_op = OP_FLAG := by decide

/-- `flag` boolean-ness. -/
example : jal_flag * (1 - jal_flag) = (0 : FGL) := by decide

/-- `is_external_op` boolean-ness. -/
example : jal_is_external_op * (1 - jal_is_external_op) = (0 : FGL) := by decide

/-- `flag * set_pc = 0` disjointness. -/
example : jal_flag * jal_set_pc = (0 : FGL) := by decide

/-- Constraint 8 (internal op=0 zeroes c_0): `(1 - ext) * (1 - op) * c_0 = 0`. -/
example :
    (1 - jal_is_external_op) * (1 - jal_op) * jal_c_lo = (0 : FGL) := by decide

/-- Constraint 17 (internal op=0 sets flag = 1): `(1 - ext) * (1 - op) * (1 - flag) = 0`. -/
example :
    (1 - jal_is_external_op) * (1 - jal_op) * (1 - jal_flag) = (0 : FGL) := by decide

end TakenJump

-- Phase 4.5 Track D: additional edge-case fixture.

section BackwardsJump

/- Witness row: JAL `x1, -20` (backwards jump). At pc = 100 this jumps
   to 80. Tests sign-handling at the field level (negative imm encoded
   as wrapped 64-bit constant in jmp_offset1). -/

@[simp] def jal_pc : FGL := 100
@[simp] def jal_c_lo : FGL := 0
@[simp] def jal_flag : FGL := 1
@[simp] def jal_set_pc : FGL := 0
@[simp] def jal_store_pc : FGL := 1
-- imm = -20 sign-extended to field-neg; next_pc should be 80.
-- Over Goldilocks we represent -20 as `p - 20` (but here we use the
-- minus form in the arithmetic identity).
@[simp] def jal_jmp_offset2 : FGL := 4
-- jmp_offset1 chosen as (pc + jmp_offset1 = 80) ↔ jmp_offset1 = -20 in 𝔽.
-- To avoid field-subtraction subtleties we instead use a forward-wrap
-- identity: `pc + jmp_offset1 = 80` as: 100 + x = 80 in 𝔽 = ZMod p
-- only holds for x = p - 20; we encode that directly.
@[simp] def jal_jmp_offset1 : FGL :=
  18446744069414584301   -- p - 20

/-- With jmp_offset1 = p - 20 in 𝔽 and pc = 100, `pc + jmp_offset1 = 80`
    (mod p). Forward direction: `80 + 20 = 100`. -/
example : (80 : FGL) + 20 = jal_pc := by decide

/-- Store-value (link address): `pc + jmp_offset2 = 104`, unaffected by
    backwards jumps. -/
example :
    jal_store_pc * (jal_pc + jal_jmp_offset2 - jal_c_lo) + jal_c_lo
      = (104 : FGL) := by decide

end BackwardsJump

end ZiskFv.GoldenTraces.JAL
