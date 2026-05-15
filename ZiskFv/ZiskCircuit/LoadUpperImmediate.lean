import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.UTypeArchetype

/-!
Compositional LUI spec.

LUI has no secondary state-machine hop — the whole microinstruction is
handled by the Main AIR alone (internal `copyb` routing). Given the
named `lui_subset_holds` Main constraints and the mode witnesses
supplied by `transpile_LUI` (`op = OP_COPYB = 1`, `is_external_op = 0`,
`m32 = 0`, `set_pc = 0`, `store_pc = 0`), the next-row `pc` cell
equals `pc + jmp_offset2 = pc + 4`, and the store-value (rd) lanes
equal `(b_0, b_1) = (imm_lo, imm_hi)`.

This module wraps `Tactics.UTypeArchetype.lui_archetype_*` at the
per-opcode layer so reviewers see the archetype applied here.
-/

namespace ZiskFv.ZiskCircuit.LoadUpperImmediate

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Trusted
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compositional LUI theorem — next-pc advance.** The next-pc equals
    `pc + jmp_offset2`. Combined with `transpile_LUI`'s pinning
    `jmp_offset2 = 4`, this says LUI advances PC by 4. -/
lemma lui_pc_advance
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : lui_archetype_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset2 r_main :=
  lui_archetype_pc_advance m r_main next_pc h

/-- **Compositional LUI theorem — rd low lane.** The rd-write low lane
    (`store_value[0]`) equals `b_0 = imm_lo`. Combined with
    `transpile_LUI`'s pinning `b_lo = imm_lo`, this says the low 32
    bits of rd receive the low 32 bits of the LUI immediate
    (which is `imm[11:0] ++ 0#12` in Sail terms — 20 imm bits shifted
    left by 12 into a 32-bit lane). -/
lemma lui_store_value_lo
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : lui_archetype_circuit_holds m r_main next_pc) :
    m.store_pc r_main *
        (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
      + m.c_0 r_main
      = m.b_0 r_main :=
  lui_archetype_store_value_lo m r_main next_pc h

/-- **Compositional LUI theorem — rd high lane.** The rd-write high
    lane `(1 - store_pc) * c_1` equals `b_1 = imm_hi`. Combined with
    `transpile_LUI`'s pinning `b_hi = imm_hi`, this says the high 32
    bits of rd receive the sign-extension of the LUI immediate. -/
lemma lui_store_value_hi
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : lui_archetype_circuit_holds m r_main next_pc) :
    (1 - m.store_pc r_main) * m.c_1 r_main = m.b_1 r_main :=
  lui_archetype_store_value_hi m r_main next_pc h

end ZiskFv.ZiskCircuit.LoadUpperImmediate
