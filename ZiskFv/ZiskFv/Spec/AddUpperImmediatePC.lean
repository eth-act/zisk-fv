import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.UTypeArchetype

/-!
Compositional AUIPC spec (Phase 3C Track T-U2).

AUIPC has no secondary state-machine hop — the whole microinstruction
is handled by the Main AIR alone (internal `flag` routing). Given the
named `auipc_subset_holds` Main constraints and the mode witnesses
supplied by `transpile_AUIPC` (`op = OP_FLAG = 0`,
`is_external_op = 0`, `m32 = 0`, `set_pc = 0`, `store_pc = 1`), the
next-row `pc` cell equals `pc + jmp_offset1 = pc + 4`, and the
store-value low lane equals `pc + jmp_offset2 = pc + imm`.

AUIPC differs from LUI only in the internal-op discriminant and the
routing of the immediate: LUI carries it in `b` (so rd = `c = b = imm`
via `store_pc = 0`), while AUIPC carries it in `jmp_offset2` (so
rd = `pc + jmp_offset2` via `store_pc = 1` with `c = 0` from
constraint 8). Both opcodes consume a single Main row with no
operation-bus entry.
-/

namespace ZiskFv.Spec.AddUpperImmediatePC

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Trusted
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compositional AUIPC theorem — next-pc advance.** The next-pc
    equals `pc + jmp_offset1`. Under `transpile_AUIPC`'s pinning
    `jmp_offset1 = 4`, this gives `pc + 4`.

    Note that AUIPC's `jmp_offset2` carries the immediate, not the
    fall-through offset — `transpile_AUIPC`'s `j(4, imm)` call inverts
    the `j1/j2` assignment relative to JAL's `j(imm, 4)`. The PC
    handshake's `flag * (jmp_offset1 - jmp_offset2)` term cancels the
    `jmp_offset2` contribution, leaving `pc + jmp_offset1 = pc + 4`. -/
theorem auipc_pc_advance
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main :=
  auipc_archetype_pc_advance m r_main next_pc h

/-- **Compositional AUIPC theorem — rd low lane.** The rd-write low
    lane (`store_value[0]`) equals `pc + jmp_offset2 = pc + imm`. -/
theorem auipc_store_value_lo
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    m.store_pc r_main *
        (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
      + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main :=
  auipc_archetype_store_value_lo m r_main next_pc h

/-- **Compositional AUIPC theorem — rd high lane.** The rd-write high
    lane `(1 - store_pc) * c_1` is zero because `store_pc = 1` zeros
    the gate. The full 64-bit `pc + imm` identity on the high lane is
    carried separately by the store-PC mechanics in the downstream
    memory-bus emission (high lane is the pc-high lane, not a direct
    column, for AUIPC). -/
theorem auipc_store_value_hi
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    (1 - m.store_pc r_main) * m.c_1 r_main = 0 :=
  auipc_archetype_store_value_hi m r_main next_pc h

end ZiskFv.Spec.AddUpperImmediatePC
