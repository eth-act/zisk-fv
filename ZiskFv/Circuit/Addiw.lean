import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.RTypeWArchetype

/-!
Compositional ADDIW spec (Phase 3C T-W).

Thin specialization of `Tactics.RTypeWArchetype` at
`opcode_lit = OP_ADD_W = 26`, `m32 = 1` — the **same** bus-literal
pair ADDW uses. The transpiler routing
(`riscv2zisk_context.rs:184-194`) dispatches ADDIW through
`immediate_op(..., "add_w", 4)`, which differs from ADDW only in
the source-b slot (immediate vs. register); the Main-AIR row shape
for the operation bus is identical modulo the `b_lo`/`b_hi`
construction.

The ADDW/ADDIW distinction on the Sail side is carried by the
`instruction.ADDIW (imm, r1, rd)` vs `instruction.RTYPEW (..., ropw.ADDW)`
constructors; the circuit-level `c`-lane bus-match identity is the
same either way.
-/

namespace ZiskFv.Circuit.Addiw

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- ADDIW's mode predicate: specialization of
    `RTypeWArchetype.main_row_in_rtypew_mode` at
    `opcode_lit = OP_ADD_W`. Same opcode as ADDW — the difference is
    the transpiler's source-b routing (imm vs. reg), not the row
    shape. -/
@[simp]
def main_row_in_addiw_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_rtypew_mode m r_main OP_ADD_W

/-- ADDIW's circuit-holds predicate: specialization of
    `rtypew_archetype_circuit_holds` at `OP_ADD_W`. -/
@[simp]
def addiw_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  rtypew_archetype_circuit_holds m r_main bus_entry OP_ADD_W

/-- **Compositional ADDIW theorem.** Main's packed `c` equals the
    bus entry's packed `c` lanes. Same identity as
    `addw_compositional`; the difference is which transpile axiom
    populated the Main row's `b` lanes (here: the sign-extended
    12-bit immediate). -/
theorem addiw_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : addiw_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  rtypew_archetype_c_bus_match m r_main bus_entry OP_ADD_W h

end ZiskFv.Circuit.Addiw
