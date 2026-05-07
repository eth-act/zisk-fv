import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.RTypeWArchetype

/-!
Compositional ADDW spec.

Thin specialization of `Tactics.RTypeWArchetype` at
`opcode_lit = OP_ADD_W = 26`, `m32 = 1`. Given the Main-side
boolean/disjointness constraints + RTYPEW-mode witnesses + bus-match
to an abstract Binary-SM bus entry, Main's packed `c` lanes equal
the bus entry's packed `c` lanes.

The Binary-SM-internal correctness (that `bus_entry.c_lo + c_hi *
2^32` equals `sign_extend 64 ((low32 rs1 + low32 rs2) as i32)`) is
delegated to the audit (same as MULW for the Arith-SM carry chains,
SLLW for the BinaryExtension bus, and the T-RT ALU RTYPE siblings
SUB/AND/OR/XOR for their Binary SMs).
-/

namespace ZiskFv.Circuit.Addw

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- ADDW's specialization of
    `RTypeWArchetype.main_row_in_rtypew_mode` at
    `opcode_lit = OP_ADD_W`. -/
@[simp]
def main_row_in_addw_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_rtypew_mode m r_main OP_ADD_W

/-- ADDW's circuit-holds predicate: specialization of
    `rtypew_archetype_circuit_holds` at `OP_ADD_W`. -/
@[simp]
def addw_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  rtypew_archetype_circuit_holds m r_main bus_entry OP_ADD_W

/-- **Compositional ADDW theorem.** Main's packed `c` equals the
    bus entry's packed `c` lanes. Instantiation of
    `rtypew_archetype_c_bus_match` at `OP_ADD_W`. -/
theorem addw_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : addw_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  rtypew_archetype_c_bus_match m r_main bus_entry OP_ADD_W h

end ZiskFv.Circuit.Addw
