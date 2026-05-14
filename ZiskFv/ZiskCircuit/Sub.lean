import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ALURTypeArchetype

/-!
Compositional SUB spec.

Thin specialization of `Tactics.ALURTypeArchetype` at
`opcode_lit = OP_SUB = 11`. Given the Main-side boolean/disjointness
constraints + mode witnesses + bus-match to an abstract bus entry,
Main's packed `c` lanes equal the bus entry's packed `c` lanes.

The Binary-SM-internal correctness (that `bus_entry.c_lo + c_hi * 2^32`
equals `rs1 - rs2` as `BitVec 64`) is delegated to the audit —
identical treatment to how MULH / MULHU / MULHSU defer the high-half
selection.
-/

namespace ZiskFv.ZiskCircuit.Sub

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- SUB's specialization of
    `ALURTypeArchetype.main_row_in_alu_rtype_mode` at
    `opcode_lit = OP_SUB`. -/
@[simp]
def main_row_in_sub_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_rtype_mode m r_main OP_SUB

/-- SUB's circuit-holds predicate: specialization of
    `alu_rtype_archetype_circuit_holds` at `OP_SUB`. -/
@[simp]
def sub_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_rtype_archetype_circuit_holds m r_main bus_entry OP_SUB

/-- **Compositional SUB theorem.** Main's packed `c` equals the bus
    entry's packed `c` lanes. Instantiation of
    `alu_rtype_archetype_c_bus_match` at `OP_SUB`. -/
lemma sub_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sub_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry OP_SUB h

end ZiskFv.ZiskCircuit.Sub
