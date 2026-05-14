import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ALURTypeArchetype

/-!
Compositional SLT spec.

Thin specialization of `Tactics.ALURTypeArchetype` at
`opcode_lit = OP_LT = 7` (shared with BLT / BGE — the same Binary-SM
opcode computes the boolean `a < b` (signed); SLT materializes it into
`c`, while branches route it into PC dispatch).

The Binary-SM-internal correctness (that `bus_entry.c_lo / c_hi` pack
a 64-bit 0/1 matching Sail's `BitVec.slt`) is delegated to the audit.
-/

namespace ZiskFv.Circuit.Slt

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[simp]
def main_row_in_slt_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_rtype_mode m r_main OP_LT

@[simp]
def slt_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_rtype_archetype_circuit_holds m r_main bus_entry OP_LT

lemma slt_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : slt_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry OP_LT h

end ZiskFv.Circuit.Slt
