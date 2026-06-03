import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ALURTypeArchetype

/-!
Compositional OR spec.

Thin specialization of `Tactics.ALURTypeArchetype` at
`opcode_lit = OP_OR = 15`. Identical structure to `Spec/Sub.lean`.
-/

namespace ZiskFv.ZiskCircuit.Or

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype


@[simp]
def main_row_in_or_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_rtype_mode m r_main OP_OR

@[simp]
def or_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_rtype_archetype_circuit_holds m r_main bus_entry OP_OR

lemma or_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : or_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry OP_OR h

end ZiskFv.ZiskCircuit.Or
