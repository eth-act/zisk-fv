import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ALURTypeArchetype

/-!
Compositional AND spec.

Thin specialization of `Tactics.ALURTypeArchetype` at
`opcode_lit = OP_AND = 14`. Identical structure to `Spec/Sub.lean`.
-/

namespace ZiskFv.Circuit.And

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[simp]
def main_row_in_and_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_rtype_mode m r_main OP_AND

@[simp]
def and_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_rtype_archetype_circuit_holds m r_main bus_entry OP_AND

lemma and_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : and_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry OP_AND h

end ZiskFv.Circuit.And
