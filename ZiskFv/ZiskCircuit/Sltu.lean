import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ALURTypeArchetype

/-!
Compositional SLTU spec.

Thin specialization of `Tactics.ALURTypeArchetype` at
`opcode_lit = OP_LTU = 6` (shared with BLTU / BGEU — unsigned
comparison, Binary SM).
-/

namespace ZiskFv.ZiskCircuit.Sltu

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[simp]
def main_row_in_sltu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_rtype_mode m r_main OP_LTU

@[simp]
def sltu_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_rtype_archetype_circuit_holds m r_main bus_entry OP_LTU

lemma sltu_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sltu_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_rtype_archetype_c_bus_match m r_main bus_entry OP_LTU h

end ZiskFv.ZiskCircuit.Sltu
