import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.ALUITypeArchetype

/-!
Compositional SLTIU spec. Thin specialization of
`Tactics.ALUITypeArchetype` at `opcode_lit = OP_LTU = 6` (shared with
BLTU / BGEU / SLTU).
-/

namespace ZiskFv.Circuit.Sltiu

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[simp]
def main_row_in_sltiu_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_itype_mode m r_main OP_LTU

@[simp]
def sltiu_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_itype_archetype_circuit_holds m r_main bus_entry OP_LTU

lemma sltiu_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : sltiu_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_itype_archetype_c_bus_match m r_main bus_entry OP_LTU h

end ZiskFv.Circuit.Sltiu
