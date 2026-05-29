import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Tactics.ALUITypeArchetype

/-!
Compositional SLTI spec. Thin specialization of
`Tactics.ALUITypeArchetype` at `opcode_lit = OP_LT = 7` (shared with
BLT / BGE / SLT; the same Binary-SM opcode computes signed `a < b`,
with SLTI materializing the verdict into `c` via an immediate-form
microinstruction).
-/

namespace ZiskFv.ZiskCircuit.Slti

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype


@[simp]
def main_row_in_slti_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_alu_itype_mode m r_main OP_LT

@[simp]
def slti_circuit_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  alu_itype_archetype_circuit_holds m r_main bus_entry OP_LT

lemma slti_compositional
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : slti_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  alu_itype_archetype_c_bus_match m r_main bus_entry OP_LT h

end ZiskFv.ZiskCircuit.Slti
