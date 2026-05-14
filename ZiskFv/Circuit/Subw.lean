import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.RTypeWArchetype

/-!
Compositional SUBW spec.

Thin specialization of `Tactics.RTypeWArchetype` at
`opcode_lit = OP_SUB_W = 27`, `m32 = 1`. Identical structure to
`Spec/Addw.lean` modulo the opcode literal.
-/

namespace ZiskFv.Circuit.Subw

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[simp]
def main_row_in_subw_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  main_row_in_rtypew_mode m r_main OP_SUB_W

@[simp]
def subw_circuit_holds
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL) : Prop :=
  rtypew_archetype_circuit_holds m r_main bus_entry OP_SUB_W

lemma subw_compositional
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h : subw_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  rtypew_archetype_c_bus_match m r_main bus_entry OP_SUB_W h

end ZiskFv.Circuit.Subw
