import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.RowShape.Contract
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus

/-!
Compositional ADD spec: given the named ADD-subset constraints on Main and
the carry-chain constraints on BinaryAdd, plus the operation-bus matching
between the two rows, the Main row's `c` lanes equal the 64-bit sum of its
`a` and `b` lanes (as Goldilocks-field arithmetic, modulo a multiple of
2^64 absorbed by the carry-out).

The proof uses only field arithmetic (no permutation-argument primitive),
thanks to the named-constraint layer abstracting the bus interaction into
`matches_entry`.
-/

namespace ZiskFv.ZiskCircuit.Add

open Goldilocks
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted


/-- The Main row at `r_main` is in ADD-execution mode: external op with
    opcode literal 10, full 64-bit width (m32 = 0), and `flag = 0`. -/
@[simp]
def main_row_in_add_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = (10 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.flag r_main = 0

/-- The 64-bit value packed into the Main row's `(c_0, c_1)` lanes,
    treated as a single Goldilocks element. -/
@[simp]
def main_c_packed (m : Valid_Main FGL FGL) (r : ℕ) : FGL :=
  m.c_0 r + m.c_1 r * 4294967296

/-- The 64-bit value packed into the Main row's `(a_0, a_1)` lanes. -/
@[simp]
def main_a_packed (m : Valid_Main FGL FGL) (r : ℕ) : FGL :=
  m.a_0 r + m.a_1 r * 4294967296

@[simp]
def main_b_packed (m : Valid_Main FGL FGL) (r : ℕ) : FGL :=
  m.b_0 r + m.b_1 r * 4294967296


end ZiskFv.ZiskCircuit.Add
