import ZiskFv.AirsClean.ArithMul.Soundness
import ZiskFv.Airs.Arith.Mul

/-!
# `Valid_ArithMul` ↔ `ArithMulRow` compatibility

The `Valid_ArithMul` record exposes only even-indexed chunk
accessors as fields; odd-indexed accessors are reached through the
`Circuit.main circuit` lookup chain. The bridge below projects all
28 column slots into the Clean Component row layout, using the
named accessor wherever Valid_ArithMul provides one.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks

variable {C : Type → Type → Type} [Circuit FGL FGL C]

@[reducible]
def rowAt (v : ZiskFv.Airs.ArithMul.Valid_ArithMul C FGL FGL) (r : ℕ) :
    ArithMulRow FGL where
  chunks := {
    a_0 := v.a_0 r
    a_1 := Circuit.main v.circuit (id := 1) (column := 8) (row := r) (rotation := 0)
    a_2 := v.a_2 r
    a_3 := Circuit.main v.circuit (id := 1) (column := 10) (row := r) (rotation := 0)
    b_0 := v.b_0 r
    b_1 := Circuit.main v.circuit (id := 1) (column := 12) (row := r) (rotation := 0)
    b_2 := v.b_2 r
    b_3 := Circuit.main v.circuit (id := 1) (column := 14) (row := r) (rotation := 0)
    c_0 := v.c_0 r
    c_1 := Circuit.main v.circuit (id := 1) (column := 16) (row := r) (rotation := 0)
    c_2 := v.c_2 r
    c_3 := Circuit.main v.circuit (id := 1) (column := 18) (row := r) (rotation := 0)
    d_0 := v.d_0 r
    d_1 := Circuit.main v.circuit (id := 1) (column := 20) (row := r) (rotation := 0)
    d_2 := v.d_2 r
    d_3 := Circuit.main v.circuit (id := 1) (column := 22) (row := r) (rotation := 0)
  }
  flags := {
    na := v.na r
    nb := Circuit.main v.circuit (id := 1) (column := 24) (row := r) (rotation := 0)
    nr := v.nr r
    np := Circuit.main v.circuit (id := 1) (column := 26) (row := r) (rotation := 0)
    sext := v.sext r
    m32 := Circuit.main v.circuit (id := 1) (column := 28) (row := r) (rotation := 0)
    div := v.div r
    main_div := Circuit.main v.circuit (id := 1) (column := 33) (row := r) (rotation := 0)
    main_mul := v.main_mul r
    op := Circuit.main v.circuit (id := 1) (column := 39) (row := r) (rotation := 0)
    bus_res1 := v.bus_res1 r
    multiplicity := Circuit.main v.circuit (id := 1) (column := 41) (row := r) (rotation := 0)
  }

end ZiskFv.AirsClean.ArithMul
