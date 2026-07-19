import ZiskFv.AirsClean.ArithMul.Constraints
import ZiskFv.AirsClean.ArithDiv.Constraints

/-! Additive completed generated Arith mirrors. Existing lookup-aware circuit tuple
shapes are preserved for downstream compatibility; these canonical complete variants
append exactly the generated constraints audited in refactor 11. -/

namespace ZiskFv.AirsClean.ArithMul
open Goldilocks Circuit
@[circuit_norm] def mainComplete (row : Var ArithMulRow FGL) : Circuit FGL Unit := do
  mainWithArithTable row
  -- Mirror of generated `constraint_2_every_row`; PIL `arith.pil:48`.
  assertZero (row.flags.main_mul * row.flags.main_div)
  -- Mirror of generated `constraint_40_every_row`; PIL `arith.pil:238`.
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  -- Mirror of generated `constraint_41_every_row`; PIL `arith.pil:239`.
  assertZero (row.flags.na * (1 - row.flags.na))
  -- Mirror of generated `constraint_42_every_row`; PIL `arith.pil:240`.
  assertZero (row.flags.nb * (1 - row.flags.nb))
  -- Mirror of generated `constraint_43_every_row`; PIL `arith.pil:241`.
  assertZero (row.flags.nr * (1 - row.flags.nr))
  -- Mirror of generated `constraint_44_every_row`; PIL `arith.pil:242`.
  assertZero (row.flags.np * (1 - row.flags.np))
  -- Mirror of generated `constraint_45_every_row`; PIL `arith.pil:243`.
  assertZero (row.flags.sext * (1 - row.flags.sext))
end ZiskFv.AirsClean.ArithMul

namespace ZiskFv.AirsClean.ArithMul
open Goldilocks Circuit
@[circuit_norm] def sharedMainComplete (row : Var ArithMulRow FGL) : Circuit FGL Unit := do
  mainWithArithTable row
  -- Generated constraints 0--5 (`constraint_N_every_row`, PIL `arith.pil:46-53`).
  assertZero (row.flags.main_div * (row.flags.main_div - 1))
  assertZero (row.flags.main_mul * (row.flags.main_mul - 1))
  assertZero (row.flags.main_mul * row.flags.main_div)
  assertZero (row.flags.signed * (1 - row.flags.signed))
  assertZero (row.flags.div_by_zero * (1 - row.flags.div_by_zero))
  assertZero (row.flags.div_overflow * (1 - row.flags.div_overflow))
  -- Generated boundary constraints 9--24 (`constraint_N_every_row`, PIL `arith.pil:130-141`).
  assertZero (row.flags.div_by_zero * row.chunks.b_0)
  assertZero (row.flags.div_by_zero * row.chunks.b_1)
  assertZero (row.flags.div_by_zero * row.chunks.b_2)
  assertZero (row.flags.div_by_zero * row.chunks.b_3)
  assertZero (row.flags.div_by_zero * (row.chunks.a_0 - 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_1 - 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_2 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_3 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_0 - 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_1 - 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_2 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_3 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * row.chunks.c_0)
  assertZero (row.flags.div_overflow * (row.chunks.c_1 - row.flags.m32 * 32768))
  assertZero (row.flags.div_overflow * row.chunks.c_2)
  assertZero (row.flags.div_overflow * (row.chunks.c_3 - (1 - row.flags.m32) * 32768))
  -- Generated inverse/scope constraints 25--30 (`constraint_N_every_row`, PIL `arith.pil:143-153`).
  assertZero ((row.flags.div - row.flags.div_by_zero) *
    (1 - row.carries.inv_sum_all_bs *
      (((row.chunks.b_0 + row.chunks.b_1) + row.chunks.b_2) + row.chunks.b_3)))
  assertZero (row.flags.div_by_zero * (1 - row.flags.div))
  assertZero (row.flags.div_overflow * (1 - row.flags.div))
  assertZero (row.flags.div_overflow * (1 - row.flags.signed))
  assertZero (row.flags.div_overflow * row.flags.div_by_zero)
  assertZero (row.flags.div_by_zero * row.flags.div_overflow)
  -- Generated mode booleans 39--45 (`constraint_N_every_row`, PIL `arith.pil:237-243`).
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  -- Generated result mux 46 (`constraint_46_every_row`, PIL `arith.pil:263`).
  assertZero (row.flags.bus_res1 -
    (row.flags.sext * 4294967295 + (1 - row.flags.m32) *
      (((1 - row.flags.main_mul - row.flags.main_div) *
          (row.chunks.d_2 + row.chunks.d_3 * 65536)) +
       row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
       row.flags.main_div * (row.chunks.a_2 + row.chunks.a_3 * 65536))))
  -- Generated W-mode lane constraints 47--48 (`constraint_N_every_row`, PIL `arith.pil:265-266`).
  assertZero (row.flags.m32 *
    (row.flags.div * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
      (1 - row.flags.div) * (row.chunks.a_2 + row.chunks.a_3 * 65536)))
  assertZero (row.flags.m32 * (row.chunks.b_2 + row.chunks.b_3 * 65536))

/-- Forget the appended complete local assertions while retaining the lookup-aware
base provider constraints. -/
theorem sharedMainComplete_base_soundness
    (offset : ℕ) (env : Environment FGL) (row : Var ArithMulRow FGL)
    (h : ConstraintsHold.Soundness env ((sharedMainComplete row).operations offset)) :
    ConstraintsHold.Soundness env ((mainWithArithTable row).operations offset) := by
  simp only [sharedMainComplete, mainWithArithTable, main, circuit_norm] at h ⊢
  rcases h with
    ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38,
      h46, hlookup, hra1, hrb1, hrc1, hrd1, hra3, hrb3, hrc3, hrd3,
      ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
      hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3,
      hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6, _⟩
  exact ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38,
    h46, hlookup, hra1, hrb1, hrc1, hrd1, hra3, hrb3, hrc3, hrd3,
    ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
    hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3,
    hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6⟩
end ZiskFv.AirsClean.ArithMul

namespace ZiskFv.AirsClean.ArithDiv
open Goldilocks Circuit
@[circuit_norm] def mainComplete (row : Var ArithDivRow FGL) : Circuit FGL Unit := do
  mainWithArithTable row
  -- Generated constraints 0--5 (`constraint_N_every_row`, PIL `arith.pil:46-53`).
  assertZero (row.flags.main_div * (row.flags.main_div - 1))
  assertZero (row.flags.main_mul * (row.flags.main_mul - 1))
  assertZero (row.flags.main_mul * row.flags.main_div)
  assertZero (row.flags.signed * (1 - row.flags.signed))
  assertZero (row.flags.div_by_zero * (1 - row.flags.div_by_zero))
  assertZero (row.flags.div_overflow * (1 - row.flags.div_overflow))
  -- Generated boundary constraints 9--24 (`constraint_N_every_row`, PIL `arith.pil:130-141`).
  assertZero (row.flags.div_by_zero * row.chunks.b_0)
  assertZero (row.flags.div_by_zero * row.chunks.b_1)
  assertZero (row.flags.div_by_zero * row.chunks.b_2)
  assertZero (row.flags.div_by_zero * row.chunks.b_3)
  assertZero (row.flags.div_by_zero * (row.chunks.a_0 - 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_1 - 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_2 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_by_zero * (row.chunks.a_3 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_0 - 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_1 - 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_2 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * (row.chunks.b_3 - (1 - row.flags.m32) * 65535))
  assertZero (row.flags.div_overflow * row.chunks.c_0)
  assertZero (row.flags.div_overflow * (row.chunks.c_1 - row.flags.m32 * 32768))
  assertZero (row.flags.div_overflow * row.chunks.c_2)
  assertZero (row.flags.div_overflow * (row.chunks.c_3 - (1 - row.flags.m32) * 32768))
  -- Generated inverse/scope constraints 25--30 (`constraint_N_every_row`, PIL `arith.pil:143-153`).
  assertZero ((row.flags.div - row.flags.div_by_zero) *
    (1 - row.aux.inv_sum_all_bs *
      (((row.chunks.b_0 + row.chunks.b_1) + row.chunks.b_2) + row.chunks.b_3)))
  assertZero (row.flags.div_by_zero * (1 - row.flags.div))
  assertZero (row.flags.div_overflow * (1 - row.flags.div))
  assertZero (row.flags.div_overflow * (1 - row.flags.signed))
  assertZero (row.flags.div_overflow * row.flags.div_by_zero)
  assertZero (row.flags.div_by_zero * row.flags.div_overflow)
  -- Generated mode booleans 39--45 (`constraint_N_every_row`, PIL `arith.pil:237-243`).
  assertZero (row.flags.div * (1 - row.flags.div))
  assertZero (row.flags.m32 * (1 - row.flags.m32))
  assertZero (row.flags.na * (1 - row.flags.na))
  assertZero (row.flags.nb * (1 - row.flags.nb))
  assertZero (row.flags.nr * (1 - row.flags.nr))
  assertZero (row.flags.np * (1 - row.flags.np))
  assertZero (row.flags.sext * (1 - row.flags.sext))
  -- Generated result mux 46 (`constraint_46_every_row`, PIL `arith.pil:263`).
  assertZero (row.flags.bus_res1 -
    (row.flags.sext * 4294967295 + (1 - row.flags.m32) *
      (((1 - row.flags.main_mul - row.flags.main_div) *
          (row.chunks.d_2 + row.chunks.d_3 * 65536)) +
       row.flags.main_mul * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
       row.flags.main_div * (row.chunks.a_2 + row.chunks.a_3 * 65536))))
  -- Generated W-mode lane constraints 47--48 (`constraint_N_every_row`, PIL `arith.pil:265-266`).
  assertZero (row.flags.m32 *
    (row.flags.div * (row.chunks.c_2 + row.chunks.c_3 * 65536) +
      (1 - row.flags.div) * (row.chunks.a_2 + row.chunks.a_3 * 65536)))
  assertZero (row.flags.m32 * (row.chunks.b_2 + row.chunks.b_3 * 65536))
end ZiskFv.AirsClean.ArithDiv
