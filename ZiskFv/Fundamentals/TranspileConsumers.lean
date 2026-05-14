import Mathlib

import ZiskFv.Fundamentals.Transpiler

/-!
# Transpile-axiom consumers

One trivial `theorem transpile_<OP>_consumer` per transpile axiom.
Each invokes its axiom under the two mode-witness premises
(`is_external_op`, `op`) and extracts the first conjunct of the
resulting conjunction.

The point of this module is mechanical: ensure that each
`transpile_<OP>` axiom has at least one proof-level consumer, so
`#print axioms transpile_<OP>_consumer` reports the axiom as a
dependency. These consumers are not individually load-bearing for any
downstream equivalence proof — they are witnesses that the axiom shape
is *consumable*.
-/

namespace ZiskFv.Trusted

open Goldilocks
open ZiskFv.Airs.Main

/-- Consumer-witness for `transpile_ADD`. -/
theorem transpile_ADD_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (state : RV64State) (rs1 rs2 : Fin 32)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD → m.a_0 r_main = lane_lo (state.xreg rs1) :=
  fun h_p1 h_p2 =>
    (transpile_ADD m r_main state rs1 rs2 h_p1 h_p2).1

/-- Consumer-witness for `transpile_JAL`. -/
theorem transpile_JAL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_JAL m r_main _rd imm_offset _state h_p1 h_p2).1

/-- Consumer-witness for `transpile_JALR`. -/
theorem transpile_JALR_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_JALR m r_main rs1 _rd imm_offset state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SD`. -/
theorem transpile_SD_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SD m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SW`. -/
theorem transpile_SW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SW m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- Consumer-witness for `transpile_MUL`. -/
theorem transpile_MUL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MUL → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MUL m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_MULH`. -/
theorem transpile_MULH_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MULH → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MULH m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLLW`. -/
theorem transpile_SLLW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLLW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SH`. -/
theorem transpile_SH_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SH m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SB`. -/
theorem transpile_SB_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SB m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLL`. -/
theorem transpile_SLL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLL m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRL`. -/
theorem transpile_SRL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRL m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRA`. -/
theorem transpile_SRA_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRA m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLLI`. -/
theorem transpile_SLLI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLLI m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRLI`. -/
theorem transpile_SRLI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRLI m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRAI`. -/
theorem transpile_SRAI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRAI m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRLW`. -/
theorem transpile_SRLW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRLW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRAW`. -/
theorem transpile_SRAW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRAW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLLIW`. -/
theorem transpile_SLLIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLLIW m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRLIW`. -/
theorem transpile_SRLIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRLIW m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SRAIW`. -/
theorem transpile_SRAIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRAIW m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- Consumer-witness for `transpile_MULHU`. -/
theorem transpile_MULHU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MULUH → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MULHU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_MULHSU`. -/
theorem transpile_MULHSU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MULSUH → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MULHSU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_LUI`. -/
theorem transpile_LUI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_lo imm_hi : FGL) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LUI m r_main _rd imm_lo imm_hi _state h_p1 h_p2).1

/-- Consumer-witness for `transpile_AUIPC`. -/
theorem transpile_AUIPC_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_AUIPC m r_main _rd imm_offset _state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SUB`. -/
theorem transpile_SUB_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SUB → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SUB m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_AND`. -/
theorem transpile_AND_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_AND → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_AND m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_OR`. -/
theorem transpile_OR_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_OR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_OR m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_XOR`. -/
theorem transpile_XOR_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_XOR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_XOR m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLT`. -/
theorem transpile_SLT_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LT → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLT m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLTU`. -/
theorem transpile_SLTU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LTU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLTU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_ADDI`. -/
theorem transpile_ADDI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ADDI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_ANDI`. -/
theorem transpile_ANDI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_AND → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ANDI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_ORI`. -/
theorem transpile_ORI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_OR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ORI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_XORI`. -/
theorem transpile_XORI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_XOR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_XORI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLTI`. -/
theorem transpile_SLTI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LT → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLTI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SLTIU`. -/
theorem transpile_SLTIU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LTU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLTIU m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_ADDW`. -/
theorem transpile_ADDW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ADDW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_SUBW`. -/
theorem transpile_SUBW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SUB_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SUBW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_ADDIW`. -/
theorem transpile_ADDIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_lo imm_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ADDIW m r_main rs1 _rd imm_lo imm_hi state h_p1 h_p2).1

/-- Consumer-witness for `transpile_DIVUW`. -/
theorem transpile_DIVUW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIVU_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_DIVUW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_REMUW`. -/
theorem transpile_REMUW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REMU_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_REMUW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_DIVW`. -/
theorem transpile_DIVW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIV_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_DIVW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_REMW`. -/
theorem transpile_REMW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REM_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_REMW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_DIVU`. -/
theorem transpile_DIVU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIVU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_DIVU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_REMU`. -/
theorem transpile_REMU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REMU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_REMU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_DIV`. -/
theorem transpile_DIV_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIV → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_DIV m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- Consumer-witness for `transpile_REM`. -/
theorem transpile_REM_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REM → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_REM m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-! ## store_pc=1 PC bridges (TP-JAL / TP-JALR / TP-AUIPC)

    Each `transpile_PC_consumer_<OP>` lemma makes its corresponding
    `transpile_PC_for_<OP>` axiom load-bearing. Unlike the operand-axiom
    consumers above, the PC axioms have a single equality conclusion
    (not a conjunction), so the consumer simply re-exposes the axiom
    under its mode-witness premises. -/

/-- Consumer-witness for `transpile_PC_for_JAL`. -/
theorem transpile_PC_consumer_JAL
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (PC : BitVec 64)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG →
      (m.pc r_main).val = PC.toNat :=
  fun h_p1 h_p2 =>
    transpile_PC_for_JAL m r_main PC h_p1 h_p2

/-- Consumer-witness for `transpile_PC_for_JALR`. -/
theorem transpile_PC_consumer_JALR
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (PC : BitVec 64)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB →
      (m.pc r_main).val = PC.toNat :=
  fun h_p1 h_p2 =>
    transpile_PC_for_JALR m r_main PC h_p1 h_p2

/-- Consumer-witness for `transpile_PC_for_AUIPC`. -/
theorem transpile_PC_consumer_AUIPC
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (PC : BitVec 64)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG →
      (m.pc r_main).val = PC.toNat :=
  fun h_p1 h_p2 =>
    transpile_PC_for_AUIPC m r_main PC h_p1 h_p2

end ZiskFv.Trusted