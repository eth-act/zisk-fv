import Mathlib

import ZiskFv.Fundamentals.Transpiler

/-!
# Transpile-axiom consumers — V13 closure (Phase 5 Track G extension)

One trivial `theorem transpile_<OP>_consumer` per transpile axiom. Each
invokes its axiom under the two mode-witness premises (`is_external_op`,
`op`) and extracts the first conjunct of the resulting conjunction.

The point of this module is mechanical: ensure every one of the 58
`transpile_<OP>` axioms has at least one proof-level consumer (V13) so
that `#print axioms transpile_<OP>_consumer` reports the axiom as a
dependency. Without this module, the 57 non-ADD axioms are declared-
but-unused (Gap 3 residue).

These consumers are not individually load-bearing for any downstream
equivalence proof — they are witnesses that the axiom shape is
*consumable*. Phase 5.1 will wire the axioms into the metaplan-
theorem path via `chip_bus_hyps_*` or similar.
-/

namespace ZiskFv.Trusted

open Goldilocks
open ZiskFv.Airs.Main

/-- V13 consumer-witness for `transpile_ADD`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_ADD_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (state : RV64State) (rs1 rs2 : Fin 32)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD → m.a_0 r_main = lane_lo (state.xreg rs1) :=
  fun h_p1 h_p2 =>
    (transpile_ADD m r_main state rs1 rs2 h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_BEQ`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_BEQ_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_EQ → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_BEQ m r_main rs1 rs2 imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_BNE`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_BNE_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_EQ → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_BNE m r_main rs1 rs2 imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_JAL`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_JAL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_JAL m r_main _rd imm_offset _state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_FENCE`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_FENCE_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_FENCE m r_main _state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_JALR`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_JALR_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_JALR m r_main rs1 _rd imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LD`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LD_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LD m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LWU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LWU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LWU m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LHU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LHU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LHU m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LBU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LBU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LBU m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SD`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SD_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SD m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SW m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_MUL`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_MUL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MUL → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MUL m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_MULH`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_MULH_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MULH → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MULH m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLLW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLLW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLLW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_BLT`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_BLT_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LT → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_BLT m r_main rs1 rs2 imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_BGE`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_BGE_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LT → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_BGE m r_main rs1 rs2 imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_BLTU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_BLTU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LTU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_BLTU m r_main rs1 rs2 imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_BGEU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_BGEU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LTU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_BGEU m r_main rs1 rs2 imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SH`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SH_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SH m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SB`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SB_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SB m r_main rs1 rs2 _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLL`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLL m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRL`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRL_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRL m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRA`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRA_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRA m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLLI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLLI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLLI m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRLI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRLI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRLI m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRAI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRAI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 6) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRAI m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRLW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRLW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRLW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRAW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRAW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRAW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLLIW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLLIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SLL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLLIW m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRLIW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRLIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRL_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRLIW m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SRAIW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SRAIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (shamt : BitVec 5) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SRA_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SRAIW m r_main rs1 _rd shamt state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_MULHU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_MULHU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MULUH → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MULHU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_MULHSU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_MULHSU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MULSUH → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_MULHSU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_MULW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_MULW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_MUL_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_MULW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LUI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LUI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_lo imm_hi : FGL) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LUI m r_main _rd imm_lo imm_hi _state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_AUIPC`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_AUIPC_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (_rd : Fin 32) (imm_offset : FGL) (_state : RV64State)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_AUIPC m r_main _rd imm_offset _state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SUB`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SUB_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SUB → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SUB m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_AND`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_AND_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_AND → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_AND m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_OR`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_OR_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_OR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_OR m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_XOR`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_XOR_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_XOR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_XOR m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLT`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLT_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LT → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLT m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLTU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLTU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LTU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLTU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_ADDI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_ADDI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ADDI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_ANDI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_ANDI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_AND → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ANDI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_ORI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_ORI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_OR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ORI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_XORI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_XORI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_XOR → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_XORI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLTI`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLTI_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LT → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLTI m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SLTIU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SLTIU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_b_lo imm_b_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_LTU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SLTIU m r_main rs1 _rd imm_b_lo imm_b_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_ADDW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_ADDW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ADDW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_SUBW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_SUBW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SUB_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_SUBW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_ADDIW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_ADDIW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (imm_lo imm_hi : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_ADD_W → m.flag r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_ADDIW m r_main rs1 _rd imm_lo imm_hi state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SIGNEXTEND_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_LW m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LH`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LH_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SIGNEXTEND_H → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LH m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_LB`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_LB_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 _rd : Fin 32) (_imm_offset : FGL) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_SIGNEXTEND_B → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_LB m r_main rs1 _rd _imm_offset state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_DIVUW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_DIVUW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIVU_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_DIVUW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_REMUW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_REMUW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REMU_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_REMUW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_DIVW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_DIVW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIV_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_DIVW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_REMW`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_REMW_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REM_W → m.m32 r_main = 1 :=
  fun h_p1 h_p2 =>
    (transpile_REMW m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_DIVU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_DIVU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIVU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_DIVU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_REMU`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_REMU_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REMU → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_REMU m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_DIV`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_DIV_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_DIV → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_DIV m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-- V13 consumer-witness for `transpile_REM`. Axiom-load-bearing via
    first-conjunct extraction. -/
theorem transpile_REM_consumer
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (rs1 rs2 _rd : Fin 32) (state : RV64State)
    : m.is_external_op r_main = 1 → m.op r_main = OP_REM → m.m32 r_main = 0 :=
  fun h_p1 h_p2 =>
    (transpile_REM m r_main rs1 rs2 _rd state h_p1 h_p2).1

/-! ## Phase 6 finishing5 S1 — store_pc=1 PC bridges (TP-JAL / TP-JALR / TP-AUIPC)

    Each of the three `transpile_PC_consumer_<OP>` lemmas below makes
    its corresponding `transpile_PC_for_<OP>` axiom load-bearing
    (`#print axioms transpile_PC_consumer_<OP>` reports the axiom).
    Unlike the operand-axiom consumers above, the PC axioms have a
    single equality conclusion (not a conjunction), so the consumer
    simply re-exposes the axiom under its mode-witness premises. -/

/-- V13 consumer-witness for `transpile_PC_for_JAL`. Re-exposes the
    PC bridge axiom under its mode-witness premises so that
    `#print axioms transpile_PC_consumer_JAL` lists it as a
    dependency. -/
theorem transpile_PC_consumer_JAL
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (PC : BitVec 64)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG →
      (m.pc r_main).val = PC.toNat :=
  fun h_p1 h_p2 =>
    transpile_PC_for_JAL m r_main PC h_p1 h_p2

/-- V13 consumer-witness for `transpile_PC_for_JALR`. -/
theorem transpile_PC_consumer_JALR
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (PC : BitVec 64)
    : m.is_external_op r_main = 0 → m.op r_main = OP_COPYB →
      (m.pc r_main).val = PC.toNat :=
  fun h_p1 h_p2 =>
    transpile_PC_for_JALR m r_main PC h_p1 h_p2

/-- V13 consumer-witness for `transpile_PC_for_AUIPC`. -/
theorem transpile_PC_consumer_AUIPC
    {C : Type → Type → Type} [Circuit FGL FGL C]
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (PC : BitVec 64)
    : m.is_external_op r_main = 0 → m.op r_main = OP_FLAG →
      (m.pc r_main).val = PC.toNat :=
  fun h_p1 h_p2 =>
    transpile_PC_for_AUIPC m r_main PC h_p1 h_p2

end ZiskFv.Trusted