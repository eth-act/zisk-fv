import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.PackedBitVec.WidePCNoWrap
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus

/-!
Compositional JALR (jump-and-link-register) spec for the production
ZisK lowering. The final architectural row is an external `OP_AND`
row with `set_pc = 1` and `store_pc = 1`; aligned immediates have only
that row, while unaligned immediates use an earlier `OP_ADD` row whose
result is fed to the final row through `lastc`.

The `store_value` expression (`main.pil:311`,
`store_pc * (pc + jmp_offset2 - c_0) + c_0`) is identical for both —
`store_pc = 1` makes `c_0` cancel, yielding `pc + jmp_offset2`.
-/

namespace ZiskFv.ZiskCircuit.Jalr

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.PackedBitVec.WidePCNoWrap

/-- The final Main row for production JALR: external `OP_AND`, full
    64-bit width, `set_pc = 1`, and `store_pc = 1`. The `flag = 0`
    pin is part of the ordinary `OP_AND` transpiler contract and makes
    the PC handshake reduce to the set-PC branch. -/
@[simp]
def main_row_in_jalr_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 1
  ∧ m.op r_main = OP_AND
  ∧ m.flag r_main = 0
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 1
  ∧ m.store_pc r_main = 1

/-- Main source-C obligations for the final JALR row. On non-segment rows
    these are the extracted/PIL source-C constraints specialized to
    `previous_c = c(row - 1)`. -/
@[simp]
def jalr_source_c_constraints_hold
    (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.segment_l1 r_main = 0 →
    b_src_c_copies_prev_c0 m r_main
    ∧ b_src_c_copies_prev_c1 m r_main

/-- Branch-specific production shape of the unaligned JALR final row.
    This records the selector and previous-row pins used to derive the
    `ADD -> lastc -> AND` chain when `imm % 4 ≠ 0`. -/
@[simp]
def jalr_unaligned_lowering_holds
    (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  ∀ (_rs1 _rd : Fin 32) (imm_offset : FGL) (_state : RV64State),
    imm_offset.val % 4 ≠ 0 →
      m.b_src_mem r_main = 0
    ∧ m.b_src_imm r_main = 0
    ∧ m.b_src_ind r_main = 0
    ∧ m.b_src_reg r_main = 0
    ∧ m.jmp_offset1 r_main = 0
    ∧ m.jmp_offset2 r_main = 3
    ∧ m.is_external_op (r_main - 1) = 1
    ∧ m.op (r_main - 1) = OP_ADD

/-- Hypotheses needed by `jalr_compositional`. All four circuit-side
    obligations are constraint witnesses plus the transpile-axiom's
    mode witnesses for the final production `OP_AND` row. -/
@[simp]
def jalr_circuit_holds
    (m : Valid_Main FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  flag_boolean m r_main
  ∧ is_external_op_boolean m r_main
  ∧ flag_set_pc_disjoint m r_main
  ∧ pc_handshake_with_next_pc m r_main next_pc
  ∧ main_row_in_jalr_mode m r_main
  ∧ jalr_source_c_constraints_hold m r_main
  ∧ jalr_unaligned_lowering_holds m r_main

/-- **Compositional JALR (next-pc) theorem.** On the final production
    row, `set_pc = 1` and `flag = 0`, so the PC handshake reduces to
    `next_pc = c_0 + jmp_offset1`. For aligned JALR the transpiler pins
    `jmp_offset1 = imm`; for unaligned JALR the final row pins
    `jmp_offset1 = 0` and receives the add row's result through `lastc`. -/
lemma jalr_pc_advance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jalr_circuit_holds m r_main next_pc) :
    next_pc = m.c_0 r_main + m.jmp_offset1 r_main := by
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h_pc, h_mode, _h_src, _h_unaligned⟩ := h
  obtain ⟨_h_ext, _h_op, h_flag, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  simp only [pc_handshake_with_next_pc] at h_pc
  rw [h_set_pc, h_flag] at h_pc
  linear_combination h_pc

/-! ## Unaligned production lowering: ADD → lastc → AND

The unaligned production lowering computes `rs1 + imm` in the previous
Main row (`OP_ADD`) and feeds that result into the final `OP_AND` row
through Main's source-C path (`lastc`). The two lemmas below keep that
bridge explicit: one proves the lastc lane equalities from Main
source-C constraints, and one packages the current trusted selector
contract for the unaligned JALR final row.
-/

/-- Source-C expansion under the four zero source selectors used by the
    unaligned final JALR row. -/
lemma b_src_c_eq_one_of_all_other_b_sources_zero
    (m : Valid_Main FGL FGL) (row : ℕ)
    (h_mem : m.b_src_mem row = 0)
    (h_imm : m.b_src_imm row = 0)
    (h_ind : m.b_src_ind row = 0)
    (h_reg : m.b_src_reg row = 0) :
    b_src_c m row = 1 := by
  simp only [b_src_c]
  rw [h_mem, h_imm, h_ind, h_reg]
  ring

/-- If the final JALR row is a non-segment source-C row, then its `b`
    operand is exactly the previous row's `c` result. This is the
    row-local `lastc` bridge for unaligned production JALR. -/
lemma jalr_unaligned_lastc_lanes
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (h_src : b_src_c m r_main = 1)
    (h_src_c0 : b_src_c_copies_prev_c0 m r_main)
    (h_src_c1 : b_src_c_copies_prev_c1 m r_main) :
    m.b_0 r_main = m.c_0 (r_main - 1)
    ∧ m.b_1 r_main = m.c_1 (r_main - 1) :=
  ⟨b_0_eq_prev_c_0_of_source_c m r_main h_src h_src_c0,
   b_1_eq_prev_c_1_of_source_c m r_main h_src h_src_c1⟩

/-- Trusted-contract entry point for production unaligned JALR.

    From the unaligned branch of the transpiler contract and the
    non-segment Main source-C constraints, derive the concrete row chain:
    the previous row is external `OP_ADD`, the final row has `b_src_c = 1`,
    `jmp_offset1 = 0`, `jmp_offset2 = 3`, and the final row's `b` lanes
    equal the previous row's `c` lanes. -/
lemma jalr_unaligned_add_lastc_and_chain
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (rs1 rd : Fin 32) (imm_offset : FGL) (state : RV64State)
    (h_imm_unaligned : imm_offset.val % 4 ≠ 0)
    (h_ext : m.is_external_op r_main = 1)
    (h_op : m.op r_main = OP_AND)
    (h_nonsegment : m.segment_l1 r_main = 0) :
      m.is_external_op (r_main - 1) = 1
    ∧ m.op (r_main - 1) = OP_ADD
    ∧ b_src_c m r_main = 1
    ∧ m.jmp_offset1 r_main = 0
    ∧ m.jmp_offset2 r_main = 3
    ∧ m.b_0 r_main = m.c_0 (r_main - 1)
    ∧ m.b_1 r_main = m.c_1 (r_main - 1) := by
  have h_shape :=
    transpile_JALR_unaligned_final_source_c
      m r_main rs1 rd imm_offset state h_imm_unaligned h_ext h_op
  obtain ⟨h_mem, h_imm, h_ind, h_reg, h_jmp1, h_jmp2, h_prev_ext, h_prev_op⟩ := h_shape
  have h_src : b_src_c m r_main = 1 :=
    b_src_c_eq_one_of_all_other_b_sources_zero
      m r_main h_mem h_imm h_ind h_reg
  have h_src_c0 := main_source_c_copies_prev_c0_nonsegment m r_main h_nonsegment
  have h_src_c1 := main_source_c_copies_prev_c1_nonsegment m r_main h_nonsegment
  obtain ⟨h_b0, h_b1⟩ :=
    jalr_unaligned_lastc_lanes m r_main h_src h_src_c0 h_src_c1
  exact ⟨h_prev_ext, h_prev_op, h_src, h_jmp1, h_jmp2, h_b0, h_b1⟩

/-- Same row-chain theorem as `jalr_unaligned_add_lastc_and_chain`, but
    consuming the obligations already packaged in `jalr_circuit_holds`.
    This is the form downstream proofs should prefer. -/
lemma jalr_unaligned_add_lastc_and_chain_of_circuit
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (rs1 rd : Fin 32) (imm_offset : FGL) (state : RV64State)
    (h_circuit : jalr_circuit_holds m r_main next_pc)
    (h_imm_unaligned : imm_offset.val % 4 ≠ 0)
    (h_nonsegment : m.segment_l1 r_main = 0) :
      m.is_external_op (r_main - 1) = 1
    ∧ m.op (r_main - 1) = OP_ADD
    ∧ b_src_c m r_main = 1
    ∧ m.jmp_offset1 r_main = 0
    ∧ m.jmp_offset2 r_main = 3
    ∧ m.b_0 r_main = m.c_0 (r_main - 1)
    ∧ m.b_1 r_main = m.c_1 (r_main - 1) := by
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_pc, _h_mode,
          h_source_c, h_unaligned⟩ := h_circuit
  obtain ⟨h_mem, h_imm, h_ind, h_reg, h_jmp1, h_jmp2, h_prev_ext, h_prev_op⟩ :=
    h_unaligned rs1 rd imm_offset state h_imm_unaligned
  obtain ⟨h_src_c0, h_src_c1⟩ := h_source_c h_nonsegment
  have h_src : b_src_c m r_main = 1 :=
    b_src_c_eq_one_of_all_other_b_sources_zero
      m r_main h_mem h_imm h_ind h_reg
  obtain ⟨h_b0, h_b1⟩ :=
    jalr_unaligned_lastc_lanes m r_main h_src h_src_c0 h_src_c1
  exact ⟨h_prev_ext, h_prev_op, h_src, h_jmp1, h_jmp2, h_b0, h_b1⟩

/-- **Link address.** The `store_value[0] = store_pc*(pc + jmp_offset2
    - c_0) + c_0` expression (`main.pil:311`) under JALR's mode
    witnesses (`store_pc = 1`) evaluates to `pc + jmp_offset2`
    (independent of `c_0` thanks to the `store_pc = 1` cancellation).
    The separate `transpile_PC_for_JALR` bridge pins this row-level
    expression to Sail's link address `PC + 4`, covering both aligned
    and unaligned production lowerings. -/
lemma jalr_store_value
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jalr_circuit_holds m r_main next_pc) :
    m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
        + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_pc, h_mode, _h_src, _h_unaligned⟩ := h
  obtain ⟨_h_ext, _h_op, _h_flag, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  rw [h_store_pc]
  ring

/-! ## Bus-emission BitVec bridges

Same shape as JAL's `jal_store_value_lo_bv` / `jal_store_value_hi_bv`,
except production JALR's link address is bridged as `pc + jmp_offset2 =
PC + 4` rather than by separately pinning `pc = PC` and
`jmp_offset2 = 4`. `store_pc = 1` zeroes the hi half. -/

/-- **JALR rd-write lo half (BitVec form).** Identical shape to
    `jal_store_value_lo_bv` modulo the JALR-specific circuit
    predicate. Composes `jalr_store_value` with
    `store_pc_lanes_match_lo` and S2's wide-PC strict lo lemma. -/
lemma jalr_store_value_lo_bv
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : jalr_circuit_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_lane_lo : store_pc_lanes_match_lo m r_main e)
    (h_pc_bridge : (m.pc r_main).val = PC.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296) :
    (memory_entry_lo e).val = (PC + 4#64).toNat % 4294967296 := by
  have h_sv := jalr_store_value m r_main next_pc h_circuit
  simp only [store_pc_lanes_match_lo] at h_lane_lo
  rw [h_sv] at h_lane_lo
  rw [h_jmp2] at h_lane_lo
  rw [h_lane_lo]
  have h_no_wrap : (m.pc r_main).val + ((4 : FGL)).val < GL_prime := by
    have h4 : ((4 : FGL)).val = 4 := by decide
    rw [h_pc_bridge, h4]
    omega
  exact fgl_pc_plus_offset_val_eq_lo_strict
    (m.pc r_main) (4 : FGL) PC 4#64
    h_pc_bridge offset_4_bridge h_no_wrap h_lo_bound

/-- **JALR rd-write hi half (BitVec form).** Identical shape to
    `jal_store_value_hi_bv`. Under JALR's `store_pc = 1` mode, the
    PIL `(1 - store_pc) * c_1` collapses to `0`, so the hi half is
    zero. Matching the BitVec hi-half projection requires
    `(PC + 4).toNat < 2^32`. -/
lemma jalr_store_value_hi_bv
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : jalr_circuit_holds m r_main next_pc)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e)
    (h_pc_offset_lt_2_32 : (PC + 4#64).toNat < 4294967296) :
    (memory_entry_hi e).val = (PC + 4#64).toNat / 4294967296 := by
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_pc, h_mode, _h_src, _h_unaligned⟩ := h_circuit
  obtain ⟨_h_ext, _h_op, _h_flag, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  simp only [store_pc_lanes_match_hi, h_store_pc] at h_lane_hi
  rw [h_lane_hi]
  have h_zero : ((1 - 1 : FGL) * m.c_1 r_main).val = 0 := by
    have : (1 - 1 : FGL) * m.c_1 r_main = 0 := by ring
    rw [this]
    rfl
  rw [h_zero]
  exact (Nat.div_eq_zero_iff_lt (by decide)).mpr h_pc_offset_lt_2_32 |>.symm

end ZiskFv.ZiskCircuit.Jalr
