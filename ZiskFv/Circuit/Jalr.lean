import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Fundamentals.PackedBitVec.WidePCNoWrap
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.JumpArchetype

/-!
Compositional JALR (jump-and-link-register) spec: given the named
JALR-subset Main constraints and the mode witnesses supplied by
`transpile_JALR` (`op = OP_COPYB = 1`, `is_external_op = 0`, `m32 = 0`,
`set_pc = 1`, `store_pc = 1`), the *next-row* `pc` cell equals
`b[0] + jmp_offset1` (= `rs1_lo + imm12`) and the store-value lane zero
expression evaluates to `pc + jmp_offset2` (= `pc + 4` — the link
address written to rd).

JALR is the sibling of JAL for the jump archetype macro
(`ZiskFv.Tactics.JumpArchetype`). Unlike JAL which uses the internal-
op-0 (`flag`) constraints 8/15/17 to pin `flag = 1`, JALR uses the
internal-op-1 (`copyb`) constraints 9/16/18 to pin `flag = 0` and
`c = b`. The PC handshake then takes the `set_pc = 1` branch
(`c_0 + jmp_offset1`) rather than JAL's flag-driven branch
(`pc + jmp_offset1`).

The `store_value` expression (`main.pil:311`,
`store_pc * (pc + jmp_offset2 - c_0) + c_0`) is identical for both —
`store_pc = 1` makes `c_0` cancel, yielding `pc + jmp_offset2`.
-/

namespace ZiskFv.Circuit.Jalr

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.Tactics.JumpArchetype
open ZiskFv.PackedBitVec.WidePCNoWrap

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- The Main row at `r_main` is in JALR-execution mode: internal op
    with opcode literal 1 (OP_COPYB), full 64-bit width (m32 = 0),
    `set_pc = 1` (PC advance comes from `c[0] + jmp_offset1`), and
    `store_pc = 1` (rd receives `pc + jmp_offset2 = pc + 4`). -/
@[simp]
def main_row_in_jalr_mode (m : Valid_Main C FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (1 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 1
  ∧ m.store_pc r_main = 1

/-- Hypotheses needed by `jalr_compositional`. All four circuit-side
    obligations are constraint witnesses plus the transpile-axiom's
    mode witnesses — no external SM delegation needed (JALR is internal
    op 1 under the archetype-validation contract; see
    `Transpiler.transpile_JALR`). -/
@[simp]
def jalr_circuit_holds
    (m : Valid_Main C FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  jalr_subset_holds m r_main next_pc
  ∧ main_row_in_jalr_mode m r_main

/-- **Compositional JALR (next-pc) theorem.** Given the JALR constraint
    subset and the mode witnesses (`is_external_op = 0`, `op = 1`,
    `m32 = 0`, `set_pc = 1`, `store_pc = 1`), the next-row `pc` equals
    `b[0] + jmp_offset1`.

    Composed with `transpile_JALR` (which pins `jmp_offset1 = imm12`
    and `b[0] = rs1_lo`), this says JALR advances PC to
    `rs1_lo + imm12`, consistent with the RISC-V JALR semantics
    (`(rs1 + sign_extend imm) & 0xFFFFFFFE`, modulo the mask-bit which
    the archetype-validation contract delegates to the immediate
    routing).

    Discharged via `jalr_archetype_pc_advance` with `opcode_lit = 1`. -/
lemma jalr_pc_advance
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jalr_circuit_holds m r_main next_pc) :
    next_pc = m.b_0 r_main + m.jmp_offset1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  exact jalr_archetype_pc_advance m r_main next_pc ⟨h_subset, h_mode⟩

/-- **Link address.** The `store_value[0] = store_pc*(pc + jmp_offset2
    - c_0) + c_0` expression (`main.pil:311`) under JALR's mode
    witnesses (`store_pc = 1`) evaluates to `pc + jmp_offset2`
    (independent of `c_0` thanks to the `store_pc = 1` cancellation).
    With `transpile_JALR` pinning `jmp_offset2 = 4`, this is the
    `pc + 4` link address written to rd — same as JAL. -/
lemma jalr_store_value
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jalr_circuit_holds m r_main next_pc) :
    m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
        + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  exact jalr_archetype_store_value m r_main next_pc ⟨h_subset, h_mode⟩

/-! ## Bus-emission BitVec bridges

Same shape as JAL's `jal_store_value_lo_bv` / `jal_store_value_hi_bv`.
JALR's link address is also `pc + 4` (the `jmp_offset2 = 4` pin in
`transpile_JALR` is identical), and `store_pc = 1` zeroes the hi
half. The Spec lemmas only differ in their input `*_circuit_holds`
predicate (`jalr_circuit_holds` here vs `jal_circuit_holds`); the PC
bridge `h_pc_bridge : (m.pc r).val = PC.toNat` is supplied by the
caller from `transpile_PC_for_JALR`. -/

/-- **JALR rd-write lo half (BitVec form).** Identical shape to
    `jal_store_value_lo_bv` modulo the JALR-specific circuit
    predicate. Composes `jalr_store_value` with
    `store_pc_lanes_match_lo` and S2's wide-PC strict lo lemma. -/
lemma jalr_store_value_lo_bv
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
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
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : jalr_circuit_holds m r_main next_pc)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e)
    (h_pc_offset_lt_2_32 : (PC + 4#64).toNat < 4294967296) :
    (memory_entry_hi e).val = (PC + 4#64).toNat / 4294967296 := by
  obtain ⟨_h_subset, h_mode⟩ := h_circuit
  obtain ⟨_h_ext, _h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  simp only [store_pc_lanes_match_hi, h_store_pc] at h_lane_hi
  rw [h_lane_hi]
  have h_zero : ((1 - 1 : FGL) * m.c_1 r_main).val = 0 := by
    have : (1 - 1 : FGL) * m.c_1 r_main = 0 := by ring
    rw [this]
    rfl
  rw [h_zero]
  exact (Nat.div_eq_zero_iff_lt (by decide)).mpr h_pc_offset_lt_2_32 |>.symm

end ZiskFv.Circuit.Jalr
