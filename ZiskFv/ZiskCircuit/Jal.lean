import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.PackedBitVec.WidePCNoWrap
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus.OperationBus

/-!
Compositional JAL (jump-and-link) spec: given the named jump-subset Main
constraints and the mode witnesses supplied by `transpile_JAL`
(`op = OP_FLAG = 0`, `is_external_op = 0`, `m32 = 0`, `set_pc = 0`,
`store_pc = 1`), the *next-row* `pc` cell equals `pc + jmp_offset1`
(= `pc + imm`) and the store-value lane zero equals `pc + jmp_offset2`
(= `pc + 4` — the return address written to rd).

Unlike BEQ, JAL is **not** an external op (`is_external_op = 0`), so
constraints 8/15 (internal-op=0 zeroes c) and 17 (internal-op=0 sets
flag) are non-trivial and together force `flag = 1` and `c = 0`. No
operation-bus hop is emitted.

This is the A2 archetype spec. JALR differs by `set_pc = 1` and
`c[0]` (from rs1 via the operation bus) driving next-pc.

## Bus-emission lo/hi BitVec bridges

The two theorems `jal_store_value_lo_bv` / `jal_store_value_hi_bv`
extend `jal_store_value` (which ties the Main columns
`store_pc * (pc + jmp_offset2 - c_0) + c_0` to `pc + jmp_offset2`) to
the **memory-bus entry** lanes via the `store_pc_lanes_match_*`
predicates from `Airs/MemoryBus.lean`, composed with the wide-PC
no-wrap toolkit (`Fundamentals/PackedBitVec/WidePCNoWrap.lean`) and
the `transpile_PC_for_JAL` axiom.

The hi-half is structurally trivial under JAL's `store_pc = 1` mode:
the PIL formula `(1 - store_pc) * c_1` collapses to `0`, so
`memory_entry_hi e = 0`. To match the BitVec hi-half projection
`(PC + 4).toNat / 2^32` the caller supplies a 32-bit bound on
`(PC + 4).toNat` (immediate from the ROM `pc < 2^32` invariant for
ELF-loaded programs).
-/

namespace ZiskFv.ZiskCircuit.Jal

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.OperationBus
open ZiskFv.Trusted
open ZiskFv.PackedBitVec.WidePCNoWrap


/-- The Main row at `r_main` is in JAL-execution mode: internal op with
    opcode literal 0 (OP_FLAG), full 64-bit width (m32 = 0), `set_pc = 0`
    (PC advance comes from `flag = 1` + `jmp_offset1`, not `c[0]`), and
    `store_pc = 1` (rd receives `pc + jmp_offset2 = pc + 4`). -/
@[simp]
def main_row_in_jal_mode (m : Valid_Main FGL FGL) (r_main : ℕ) : Prop :=
  m.is_external_op r_main = 0
  ∧ m.op r_main = (0 : FGL)
  ∧ m.m32 r_main = 0
  ∧ m.set_pc r_main = 0
  ∧ m.store_pc r_main = 1

/-- Hypotheses needed by `jal_compositional`. All four circuit-side
    obligations are constraint witnesses plus the transpile-axiom's
    mode witnesses — no external SM delegation needed (JAL is internal
    op 0). -/
@[simp]
def jal_circuit_holds
    (m : Valid_Main FGL FGL)
    (r_main : ℕ) (next_pc : FGL) : Prop :=
  jump_subset_holds m r_main next_pc
  ∧ main_row_in_jal_mode m r_main

/-- **Compositional JAL (next-pc) theorem.** Given the jump-subset Main
    constraints (booleans + `flag*set_pc = 0` disjointness + constraints
    8/15/17 + PC handshake) and the mode witnesses (`is_external_op = 0`,
    `op = 0`, `m32 = 0`, `set_pc = 0`, `store_pc = 1`), the next-row `pc`
    equals `pc + jmp_offset1`.

    Composed with `transpile_JAL` (which pins `jmp_offset1 = imm`), this
    says JAL advances PC to `pc + imm`, consistent with the RISC-V
    unconditional-jump semantics. -/
lemma jal_pc_advance
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jal_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, _h_c0_zero, _h_c1_zero,
          h17, h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, h_set_pc, _h_store_pc⟩ := h_mode
  have h_flag : m.flag r_main = 1 :=
    flag_eq_one_of_internal_op_zero m r_main h_ext h_op h17
  exact pc_handshake_jump m r_main next_pc h_set_pc h_flag h_handshake

/-- **Return address.** The `store_value[0] = store_pc*(pc + jmp_offset2
    - c_0) + c_0` expression (`main.pil:311`) under JAL's mode
    witnesses (`store_pc = 1`, and `c_0 = 0` from constraint 8 with
    `is_external_op = 0, op = 0`) evaluates to `pc + jmp_offset2`.
    With `transpile_JAL` pinning `jmp_offset2 = 4`, this is the
    `pc + 4` return-address value written to rd. -/
lemma jal_store_value
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : jal_circuit_holds m r_main next_pc) :
    m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
        + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main := by
  obtain ⟨h_subset, h_mode⟩ := h
  obtain ⟨_h_flag_bool, _h_ext_bool, _h_disjoint, h8, _h15, _h17, _h_handshake⟩ := h_subset
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  have h_c0 : m.c_0 r_main = 0 :=
    c_0_eq_zero_of_internal_op_zero m r_main h_ext h_op h8
  rw [h_c0, h_store_pc]
  ring

/-! ## Bus-emission BitVec bridges -/

/-- **JAL rd-write lo half (BitVec form).** The memory-bus entry's
    lo-half lane carries `(PC + 4)` modulo `2^32`. Composed from:

    1. `jal_store_value` — Main's `store_value[0]` formula collapses
       to `pc + jmp_offset2`.
    2. `store_pc_lanes_match_lo` — the bus entry's lo half equals the
       same PIL expression `store_pc * (pc + jmp_offset2 - c_0) + c_0`.
    3. `transpile_JAL`'s `jmp_offset2 = 4` pin.
    4. `transpile_PC_for_JAL` — `(m.pc r).val = PC.toNat`.
    5. `WidePCNoWrap.fgl_pc_plus_offset_val_eq_lo_strict` — under the
       no-wrap hypothesis (PC trajectory bound) and the lo-half range
       bound on the FGL sum, the FGL `(pc_fgl + 4).val` equals
       `(PC + 4).toNat` modulo `2^32` directly (no outer-mod on LHS).

    The strict form matches the downstream consumer
    (`JumpUType.lean`'s lo-half input) directly. The
    `h_lo_bound : (m.pc + 4).val < 2^32` hypothesis is realistic for
    ELF-loaded ZisK programs (ROM `pc : bits(32)` invariant). -/
lemma jal_store_value_lo_bv
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : jal_circuit_holds m r_main next_pc)
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    (h_lane_lo : store_pc_lanes_match_lo m r_main e)
    (h_pc_bridge : (m.pc r_main).val = PC.toNat)
    (h_pc_bound : PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296) :
    (memory_entry_lo e).val = (PC + 4#64).toNat % 4294967296 := by
  -- Combine `jal_store_value` and the lane-match predicate to derive
  -- `memory_entry_lo e = m.pc r_main + m.jmp_offset2 r_main`.
  have h_sv := jal_store_value m r_main next_pc h_circuit
  -- `h_lane_lo` unfolds (via `@[simp]`) to the PIL expression equality.
  simp only [store_pc_lanes_match_lo] at h_lane_lo
  -- `h_lane_lo : memory_entry_lo e = store_pc * (pc + jmp_offset2 - c_0) + c_0`
  -- `h_sv     : store_pc * (pc + jmp_offset2 - c_0) + c_0 = pc + jmp_offset2`
  rw [h_sv] at h_lane_lo
  -- `h_lane_lo : memory_entry_lo e = m.pc r_main + m.jmp_offset2 r_main`
  rw [h_jmp2] at h_lane_lo
  -- `h_lane_lo : memory_entry_lo e = m.pc r_main + 4`
  -- Lift the FGL equality to `.val` and apply S2's wide-PC lo lemma.
  rw [h_lane_lo]
  -- Discharge the no-wrap hypothesis from the PC bound.
  have h_no_wrap : (m.pc r_main).val + ((4 : FGL)).val < GL_prime := by
    have h4 : ((4 : FGL)).val = 4 := by decide
    rw [h_pc_bridge, h4]
    omega
  exact fgl_pc_plus_offset_val_eq_lo_strict
    (m.pc r_main) (4 : FGL) PC 4#64
    h_pc_bridge offset_4_bridge h_no_wrap h_lo_bound

/-- **JAL rd-write hi half (BitVec form).** Under JAL's
    `store_pc = 1` mode, the PIL `store_value[1] = (1 - store_pc) * c_1`
    collapses to `0`, so the memory-bus entry's hi half is identically
    zero. Matching the BitVec hi-half projection `(PC + 4).toNat / 2^32`
    requires the caller to supply the 32-bit PC-plus-offset bound
    (immediate from the ROM `pc < 2^32` invariant for ELF-loaded
    programs).

    Plugged into JumpUType's hi-entry input by the equivalence layer. -/
lemma jal_store_value_hi_bv
    (m : Valid_Main FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : jal_circuit_holds m r_main next_pc)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e)
    (h_pc_offset_lt_2_32 : (PC + 4#64).toNat < 4294967296) :
    (memory_entry_hi e).val = (PC + 4#64).toNat / 4294967296 := by
  obtain ⟨_h_subset, h_mode⟩ := h_circuit
  obtain ⟨_h_ext, _h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  -- Unfold the hi-lane match predicate and apply `store_pc = 1` to
  -- collapse `(1 - 1) * c_1` to `0`.
  simp only [store_pc_lanes_match_hi, h_store_pc] at h_lane_hi
  -- `h_lane_hi : memory_entry_hi e = (1 - 1) * c_1`
  rw [h_lane_hi]
  -- Goal: `((1 - 1) * c_1).val = (PC + 4#64).toNat / 2^32`
  -- LHS = 0 by ring, RHS = 0 by the 32-bit bound.
  have h_zero : ((1 - 1 : FGL) * m.c_1 r_main).val = 0 := by
    have : (1 - 1 : FGL) * m.c_1 r_main = 0 := by ring
    rw [this]
    rfl
  rw [h_zero]
  exact (Nat.div_eq_zero_iff_lt (by decide)).mpr h_pc_offset_lt_2_32 |>.symm

end ZiskFv.ZiskCircuit.Jal
