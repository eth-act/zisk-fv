import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Trusted.Transpiler
import ZiskFv.Bits.PackedBitVec.WidePCNoWrap
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.OperationBus
import ZiskFv.Tactics.UTypeArchetype

/-!
Compositional AUIPC spec.

AUIPC has no secondary state-machine hop — the whole microinstruction
is handled by the Main AIR alone (internal `flag` routing). Given the
named `auipc_subset_holds` Main constraints and the mode witnesses
supplied by `transpile_AUIPC` (`op = OP_FLAG = 0`,
`is_external_op = 0`, `m32 = 0`, `set_pc = 0`, `store_pc = 1`), the
next-row `pc` cell equals `pc + jmp_offset1 = pc + 4`, and the
store-value low lane equals `pc + jmp_offset2 = pc + imm`.

AUIPC differs from LUI only in the internal-op discriminant and the
routing of the immediate: LUI carries it in `b` (so rd = `c = b = imm`
via `store_pc = 0`), while AUIPC carries it in `jmp_offset2` (so
rd = `pc + jmp_offset2` via `store_pc = 1` with `c = 0` from
constraint 8). Both opcodes consume a single Main row with no
operation-bus entry.
-/

namespace ZiskFv.Circuit.AddUpperImmediatePC

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Trusted
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.PackedBitVec.WidePCNoWrap

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compositional AUIPC theorem — next-pc advance.** The next-pc
    equals `pc + jmp_offset1`. Under `transpile_AUIPC`'s pinning
    `jmp_offset1 = 4`, this gives `pc + 4`.

    Note that AUIPC's `jmp_offset2` carries the immediate, not the
    fall-through offset — `transpile_AUIPC`'s `j(4, imm)` call inverts
    the `j1/j2` assignment relative to JAL's `j(imm, 4)`. The PC
    handshake's `flag * (jmp_offset1 - jmp_offset2)` term cancels the
    `jmp_offset2` contribution, leaving `pc + jmp_offset1 = pc + 4`. -/
lemma auipc_pc_advance
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    next_pc = m.pc r_main + m.jmp_offset1 r_main :=
  auipc_archetype_pc_advance m r_main next_pc h

/-- **Compositional AUIPC theorem — rd low lane.** The rd-write low
    lane (`store_value[0]`) equals `pc + jmp_offset2 = pc + imm`. -/
lemma auipc_store_value_lo
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    m.store_pc r_main *
        (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main)
      + m.c_0 r_main
      = m.pc r_main + m.jmp_offset2 r_main :=
  auipc_archetype_store_value_lo m r_main next_pc h

/-- **Compositional AUIPC theorem — rd high lane.** The rd-write high
    lane `(1 - store_pc) * c_1` is zero because `store_pc = 1` zeros
    the gate. The full 64-bit `pc + imm` identity on the high lane is
    carried separately by the store-PC mechanics in the downstream
    memory-bus emission (high lane is the pc-high lane, not a direct
    column, for AUIPC). -/
lemma auipc_store_value_hi
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h : auipc_archetype_circuit_holds m r_main next_pc) :
    (1 - m.store_pc r_main) * m.c_1 r_main = 0 :=
  auipc_archetype_store_value_hi m r_main next_pc h

/-! ## Bus-emission BitVec bridges

AUIPC writes `pc + signExtend 64 (imm ++ 0#12)` to rd. Unlike JAL/JALR
the offset is a sign-extended 32-bit immediate, not a constant 4. The
lo-half theorem composes the existing `auipc_store_value_lo` (Main's
column-level `pc + jmp_offset2` identity) with `store_pc_lanes_match_lo`
(memory-bus entry's lo half = same PIL expression) and S2's
`fgl_pc_plus_offset_val_eq_lo_strict` (FGL ↔ BitVec wide-PC bridge).

The hi-half is structurally trivial under AUIPC's `store_pc = 1` mode
— the PIL `(1 - store_pc) * c_1` collapses to `0`. Matching the
BitVec hi-half projection `(PC + signExtend 64 (imm ++ 0#12)).toNat
/ 2^32` requires the caller to supply a 32-bit bound on the
PC-plus-offset Sail sum. -/

/-- **AUIPC rd-write lo half (BitVec form).** The memory-bus entry's
    lo-half lane carries `(PC + offset_bv)` modulo `2^32` where
    `offset_bv` is the Sail-side sign-extended 32-bit immediate.
    Composed from:

    1. `auipc_store_value_lo` — Main's `store_value[0]` formula
       collapses to `pc + jmp_offset2`.
    2. `store_pc_lanes_match_lo` — the bus entry's lo half equals the
       same PIL expression.
    3. `transpile_PC_for_AUIPC` — `(m.pc r).val = PC.toNat`.
    4. `h_offset_bridge` — caller-supplied bridge from the FGL-side
       `m.jmp_offset2 r` to the Sail-side `offset_bv.toNat` (this is
       the transpile contract for AUIPC's offset routing,
       `transpile_AUIPC` pins `jmp_offset2 = imm_offset` at the FGL
       level; the BitVec ↔ FGL `.val ↔ .toNat` bridge is taken as
       hypothesis here).
    5. `WidePCNoWrap.fgl_pc_plus_offset_val_eq_lo_strict` — under
       no-wrap and lo-half range bounds, the FGL `(pc + offset).val`
       equals the BitVec `(PC + offset_bv).toNat % 2^32`.

    The strict form matches `JumpUType.lean`'s lo-half input
    directly. -/
lemma auipc_store_value_lo_bv
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC offset_bv : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : auipc_archetype_circuit_holds m r_main next_pc)
    (h_lane_lo : store_pc_lanes_match_lo m r_main e)
    (h_pc_bridge : (m.pc r_main).val = PC.toNat)
    (h_offset_bridge : (m.jmp_offset2 r_main).val = offset_bv.toNat)
    (h_no_wrap : PC.toNat + offset_bv.toNat < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val
                    < 4294967296) :
    (memory_entry_lo e).val = (PC + offset_bv).toNat % 4294967296 := by
  -- Combine `auipc_store_value_lo` and the lane-match predicate.
  have h_sv := auipc_store_value_lo m r_main next_pc h_circuit
  simp only [store_pc_lanes_match_lo] at h_lane_lo
  rw [h_sv] at h_lane_lo
  -- `h_lane_lo : memory_entry_lo e = m.pc r_main + m.jmp_offset2 r_main`
  rw [h_lane_lo]
  -- Apply S2's strict-form lo lemma with the AUIPC offset.
  have h_no_wrap_fgl :
      (m.pc r_main).val + (m.jmp_offset2 r_main).val < GL_prime := by
    rw [h_pc_bridge, h_offset_bridge]
    exact h_no_wrap
  exact fgl_pc_plus_offset_val_eq_lo_strict
    (m.pc r_main) (m.jmp_offset2 r_main) PC offset_bv
    h_pc_bridge h_offset_bridge h_no_wrap_fgl h_lo_bound

/-- **AUIPC rd-write hi half (BitVec form).** Under AUIPC's
    `store_pc = 1` mode, the PIL `(1 - store_pc) * c_1` collapses to
    `0`, so `memory_entry_hi e = 0`. Matching the BitVec hi-half
    projection `(PC + offset_bv).toNat / 2^32` requires the caller to
    supply a 32-bit bound on `(PC + offset_bv).toNat`.

    This upgrades the existing `auipc_store_value_hi` (which proves
    only the gate-zero identity `(1 - store_pc) * c_1 = 0`) into the
    substantive bus-emission bridge. -/
lemma auipc_store_value_hi_bv
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (PC offset_bv : BitVec 64) (e : MemoryBusEntry FGL)
    (h_circuit : auipc_archetype_circuit_holds m r_main next_pc)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e)
    (h_pc_offset_lt_2_32 : (PC + offset_bv).toNat < 4294967296) :
    (memory_entry_hi e).val = (PC + offset_bv).toNat / 4294967296 := by
  -- Extract `store_pc = 1` from the AUIPC archetype-validation contract.
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

end ZiskFv.Circuit.AddUpperImmediatePC
