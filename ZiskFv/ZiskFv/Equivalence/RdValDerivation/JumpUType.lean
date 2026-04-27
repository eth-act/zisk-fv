import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.PackedBitVec
import ZiskFv.Fundamentals.PackedBitVec.Extensions
import ZiskFv.Airs.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Spec.Jal
import ZiskFv.Spec.Jalr
import ZiskFv.Spec.LoadUpperImmediate
import ZiskFv.Spec.AddUpperImmediatePC
import ZiskFv.Tactics.UTypeArchetype

/-!
# RdValDerivation.JumpUType — `h_rd_val` discharge lemmas for JAL/JALR/LUI/AUIPC

**Phase 2.5 N-Jump-UTYPE Tier-1 derivation (finishing1.md Phase 2.5).**

Each lemma in this file is **Tier 1**: it derives the `h_rd_val` conclusion
from circuit primitives directly. The old `h_byte_sum` parameter (a raw Nat
equality) has been replaced by structured circuit hypotheses:

* For **JAL/JALR**: `jal_circuit_holds` / `jalr_circuit_holds` (field-level
  `store_value = pc + jmp_offset2`) + transpiler pin `jmp_offset2 = 4` +
  FGL store_value-to-entry-lo match + Nat entry-hi match + PC-lo alignment.
  The proof derives `h_byte_sum` internally via FGL→Nat lifting and closes
  with K3 `pc_plus4_bv64_of_bytes`.

* For **LUI**: `lui_archetype_circuit_holds` + `register_write_lanes_match`
  (ties `c_0`/`c_1` to entry bytes, valid because `c = b = imm` for LUI)
  + transpiler b-lane Nat pins + K3 `signExtend_imm20_nat_lanes` compatibility.

* For **AUIPC**: `auipc_archetype_circuit_holds` + FGL store_value-to-entry-lo
  match + Nat entry-hi match + combined PC+imm lo alignment.

## Opcode → K3 lemma map

| Opcode | Pure-spec rd value | K3 lemma used |
|---|---|---|
| JAL  | `jal_input.PC + 4` | `pc_plus4_bv64_of_bytes` |
| JALR | `jalr_input.PC + 4` | `pc_plus4_bv64_of_bytes` |
| LUI  | `BitVec.signExtend 64 (imm ++ 0#12)` | `u64_toBV_of_imm20_lanes` |
| AUIPC| `PC + BitVec.signExtend 64 (imm ++ 0#12)` | `BitVec.eq_of_toNat_eq` + byte-sum |

## Trust surface

These lemmas accept structured hypotheses derivable from circuit constraints
and the PIL bus-emission contract. The FGL store_value-to-entry-lo hypotheses
(`h_e2_lo`) are the interface point between Main's internal circuit constraints
and the memory bus's byte emission — Phase 4 audit derives these from the PIL
memory-bus permutation-proves emission spec. The Nat hi-half hypotheses (`h_e2_hi_val`)
capture the high 4 bytes of the 64-bit value, which in practice are 0 for
programs executing within the lower 4 GB of address space.
-/

set_option maxHeartbeats 800000

namespace ZiskFv.Equivalence.RdValDerivation.JumpUType

open Goldilocks
open Interaction
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.Airs.MemoryBus.LaneMatch
open ZiskFv.Spec.Jal
open ZiskFv.Spec.Jalr
open ZiskFv.Spec.LoadUpperImmediate
open ZiskFv.Spec.AddUpperImmediatePC
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.Extensions

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-! ## Shared internal helper

Both JAL and JALR (and AUIPC in a similar form) need to derive a Nat byte_sum
from FGL lo/hi equalities plus byte range bounds. This private lemma handles
the common arithmetic. -/

/-- **FGL lane-to-byte-sum bridge (lo half).** Given:
    - `memory_entry_lo e2 = fgl_lo : FGL`
    - `(fgl_lo).val = target_nat % 4294967296`
    - byte ranges on the 4 lo bytes

    derives `x0.val + x1.val*256 + x2.val*65536 + x3.val*16777216 = target_nat % 4294967296`.

    Used to connect the lo 4 bytes of the memory bus entry to the
    FGL-level store_value expression. -/
private lemma lo_bytes_from_fgl_eq
    (e2 : MemoryBusEntry FGL) (fgl_lo : FGL)
    (target_nat : ℕ)
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h_lo_entry : memory_entry_lo e2 = fgl_lo)
    (h_lo_val : fgl_lo.val = target_nat % 4294967296) :
    e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      = target_nat % 4294967296 := by
  -- Unfold memory_entry_lo to expose the FGL sum.
  simp only [memory_entry_lo] at h_lo_entry
  -- Cast the FGL sum to its Nat value using push_cast + range bounds.
  have h_cast : (e2.x0 + e2.x1 * 256 + e2.x2 * 65536 + e2.x3 * 16777216 : FGL)
      = (((e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216 : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast] at h_lo_entry
  have h_lo_fgl_val := congr_arg Fin.val h_lo_entry
  simp only [Fin.val_natCast] at h_lo_fgl_val
  -- h_lo_fgl_val : (x0.val + ...) % GL_prime = fgl_lo.val
  -- Since the sum is at most 4*255 * 2^24 = 4278190080 < 2^32 < GL_prime, the mod is trivial.
  have h_sum_bound : e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      < 18446744069414584321 := by omega
  rw [Nat.mod_eq_of_lt h_sum_bound] at h_lo_fgl_val
  omega

/-- **FGL lane-to-byte-sum bridge (hi half).** Symmetric with `lo_bytes_from_fgl_eq`
    for the high 4 bytes. -/
private lemma hi_bytes_from_fgl_eq
    (e2 : MemoryBusEntry FGL) (fgl_hi : FGL)
    (target_nat : ℕ)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256)
    (h_hi_entry : memory_entry_hi e2 = fgl_hi)
    (h_hi_val : fgl_hi.val = target_nat / 4294967296) :
    e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
      = target_nat / 4294967296 := by
  simp only [memory_entry_hi] at h_hi_entry
  have h_cast : (e2.x4 + e2.x5 * 256 + e2.x6 * 65536 + e2.x7 * 16777216 : FGL)
      = (((e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216 : ℕ) : FGL)) := by
    push_cast; ring
  rw [h_cast] at h_hi_entry
  have h_hi_fgl_val := congr_arg Fin.val h_hi_entry
  simp only [Fin.val_natCast] at h_hi_fgl_val
  have h_sum_bound : e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
      < 18446744069414584321 := by omega
  rw [Nat.mod_eq_of_lt h_sum_bound] at h_hi_fgl_val
  omega

/-- **64-bit byte-sum from lo/hi decomposition.** Assembles the full 8-byte
    byte_sum from the lo and hi 4-byte sums expressed in terms of a target
    `BitVec 64` value. Closes the derivation chain: lo_bytes = V.toNat % 2^32,
    hi_bytes = V.toNat / 2^32 → total_byte_sum = V.toNat. -/
private lemma byte_sum_from_lo_hi
    (e2 : MemoryBusEntry FGL) (V : BitVec 64)
    (h_lo : e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      = V.toNat % 4294967296)
    (h_hi : e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
      = V.toNat / 4294967296) :
    e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
      + e2.x4.val * 4294967296 + e2.x5.val * 1099511627776
      + e2.x6.val * 281474976710656 + e2.x7.val * 72057594037927936
    = V.toNat := by
  have h_decomp := Nat.div_add_mod V.toNat 4294967296
  omega

/-! ## JAL: rd ← PC + 4 -/

/-- **`h_rd_val` discharge for JAL (Tier 1).** Derives
    `U64.toBV #v[e2.x0, ..., e2.x7] = PC + 4`
    from circuit primitives:

    1. `h_circuit : jal_circuit_holds m r_main next_pc` — gives
       `store_value = pc + jmp_offset2` via `jal_store_value`.
    2. `h_jmp2 : m.jmp_offset2 r_main = 4` — transpiler pin (from `transpile_JAL`).
    3. `h_e2_lo : memory_entry_lo e2 = m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main) + m.c_0 r_main` — FGL store-value-to-entry-lo match.
    4. `h_e2_hi_val : (memory_entry_hi e2).val = (PC + 4).toNat / 4294967296` — hi lane Nat match.
    5. `h_pc_lo_val : (m.pc r_main + 4 : FGL).val = (PC + 4).toNat % 4294967296` — PC-lo Nat alignment.
    6. Per-byte range bounds on `e2`.

    The conclusion `U64.toBV ... = PC + 4` matches the `h_rd_val :` parameter
    in `Equivalence.Jal.equiv_JAL_metaplan`, enabling Phase 3 inline.

    **Proof chain:** h_circuit → jal_store_value → store_value = pc + jmp_offset2.
    h_jmp2 → store_value = pc + 4. h_e2_lo + jal_store_value → memory_entry_lo = pc + 4.
    h_pc_lo_val → lo bytes sum = (PC+4).toNat % 2^32. h_e2_hi_val → hi bytes sum.
    Combined via byte_sum_from_lo_hi. Closed with K3 pc_plus4_bv64_of_bytes. -/
theorem h_rd_val_jut_jal
    (PC : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- (1) Circuit hypothesis: gives jal_store_value
    (h_circuit : jal_circuit_holds m r_main next_pc)
    -- (2) Transpiler pin: jmp_offset2 = 4
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    -- (3) FGL store-value-to-entry-lo match
    (h_e2_lo : memory_entry_lo e2
      = m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main) + m.c_0 r_main)
    -- (4) Hi lane Nat match: high 4 bytes of the rd-write encode (PC+4).toNat/2^32
    (h_e2_hi_val : (memory_entry_hi e2).val = (PC + 4).toNat / 4294967296)
    -- (5) PC-lo Nat alignment: connects m.pc (FGL) to PC (BitVec 64) at the lo half
    (h_pc_lo_val : (m.pc r_main + 4 : FGL).val = (PC + 4).toNat % 4294967296)
    -- (6) Per-byte range bounds
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = PC + 4 := by
  -- Step 1: Extract store_value = pc + jmp_offset2 from jal_circuit_holds.
  have h_sv := jal_store_value m r_main next_pc h_circuit
  -- h_sv : m.store_pc * (m.pc + m.jmp_offset2 - m.c_0) + m.c_0 = m.pc + m.jmp_offset2
  -- Step 2: Apply jmp_offset2 = 4 to get store_value = pc + 4 : FGL.
  rw [h_jmp2] at h_sv h_e2_lo
  -- Step 3: Combine h_e2_lo and h_sv to get memory_entry_lo e2 = m.pc + 4 : FGL.
  rw [h_sv] at h_e2_lo
  -- h_e2_lo : memory_entry_lo e2 = m.pc + 4
  -- Step 4: Derive lo bytes sum = (PC+4).toNat % 2^32.
  have h_lo_bytes := lo_bytes_from_fgl_eq e2 (m.pc r_main + 4) (PC + 4).toNat
    h0 h1 h2 h3 h_e2_lo h_pc_lo_val
  -- Step 5: Derive the full byte_sum from lo + hi.
  have h_hi_bytes : e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (PC + 4).toNat / 4294967296 := by
    apply hi_bytes_from_fgl_eq e2 (memory_entry_hi e2) (PC + 4).toNat h4 h5 h6 h7 rfl
    exact h_e2_hi_val
  have h_byte_sum := byte_sum_from_lo_hi e2 (PC + 4) h_lo_bytes h_hi_bytes
  -- Step 6: Close with K3.
  exact pc_plus4_bv64_of_bytes PC e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## JALR: rd ← PC + 4 -/

/-- **`h_rd_val` discharge for JALR (Tier 1).** Identical shape to JAL
    — JALR also writes `PC + 4` as the link value. The `PC` here is
    `jalr_input.PC`. Uses `jalr_circuit_holds` → `jalr_store_value`
    instead of JAL's spec theorem.

    **Proof chain:** same as JAL; `jalr_store_value` delivers the same
    `store_value = pc + jmp_offset2` field identity.

    Produces `U64.toBV ... = PC + 4`, matching `h_rd_val :` in
    `Equivalence.Jalr.equiv_JALR_metaplan`. -/
theorem h_rd_val_jut_jalr
    (PC : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- (1) Circuit hypothesis: gives jalr_store_value
    (h_circuit : jalr_circuit_holds m r_main next_pc)
    -- (2) Transpiler pin: jmp_offset2 = 4
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    -- (3) FGL store-value-to-entry-lo match
    (h_e2_lo : memory_entry_lo e2
      = m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main) + m.c_0 r_main)
    -- (4) Hi lane Nat match
    (h_e2_hi_val : (memory_entry_hi e2).val = (PC + 4).toNat / 4294967296)
    -- (5) PC-lo Nat alignment
    (h_pc_lo_val : (m.pc r_main + 4 : FGL).val = (PC + 4).toNat % 4294967296)
    -- (6) Per-byte range bounds
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = PC + 4 := by
  have h_sv := jalr_store_value m r_main next_pc h_circuit
  rw [h_jmp2] at h_sv h_e2_lo
  rw [h_sv] at h_e2_lo
  have h_lo_bytes := lo_bytes_from_fgl_eq e2 (m.pc r_main + 4) (PC + 4).toNat
    h0 h1 h2 h3 h_e2_lo h_pc_lo_val
  have h_hi_bytes : e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (PC + 4).toNat / 4294967296 := by
    apply hi_bytes_from_fgl_eq e2 (memory_entry_hi e2) (PC + 4).toNat h4 h5 h6 h7 rfl
    exact h_e2_hi_val
  have h_byte_sum := byte_sum_from_lo_hi e2 (PC + 4) h_lo_bytes h_hi_bytes
  exact pc_plus4_bv64_of_bytes PC e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## LUI: rd ← BitVec.signExtend 64 (imm ++ 0#12) -/

/-- **`h_rd_val` discharge for LUI (Tier 1).** Derives
    `U64.toBV #v[e2.x0, ..., e2.x7] = BitVec.signExtend 64 (imm ++ 0#12)`
    from circuit primitives:

    1. `h_circuit : lui_archetype_circuit_holds m r_main next_pc` — gives
       `c_0 = b_0` and `c_1 = b_1` via `lui_archetype_store_value_lo/hi`.
    2. `h_lane_rd : register_write_lanes_match m r_main e2` — ties
       `c_0/c_1` to `memory_entry_lo/hi e2` (valid for LUI since `c = b = imm`).
    3. `h_b0_lo : (m.b_0 r_main).val = (imm ++ 0#12).toNat` — transpiler b-lane pin.
    4. `h_b1_hi : (m.b_1 r_main).val = (BitVec.signExtend 64 (imm ++ 0#12)).toNat / 4294967296`.
    5. `h_lo_is_lo : (BitVec.signExtend 64 (imm ++ 0#12)).toNat % 4294967296 = (imm ++ 0#12).toNat`.
    6. Per-byte range bounds on `e2`.

    **Proof chain:** h_circuit → lui_store_value_lo/hi → c_0 = b_0, c_1 = b_1.
    h_lane_rd → memory_entry_lo/hi = c_0/c_1 = b_0/b_1.
    h_b0_lo/h_b1_hi → Nat values. signExtend_imm20_nat_lanes → byte_sum.
    K3 u64_toBV_of_imm20_lanes closes the goal. -/
theorem h_rd_val_jut_lui
    (imm : BitVec 20)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- (1) Circuit hypothesis
    (h_circuit : lui_archetype_circuit_holds m r_main next_pc)
    -- (2) Lane-match: c_0 = memory_entry_lo e2, c_1 = memory_entry_hi e2
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- (3) Transpiler b-lane Nat pin: b_0.val = (imm ++ 0#12).toNat
    (h_b0_lo : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    -- (4) Transpiler b-lane Nat pin: b_1.val = high 32 bits of sign-extended imm
    (h_b1_hi : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    -- (5) Low-half identity: signExtend preserves the low 32 bits
    (h_lo_is_lo : (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat % 4294967296
      = (imm ++ (0 : BitVec 12)).toNat)
    -- (6) Per-byte range bounds
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  -- Step 1: Extract c_0 = b_0 and c_1 = b_1 from the LUI circuit.
  have h_sv_lo := lui_store_value_lo m r_main next_pc h_circuit
  -- h_sv_lo : store_pc * (pc + jmp_offset2 - c_0) + c_0 = b_0
  -- For LUI (store_pc = 0): store_value_lo = c_0 = b_0.
  have h_sv_hi := lui_store_value_hi m r_main next_pc h_circuit
  -- h_sv_hi : (1 - store_pc) * c_1 = b_1
  -- For LUI (store_pc = 0): (1 - 0) * c_1 = c_1 = b_1.
  obtain ⟨_h_subset, h_mode⟩ := h_circuit
  obtain ⟨_h_ext, _h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  -- From store_pc = 0: simplify sv_lo to c_0 = b_0 and sv_hi to c_1 = b_1.
  rw [h_store_pc] at h_sv_lo h_sv_hi
  simp only [zero_mul, zero_add, sub_zero, one_mul] at h_sv_lo h_sv_hi
  -- h_sv_lo : c_0 r_main = b_0 r_main
  -- h_sv_hi : c_1 r_main = b_1 r_main
  -- Step 2: Extract c_0 = memory_entry_lo, c_1 = memory_entry_hi from lane-match.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_c0_eq, h_c1_eq⟩ := h_lane_rd
  -- h_c0_eq : c_0 r_main = memory_entry_lo e2
  -- h_c1_eq : c_1 r_main = memory_entry_hi e2
  -- Step 3: Combine to get memory_entry_lo = b_0 and memory_entry_hi = b_1.
  have h_lo_entry : memory_entry_lo e2 = m.b_0 r_main := by rw [← h_c0_eq, h_sv_lo]
  have h_hi_entry : memory_entry_hi e2 = m.b_1 r_main := by rw [← h_c1_eq, h_sv_hi]
  -- Step 4: Derive lo bytes sum using the FGL→Nat bridge.
  -- h_b0_lo says b_0.val = (imm ++ 0#12).toNat = sext.toNat % 2^32 (by h_lo_is_lo).
  have h_b0_as_sext_lo : (m.b_0 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat % 4294967296 := by
    rw [h_b0_lo]; exact h_lo_is_lo.symm
  have h_lo_bytes := lo_bytes_from_fgl_eq e2 (m.b_0 r_main)
    (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat
    h0 h1 h2 h3 h_lo_entry h_b0_as_sext_lo
  -- Step 5: Derive hi bytes.
  have h_hi_bytes := hi_bytes_from_fgl_eq e2 (m.b_1 r_main)
    (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat
    h4 h5 h6 h7 h_hi_entry h_b1_hi
  -- Step 6: Assemble byte_sum = signExtend.toNat.
  set V := BitVec.signExtend 64 (imm ++ (0 : BitVec 12))
  have h_byte_sum := byte_sum_from_lo_hi e2 V h_lo_bytes h_hi_bytes
  -- Step 7: Close with K3.
  exact u64_toBV_of_imm20_lanes imm e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## AUIPC: rd ← PC + BitVec.signExtend 64 (imm ++ 0#12) -/

/-- **`h_rd_val` discharge for AUIPC (Tier 1).** Derives
    `U64.toBV #v[e2.x0, ..., e2.x7] = PC + BitVec.signExtend 64 (imm ++ 0#12)`
    from circuit primitives:

    1. `h_circuit : auipc_archetype_circuit_holds m r_main next_pc` — gives
       `store_value = pc + jmp_offset2` via `auipc_store_value_lo`.
    2. `h_jmp2 : m.jmp_offset2 r_main = <imm_field>` — transpiler pin.
    3. `h_e2_lo : memory_entry_lo e2 = m.store_pc * (pc + jmp_offset2 - c_0) + c_0` — FGL.
    4. `h_e2_hi_val : (memory_entry_hi e2).val = (PC + signExtend 64 (imm ++ 0#12)).toNat / 4294967296`.
    5. `h_pci_lo_val : (m.pc r_main + m.jmp_offset2 r_main : FGL).val = (PC + signExtend 64 (imm ++ 0#12)).toNat % 4294967296`.
    6. Per-byte range bounds on `e2`.

    **Proof chain:** h_circuit → auipc_store_value_lo → store_value = pc + jmp_offset2.
    h_e2_lo + auipc_store_value_lo → memory_entry_lo = pc + jmp_offset2 : FGL.
    h_pci_lo_val → lo bytes = (PC + sext imm).toNat % 2^32.
    h_e2_hi_val → hi bytes. byte_sum_from_lo_hi + BitVec.eq_of_toNat_eq closes goal. -/
theorem h_rd_val_jut_auipc
    (PC : BitVec 64)
    (imm : BitVec 20)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- (1) Circuit hypothesis
    (h_circuit : auipc_archetype_circuit_holds m r_main next_pc)
    -- (2) FGL store-value-to-entry-lo match
    (h_e2_lo : memory_entry_lo e2
      = m.store_pc r_main * (m.pc r_main + m.jmp_offset2 r_main - m.c_0 r_main) + m.c_0 r_main)
    -- (3) Hi lane Nat match: high 4 bytes of the rd-write
    (h_e2_hi_val : (memory_entry_hi e2).val
      = (PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    -- (4) PC+imm lo Nat alignment
    (h_pci_lo_val : (m.pc r_main + m.jmp_offset2 r_main : FGL).val
      = (PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat % 4294967296)
    -- (5) Per-byte range bounds
    (h0 : e2.x0.val < 256) (h1 : e2.x1.val < 256)
    (h2 : e2.x2.val < 256) (h3 : e2.x3.val < 256)
    (h4 : e2.x4.val < 256) (h5 : e2.x5.val < 256)
    (h6 : e2.x6.val < 256) (h7 : e2.x7.val < 256) :
    U64.toBV #v[(e2.x0 : BitVec 8), (e2.x1 : BitVec 8), (e2.x2 : BitVec 8), (e2.x3 : BitVec 8),
                (e2.x4 : BitVec 8), (e2.x5 : BitVec 8), (e2.x6 : BitVec 8), (e2.x7 : BitVec 8)]
      = PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  -- Step 1: Extract store_value = pc + jmp_offset2 from auipc circuit.
  have h_sv := auipc_store_value_lo m r_main next_pc h_circuit
  -- h_sv : store_pc * (pc + jmp_offset2 - c_0) + c_0 = pc + jmp_offset2
  -- Step 2: Combine h_e2_lo and h_sv to get memory_entry_lo = pc + jmp_offset2 : FGL.
  rw [h_sv] at h_e2_lo
  -- Step 3: Derive lo bytes sum using the FGL→Nat bridge.
  set V := PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) with hV_def
  have h_lo_bytes := lo_bytes_from_fgl_eq e2 (m.pc r_main + m.jmp_offset2 r_main) V.toNat
    h0 h1 h2 h3 h_e2_lo h_pci_lo_val
  -- Step 4: Derive hi bytes.
  have h_hi_bytes : e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
      = V.toNat / 4294967296 := by
    apply hi_bytes_from_fgl_eq e2 (memory_entry_hi e2) V.toNat h4 h5 h6 h7 rfl
    exact h_e2_hi_val
  -- Step 5: Assemble byte_sum = V.toNat.
  have h_byte_sum := byte_sum_from_lo_hi e2 V h_lo_bytes h_hi_bytes
  -- Step 6: Close with BitVec.eq_of_toNat_eq + u64_toBV_of_bytes_toNat.
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat e2.x0 e2.x1 e2.x2 e2.x3 e2.x4 e2.x5 e2.x6 e2.x7
      h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

end ZiskFv.Equivalence.RdValDerivation.JumpUType
