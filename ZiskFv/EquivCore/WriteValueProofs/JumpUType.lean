import Mathlib

import ZiskFv.Field.Goldilocks
import ZiskFv.Airs.Bus.Interaction
import ZiskFv.Bits.PackedBitVec
import ZiskFv.Bits.PackedBitVec.Extensions
import ZiskFv.Bits.PackedBitVec.NoWrap
import ZiskFv.Bits.PackedBitVec.WidePCNoWrap
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.MemoryBus
import ZiskFv.Channels.MemoryBusBytes
import ZiskFv.ZiskCircuit.Jal
import ZiskFv.ZiskCircuit.Jalr
import ZiskFv.ZiskCircuit.LoadUpperImmediate
import ZiskFv.ZiskCircuit.AddUpperImmediatePC
import ZiskFv.Tactics.UTypeArchetype

/-!
# WriteValueProofs.JumpUType — `h_rd_val` discharge lemmas for JAL/JALR/LUI/AUIPC

Each lemma in this file is **Tier 1**: it derives the `h_rd_val` conclusion
from circuit primitives directly. No output-equality residuals survive in any
parameter list. Parameter trust classes:

* For **JAL/JALR**: `jal_circuit_holds` / `jalr_circuit_holds` (field-level
  `store_value = pc + jmp_offset2`) + transpiler pin `jmp_offset2 = 4` +
  FGL store_value-to-entry-lo match (`h_entry_lo_eq`) + hi-lane Nat match
  (`h_entry_hi_nat`) + PC-lo FGL Nat alignment (`h_pc_fgl_lo_nat`).
  The proof derives `h_byte_sum` internally via FGL→Nat lifting and closes
  with K3 `pc_plus4_bv64_of_bytes`.

* For **LUI**: `lui_archetype_circuit_holds` + `register_write_lanes_match`
  (ties `c_0`/`c_1` to entry bytes) + transpiler b-lane Nat pins (`h_imm_lo_nat`,
  `h_imm_hi_nat`, renamed from `h_b0_lo`/`h_b1_hi`) + K3
  `u64_toBV_of_imm20_lanes`. The `h_lo_is_lo` pure-math fact is now derived
  internally using `BitVec.toNat_signExtend`.

* For **AUIPC**: `auipc_archetype_circuit_holds` + FGL store_value-to-entry-lo
  match (`h_entry_lo_eq`) + hi-lane Nat match (`h_entry_hi_nat`) + combined
  PC+imm FGL Nat alignment (`h_pci_fgl_lo_nat`).

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
(`h_entry_lo_eq`) are the interface point between Main's internal circuit
constraints and the memory bus's byte emission. The Nat hi-half hypotheses
(`h_entry_hi_nat`) capture the high 4 bytes of the 64-bit value; the
transpiler b-lane Nat pins (`h_imm_lo_nat`, `h_imm_hi_nat`) tie Sail's
`imm : BitVec 20` to Main's `b` columns (transpile-trusted surface).
-/

set_option maxHeartbeats 800000

namespace ZiskFv.EquivCore.WriteValueProofs.JumpUType

open Goldilocks
open Interaction
open ZiskFv.Channels.MemoryBusBytes (byteAt byteOf byteOf_val_lt_256 byteOf_val_sum_eq)
open ZiskFv.Airs.Main
open ZiskFv.Airs.MemoryBus
open ZiskFv.ZiskCircuit.Jal
open ZiskFv.ZiskCircuit.Jalr
open ZiskFv.ZiskCircuit.LoadUpperImmediate
open ZiskFv.ZiskCircuit.AddUpperImmediatePC
open ZiskFv.Tactics.UTypeArchetype
open ZiskFv.PackedBitVec
open ZiskFv.PackedBitVec.Extensions
open ZiskFv.PackedBitVec.WidePCNoWrap
open ZiskFv.Trusted


/-! ## Shared internal helper

Both JAL and JALR (and AUIPC in a similar form) need to derive a Nat byte_sum
from FGL lo/hi equalities plus byte range bounds. This private lemma handles
the common arithmetic. -/

/-- **FGL lane-to-byte-sum bridge (lo half).** Given:
    - `memory_entry_lo e2 = fgl_lo : FGL`
    - `(fgl_lo).val = target_nat % 4294967296`

    derives `(byteAt e2 0).val + (byteAt e2 1).val*256 + (byteAt e2 2).val*65536
      + (byteAt e2 3).val*16777216 = target_nat % 4294967296`.

    Used to connect the lo 4 bytes of the memory bus entry to the
    FGL-level store_value expression. -/
private lemma lo_bytes_from_fgl_eq
    (e2 : MemoryBusEntry FGL) (fgl_lo : FGL)
    (target_nat : ℕ)
    (h_lo_entry : memory_entry_lo e2 = fgl_lo)
    (h_lo_val : fgl_lo.val = target_nat % 4294967296) :
    (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = target_nat % 4294967296 := by
  -- memory_entry_lo e2 = e2.value_0 by definition.
  simp only [memory_entry_lo] at h_lo_entry
  -- The byte projections byteAt e2 0..3 collapse to byteOf e2.value_0 0..3.
  -- e2.value_0.val < 2^32 follows from h_lo_entry + h_lo_val (a mod is < the modulus).
  have h_v0_lt : e2.value_0.val < 4294967296 := by
    rw [h_lo_entry]; rw [h_lo_val]; exact Nat.mod_lt _ (by decide)
  have h_sum := byteOf_val_sum_eq e2.value_0 h_v0_lt
  -- byteAt e2 i for i < 4 unfolds to byteOf e2.value_0 i; @[reducible].
  show (byteOf e2.value_0 0).val + (byteOf e2.value_0 1).val * 256
       + (byteOf e2.value_0 2).val * 65536 + (byteOf e2.value_0 3).val * 16777216
       = target_nat % 4294967296
  rw [h_sum, h_lo_entry, h_lo_val]

/-- **FGL lane-to-byte-sum bridge (hi half).** Symmetric with `lo_bytes_from_fgl_eq`
    for the high 4 bytes. -/
private lemma hi_bytes_from_fgl_eq
    (e2 : MemoryBusEntry FGL) (fgl_hi : FGL)
    (target_nat : ℕ)
    (h_hi_entry : memory_entry_hi e2 = fgl_hi)
    (h_hi_val : fgl_hi.val = target_nat / 4294967296)
    (h_hi_bound : target_nat / 4294967296 < 4294967296) :
    (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = target_nat / 4294967296 := by
  simp only [memory_entry_hi] at h_hi_entry
  have h_v1_lt : e2.value_1.val < 4294967296 := by
    rw [h_hi_entry, h_hi_val]; exact h_hi_bound
  have h_sum := byteOf_val_sum_eq e2.value_1 h_v1_lt
  show (byteOf e2.value_1 0).val + (byteOf e2.value_1 1).val * 256
       + (byteOf e2.value_1 2).val * 65536 + (byteOf e2.value_1 3).val * 16777216
       = target_nat / 4294967296
  rw [h_sum, h_hi_entry, h_hi_val]

/-- **64-bit byte-sum from lo/hi decomposition.** Assembles the full 8-byte
    byte_sum from the lo and hi 4-byte sums expressed in terms of a target
    `BitVec 64` value. Closes the derivation chain: lo_bytes = V.toNat % 2^32,
    hi_bytes = V.toNat / 2^32 → total_byte_sum = V.toNat. -/
private lemma byte_sum_from_lo_hi
    (e2 : MemoryBusEntry FGL) (V : BitVec 64)
    (h_lo : (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = V.toNat % 4294967296)
    (h_hi : (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = V.toNat / 4294967296) :
    (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      + (byteAt e2 4).val * 4294967296 + (byteAt e2 5).val * 1099511627776
      + (byteAt e2 6).val * 281474976710656 + (byteAt e2 7).val * 72057594037927936
    = V.toNat := by
  have h_decomp := Nat.div_add_mod V.toNat 4294967296
  omega

/-! ## JAL: rd ← PC + 4 -/

/-- **`h_rd_val` discharge for JAL (Tier 1).**

    Derives `U64.toBV #v[byteAt e2 0, ..., byteAt e2 7] = PC + 4` from circuit
    primitives. Exposes only {CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE,
    TRANSPILE-PIN} parameters — no OUTPUT-EQ residuals.

    **Parameters and trust class.**

    * `h_circuit : jal_circuit_holds m r_main next_pc` — CIRCUIT-CONSTRAINT.
      Gives `jal_store_value` and the JAL-mode witnesses
      (`is_external_op = 0`, `op = OP_FLAG`) needed to invoke the
      `transpile_PC_for_JAL` axiom internally.
    * `h_jmp2 : m.jmp_offset2 r_main = 4` — TRANSPILE-PIN (from
      `transpile_JAL`).
    * `h_lane_lo : store_pc_lanes_match_lo m r_main e2` and
      `h_lane_hi : store_pc_lanes_match_hi m r_main e2` — LANE-MATCH
      (S4 produces these from a memory-bus emission witness via
      `store_pc_lanes_match_{lo,hi}_of_bus_emission`).
    * `h_pc_bound : PC.toNat < GL_prime - 4` — RANGE (PC-trajectory
      bound; immediate from the ROM `pc < 2^32` invariant).
    * `h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296` — RANGE
      (FGL-side lo-half range; immediate from the byte decomposition
      of the lo lane).
    * `h_pc_offset_lt_2_32 : (PC + 4#64).toNat < 4294967296` — RANGE
      (32-bit bound on the link address; immediate from the ROM
      `pc < 2^32` invariant).
    * `h0..h7 : (byteAt e2 i).val < 256` — RANGE (per-byte range bounds).

    **Proof chain.** `transpile_PC_for_JAL` (gated by mode witnesses
    extracted from `h_circuit`) gives `(m.pc r_main).val = PC.toNat`.
    `jal_store_value_lo_bv` composes that with `h_circuit, h_jmp2,
    h_lane_lo, h_pc_bound, h_lo_bound` to deliver
    `(memory_entry_lo e2).val = (PC + 4#64).toNat % 2^32`.
    `jal_store_value_hi_bv` composes `h_circuit, h_lane_hi,
    h_pc_offset_lt_2_32` to deliver
    `(memory_entry_hi e2).val = (PC + 4#64).toNat / 2^32`.
    The internal helpers `lo_bytes_from_fgl_eq` / `hi_bytes_from_fgl_eq`
    bridge to the byte-sum form, and `pc_plus4_bv64_of_bytes` (K3)
    closes the goal. -/
lemma h_rd_val_jut_jal
    (PC : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- CIRCUIT-CONSTRAINT
    (h_circuit : jal_circuit_holds m r_main next_pc)
    -- TRANSPILE-PIN
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    -- LANE-MATCH (lo + hi)
    (h_lane_lo : store_pc_lanes_match_lo m r_main e2)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e2)
    -- RANGE: PC trajectory + lo-half FGL bound + 32-bit link-addr bound
    (h_pc_bound : PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (PC + 4#64).toNat < 4294967296)
    -- RANGE: per-byte bounds
    (h0 : (byteAt e2 0).val < 256) (h1 : (byteAt e2 1).val < 256)
    (h2 : (byteAt e2 2).val < 256) (h3 : (byteAt e2 3).val < 256)
    (h4 : (byteAt e2 4).val < 256) (h5 : (byteAt e2 5).val < 256)
    (h6 : (byteAt e2 6).val < 256) (h7 : (byteAt e2 7).val < 256) :
    U64.toBV #v[(byteAt e2 0 : BitVec 8), (byteAt e2 1 : BitVec 8),
                (byteAt e2 2 : BitVec 8), (byteAt e2 3 : BitVec 8),
                (byteAt e2 4 : BitVec 8), (byteAt e2 5 : BitVec 8),
                (byteAt e2 6 : BitVec 8), (byteAt e2 7 : BitVec 8)]
      = PC + 4 := by
  -- Extract JAL mode witnesses from h_circuit and apply S1's
  -- transpile_PC_for_JAL axiom to derive the FGL→BitVec PC bridge.
  have h_mode := h_circuit.2
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
  have h_pc_bridge : (m.pc r_main).val = PC.toNat :=
    transpile_PC_for_JAL m r_main PC h_ext h_op
  -- Apply S3's lo/hi BitVec bridges.
  have h_lo_val : (memory_entry_lo e2).val = (PC + 4#64).toNat % 4294967296 :=
    jal_store_value_lo_bv m r_main next_pc PC e2
      h_circuit h_jmp2 h_lane_lo h_pc_bridge h_pc_bound h_lo_bound
  have h_hi_val : (memory_entry_hi e2).val = (PC + 4#64).toNat / 4294967296 :=
    jal_store_value_hi_bv m r_main next_pc PC e2
      h_circuit h_lane_hi h_pc_offset_lt_2_32
  -- Convert (PC + 4#64) to (PC + 4) — definitionally equal.
  have h_pc4_eq : (PC + 4#64) = (PC + 4) := rfl
  rw [h_pc4_eq] at h_lo_val h_hi_val
  -- Bridge each .val equality to the FGL form via the helpers.
  have h_lo_bytes :
      (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (PC + 4).toNat % 4294967296 :=
    lo_bytes_from_fgl_eq e2 (memory_entry_lo e2) (PC + 4).toNat
      rfl h_lo_val
  have h_hi_bound : (PC + 4).toNat / 4294967296 < 4294967296 :=
    Nat.div_lt_of_lt_mul (by have := (PC + 4).isLt; norm_num at this ⊢; omega)
  have h_hi_bytes :
      (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (PC + 4).toNat / 4294967296 :=
    hi_bytes_from_fgl_eq e2 (memory_entry_hi e2) (PC + 4).toNat
      rfl h_hi_val h_hi_bound
  -- Assemble byte_sum and close with K3.
  have h_byte_sum := byte_sum_from_lo_hi e2 (PC + 4) h_lo_bytes h_hi_bytes
  exact pc_plus4_bv64_of_bytes PC (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## JALR: rd ← PC + 4 -/

/-- **`h_rd_val` discharge for JALR (Tier 1).**

    Identical shape to JAL — JALR also writes `PC + 4` as the link
    value; only the underlying circuit-hypothesis predicate differs
    (`jalr_circuit_holds` instead of `jal_circuit_holds`). Uses S3's
    `jalr_store_value_lo_bv` / `_hi_bv`. The PC bridge is established
    internally via `transpile_PC_for_JALR` (gated by JALR mode
    witnesses `is_external_op = 0`, `op = OP_COPYB = 1` from
    `h_circuit`).

    Parameter classes match `h_rd_val_jut_jal` exactly:
    {CIRCUIT-CONSTRAINT, TRANSPILE-PIN, LANE-MATCH, RANGE}. -/
lemma h_rd_val_jut_jalr
    (PC : BitVec 64)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- CIRCUIT-CONSTRAINT
    (h_circuit : jalr_circuit_holds m r_main next_pc)
    -- TRANSPILE-PIN
    (h_jmp2 : m.jmp_offset2 r_main = 4)
    -- LANE-MATCH (lo + hi)
    (h_lane_lo : store_pc_lanes_match_lo m r_main e2)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e2)
    -- RANGE: PC trajectory + lo-half FGL bound + 32-bit link-addr bound
    (h_pc_bound : PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (PC + 4#64).toNat < 4294967296)
    -- RANGE: per-byte bounds
    (h0 : (byteAt e2 0).val < 256) (h1 : (byteAt e2 1).val < 256)
    (h2 : (byteAt e2 2).val < 256) (h3 : (byteAt e2 3).val < 256)
    (h4 : (byteAt e2 4).val < 256) (h5 : (byteAt e2 5).val < 256)
    (h6 : (byteAt e2 6).val < 256) (h7 : (byteAt e2 7).val < 256) :
    U64.toBV #v[(byteAt e2 0 : BitVec 8), (byteAt e2 1 : BitVec 8),
                (byteAt e2 2 : BitVec 8), (byteAt e2 3 : BitVec 8),
                (byteAt e2 4 : BitVec 8), (byteAt e2 5 : BitVec 8),
                (byteAt e2 6 : BitVec 8), (byteAt e2 7 : BitVec 8)]
      = PC + 4 := by
  -- Extract JALR mode witnesses + apply transpile_PC_for_JALR.
  have h_mode := h_circuit.2
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
  have h_pc_bridge : (m.pc r_main).val = PC.toNat :=
    transpile_PC_for_JALR m r_main PC h_ext h_op
  -- Apply S3's lo/hi BitVec bridges (JALR variants).
  have h_lo_val : (memory_entry_lo e2).val = (PC + 4#64).toNat % 4294967296 :=
    jalr_store_value_lo_bv m r_main next_pc PC e2
      h_circuit h_jmp2 h_lane_lo h_pc_bridge h_pc_bound h_lo_bound
  have h_hi_val : (memory_entry_hi e2).val = (PC + 4#64).toNat / 4294967296 :=
    jalr_store_value_hi_bv m r_main next_pc PC e2
      h_circuit h_lane_hi h_pc_offset_lt_2_32
  -- PC + 4#64 = PC + 4 definitionally.
  have h_pc4_eq : (PC + 4#64) = (PC + 4) := rfl
  rw [h_pc4_eq] at h_lo_val h_hi_val
  -- Bridge to byte-sum form.
  have h_lo_bytes :
      (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (PC + 4).toNat % 4294967296 :=
    lo_bytes_from_fgl_eq e2 (memory_entry_lo e2) (PC + 4).toNat
      rfl h_lo_val
  have h_hi_bound : (PC + 4).toNat / 4294967296 < 4294967296 :=
    Nat.div_lt_of_lt_mul (by have := (PC + 4).isLt; norm_num at this ⊢; omega)
  have h_hi_bytes :
      (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (PC + 4).toNat / 4294967296 :=
    hi_bytes_from_fgl_eq e2 (memory_entry_hi e2) (PC + 4).toNat
      rfl h_hi_val h_hi_bound
  -- Assemble byte_sum and close with K3.
  have h_byte_sum := byte_sum_from_lo_hi e2 (PC + 4) h_lo_bytes h_hi_bytes
  exact pc_plus4_bv64_of_bytes PC (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## LUI: rd ← BitVec.signExtend 64 (imm ++ 0#12) -/

/-- **`h_rd_val` discharge for LUI (Tier 1).** Derives
    `U64.toBV #v[byteAt e2 0, ..., byteAt e2 7] = BitVec.signExtend 64 (imm ++ 0#12)`
    from circuit primitives:

    1. `h_circuit : lui_archetype_circuit_holds m r_main next_pc` — gives
       `c_0 = b_0` and `c_1 = b_1` via `lui_archetype_store_value_lo/hi`.
    2. `h_lane_rd : register_write_lanes_match m r_main e2` — ties
       `c_0/c_1` to `memory_entry_lo/hi e2` (valid for LUI since `c = b = imm`).
    3. `h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ 0#12).toNat` — transpiler b-lane pin.
    4. `h_imm_hi_nat : (m.b_1 r_main).val = (BitVec.signExtend 64 (imm ++ 0#12)).toNat / 4294967296` — transpiler b-lane pin.
    5. Per-byte range bounds on `e2`.

    The low-half identity `(sext 64 (imm ++ 0#12)).toNat % 2^32 = (imm ++ 0#12).toNat`
    is derived internally from `BitVec.toNat_signExtend`.

    **Proof chain:** h_circuit → lui_store_value_lo/hi → c_0 = b_0, c_1 = b_1.
    h_lane_rd → memory_entry_lo/hi = c_0/c_1 = b_0/b_1.
    h_imm_lo_nat/h_imm_hi_nat → Nat values. Internal derivation of low-half identity.
    K3 u64_toBV_of_imm20_lanes closes the goal. -/
lemma h_rd_val_jut_lui
    (imm : BitVec 20)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- (1) Circuit hypothesis
    (h_circuit : lui_archetype_circuit_holds m r_main next_pc)
    -- (2) Lane-match: c_0 = memory_entry_lo e2, c_1 = memory_entry_hi e2
    (h_lane_rd : register_write_lanes_match m r_main e2)
    -- (3) Transpiler b-lane Nat pin: b_0.val = (imm ++ 0#12).toNat
    (h_imm_lo_nat : (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat)
    -- (4) Transpiler b-lane Nat pin: b_1.val = high 32 bits of sign-extended imm
    (h_imm_hi_nat : (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296)
    -- (5) Per-byte range bounds
    (h0 : (byteAt e2 0).val < 256) (h1 : (byteAt e2 1).val < 256)
    (h2 : (byteAt e2 2).val < 256) (h3 : (byteAt e2 3).val < 256)
    (h4 : (byteAt e2 4).val < 256) (h5 : (byteAt e2 5).val < 256)
    (h6 : (byteAt e2 6).val < 256) (h7 : (byteAt e2 7).val < 256) :
    U64.toBV #v[(byteAt e2 0 : BitVec 8), (byteAt e2 1 : BitVec 8),
                (byteAt e2 2 : BitVec 8), (byteAt e2 3 : BitVec 8),
                (byteAt e2 4 : BitVec 8), (byteAt e2 5 : BitVec 8),
                (byteAt e2 6 : BitVec 8), (byteAt e2 7 : BitVec 8)]
      = BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  -- Derive the low-half identity internally.
  -- (BitVec.signExtend 64 v).toNat % 2^32 = v.toNat for v : BitVec 32.
  -- Proof: signExtend adds 2^64 - 2^32 to toNat when msb = 1, which is
  -- divisible by 2^32; and setWidth 64 v has toNat = v.toNat (since v.toNat < 2^32).
  set v := imm ++ (0 : BitVec 12) with hv_def
  have hv_lt : v.toNat < 4294967296 := by
    have := v.isLt; norm_num at this; omega
  have h_lo_is_lo : (BitVec.signExtend 64 v).toNat % 4294967296 = v.toNat := by
    rw [BitVec.toNat_signExtend]
    have h_setWidth : (BitVec.setWidth 64 v).toNat = v.toNat := by
      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    rw [h_setWidth]
    split_ifs with h_msb
    · have : (2 : ℕ) ^ 64 - 2 ^ 32 = (2 ^ 32 - 1) * 4294967296 := by norm_num
      rw [this, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hv_lt
    · simp only [add_zero]; exact Nat.mod_eq_of_lt hv_lt
  -- Extract c_0 = b_0 and c_1 = b_1 from the LUI circuit.
  have h_sv_lo := lui_store_value_lo m r_main next_pc h_circuit
  have h_sv_hi := lui_store_value_hi m r_main next_pc h_circuit
  have h_mode := h_circuit.2
  obtain ⟨_h_ext, _h_op, _h_m32, _h_set_pc, h_store_pc⟩ := h_mode
  -- From store_pc = 0: simplify sv_lo to c_0 = b_0 and sv_hi to c_1 = b_1.
  rw [h_store_pc] at h_sv_lo h_sv_hi
  simp only [zero_mul, zero_add, sub_zero, one_mul] at h_sv_lo h_sv_hi
  -- Extract c_0 = memory_entry_lo, c_1 = memory_entry_hi from lane-match.
  simp only [register_write_lanes_match] at h_lane_rd
  obtain ⟨h_c0_eq, h_c1_eq⟩ := h_lane_rd
  -- Combine to get memory_entry_lo = b_0 and memory_entry_hi = b_1.
  have h_lo_entry : memory_entry_lo e2 = m.b_0 r_main := by rw [← h_c0_eq, h_sv_lo]
  have h_hi_entry : memory_entry_hi e2 = m.b_1 r_main := by rw [← h_c1_eq, h_sv_hi]
  -- Derive lo bytes sum using the FGL→Nat bridge.
  have h_b0_as_sext_lo : (m.b_0 r_main).val
      = (BitVec.signExtend 64 v).toNat % 4294967296 := by
    rw [h_imm_lo_nat]; exact h_lo_is_lo.symm
  have h_lo_bytes := lo_bytes_from_fgl_eq e2 (m.b_0 r_main)
    (BitVec.signExtend 64 v).toNat
    h_lo_entry h_b0_as_sext_lo
  -- Derive hi bytes.
  have h_hi_bound : (BitVec.signExtend 64 v).toNat / 4294967296 < 4294967296 := by
    have h_le := (BitVec.signExtend 64 v).isLt
    have : (BitVec.signExtend 64 v).toNat < 2 ^ 64 := h_le
    have h64 : (2 : ℕ) ^ 64 = 4294967296 * 4294967296 := by norm_num
    rw [h64] at this
    exact Nat.div_lt_of_lt_mul (by linarith)
  have h_hi_bytes := hi_bytes_from_fgl_eq e2 (m.b_1 r_main)
    (BitVec.signExtend 64 v).toNat
    h_hi_entry h_imm_hi_nat h_hi_bound
  -- Assemble byte_sum = signExtend.toNat.
  have h_byte_sum := byte_sum_from_lo_hi e2 (BitVec.signExtend 64 v) h_lo_bytes h_hi_bytes
  -- Close with K3.
  exact u64_toBV_of_imm20_lanes imm (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
    (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
    h0 h1 h2 h3 h4 h5 h6 h7 h_byte_sum

/-! ## AUIPC: rd ← PC + BitVec.signExtend 64 (imm ++ 0#12) -/

/-- **`h_rd_val` discharge for AUIPC (Tier 1).**

    Derives `U64.toBV #v[byteAt e2 0, ..., byteAt e2 7] = PC + signExtend 64 (imm ++ 0#12)`
    from circuit primitives. AUIPC differs from JAL/JALR in two ways:

    1. The offset is `signExtend 64 (imm ++ 0#12)` rather than the
       constant 4. The transpile contract (`transpile_AUIPC`) pins
       `m.jmp_offset2 r = imm_offset` for some FGL representative, but
       the BitVec-side lift requires the caller to supply
       `h_offset_bridge : (m.jmp_offset2 r_main).val = (signExtend 64 (imm ++ 0#12)).toNat`.
    2. The PC bridge is gated by AUIPC's mode witnesses
       (`is_external_op = 0`, `op = OP_FLAG`) — extracted from
       `h_circuit` and combined with `transpile_PC_for_AUIPC`.

    Parameter classes: {CIRCUIT-CONSTRAINT, LANE-MATCH, RANGE,
    TRANSPILE-BRIDGE}. Note: there is no JAL-style "jmp2 = 4"
    TRANSPILE-PIN here — for AUIPC the offset is `imm`-dependent and is
    routed through the `h_offset_bridge` TRANSPILE-BRIDGE parameter
    instead. -/
lemma h_rd_val_jut_auipc
    (PC : BitVec 64)
    (imm : BitVec 20)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (next_pc : FGL)
    (e2 : MemoryBusEntry FGL)
    -- CIRCUIT-CONSTRAINT
    (h_circuit : auipc_archetype_circuit_holds m r_main next_pc)
    -- TRANSPILE-BRIDGE: jmp_offset2 lifts to (sext (imm ++ 0#12)).toNat
    (h_offset_bridge : (m.jmp_offset2 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat)
    -- LANE-MATCH (lo + hi)
    (h_lane_lo : store_pc_lanes_match_lo m r_main e2)
    (h_lane_hi : store_pc_lanes_match_hi m r_main e2)
    -- RANGE: no-wrap PC+offset bound + lo-half FGL bound + 32-bit bound
    (h_no_wrap :
      PC.toNat + (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat < 4294967296)
    -- RANGE: per-byte bounds
    (h0 : (byteAt e2 0).val < 256) (h1 : (byteAt e2 1).val < 256)
    (h2 : (byteAt e2 2).val < 256) (h3 : (byteAt e2 3).val < 256)
    (h4 : (byteAt e2 4).val < 256) (h5 : (byteAt e2 5).val < 256)
    (h6 : (byteAt e2 6).val < 256) (h7 : (byteAt e2 7).val < 256) :
    U64.toBV #v[(byteAt e2 0 : BitVec 8), (byteAt e2 1 : BitVec 8),
                (byteAt e2 2 : BitVec 8), (byteAt e2 3 : BitVec 8),
                (byteAt e2 4 : BitVec 8), (byteAt e2 5 : BitVec 8),
                (byteAt e2 6 : BitVec 8), (byteAt e2 7 : BitVec 8)]
      = PC + BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) := by
  -- Extract AUIPC mode witnesses + apply transpile_PC_for_AUIPC.
  have h_mode := h_circuit.2
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
  have h_pc_bridge : (m.pc r_main).val = PC.toNat :=
    transpile_PC_for_AUIPC m r_main PC h_ext h_op
  -- Apply S3's lo/hi BitVec bridges (AUIPC variants).
  set offset_bv : BitVec 64 := BitVec.signExtend 64 (imm ++ (0 : BitVec 12)) with h_offset_def
  have h_lo_val : (memory_entry_lo e2).val = (PC + offset_bv).toNat % 4294967296 :=
    auipc_store_value_lo_bv m r_main next_pc PC offset_bv e2
      h_circuit h_lane_lo h_pc_bridge h_offset_bridge h_no_wrap h_lo_bound
  have h_hi_val : (memory_entry_hi e2).val = (PC + offset_bv).toNat / 4294967296 :=
    auipc_store_value_hi_bv m r_main next_pc PC offset_bv e2
      h_circuit h_lane_hi h_pc_offset_lt_2_32
  -- Bridge to byte-sum form via the helpers.
  have h_lo_bytes :
      (byteAt e2 0).val + (byteAt e2 1).val * 256
        + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (PC + offset_bv).toNat % 4294967296 :=
    lo_bytes_from_fgl_eq e2 (memory_entry_lo e2) (PC + offset_bv).toNat
      rfl h_lo_val
  have h_hi_bound : (PC + offset_bv).toNat / 4294967296 < 4294967296 :=
    Nat.div_lt_of_lt_mul (by have := (PC + offset_bv).isLt; norm_num at this ⊢; omega)
  have h_hi_bytes :
      (byteAt e2 4).val + (byteAt e2 5).val * 256
        + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (PC + offset_bv).toNat / 4294967296 :=
    hi_bytes_from_fgl_eq e2 (memory_entry_hi e2) (PC + offset_bv).toNat
      rfl h_hi_val h_hi_bound
  -- Assemble byte_sum = (PC + offset_bv).toNat.
  have h_byte_sum := byte_sum_from_lo_hi e2 (PC + offset_bv) h_lo_bytes h_hi_bytes
  -- Close via BitVec.eq_of_toNat_eq + u64_toBV_of_bytes_toNat.
  apply BitVec.eq_of_toNat_eq
  rw [ZiskFv.PackedBitVec.u64_toBV_of_bytes_toNat
        (byteAt e2 0) (byteAt e2 1) (byteAt e2 2) (byteAt e2 3)
        (byteAt e2 4) (byteAt e2 5) (byteAt e2 6) (byteAt e2 7)
      h0 h1 h2 h3 h4 h5 h6 h7]
  rw [h_byte_sum]

end ZiskFv.EquivCore.WriteValueProofs.JumpUType
