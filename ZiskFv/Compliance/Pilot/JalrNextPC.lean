import ZiskFv.Compliance.Pilot.SubNextPC
import ZiskFv.EquivCore.And

/-!
# Pilot next-PC discharge for JALR (#100): the masked AND jump target

JALR's set-PC handshake (`main.pil:159`, `if set_pc = 1, jump to c[0] + jmp_offset1`)
commits `next_pc = c_0 + jmp_offset1` — using only the **lo lane** `c[0]` of the
final external `OP_AND` row.  The architectural target is
`0xFF…FE &&& (rs1_val + signExtend 64 imm)`.

ZisK lowers JALR two ways (`riscv2zisk_context.rs::jalr`):

* **aligned** (`imm % 4 == 0`): one `OP_AND` row, `b = rs1`, `jmp_offset1 = imm`;
  the target is `(mask &&& rs1) + imm`, which equals `mask &&& (rs1 + imm)` because
  `imm` is even (the bit-0 commutation `masked_add_offset_even` below);
* **unaligned**: an earlier `OP_ADD` row computes `rs1 + imm`, fed to the final
  `OP_AND` row through `lastc`, with `jmp_offset1 = 0`; the target is
  `mask &&& (rs1 + imm)` directly.

Both fit the single shape `target = mask &&& (operand + offset_bv)` with
`operand := binaryRowB64 row` (the `OP_AND` `b` operand) and
`offset_bv := the BitVec of jmp_offset1`:
* aligned: `operand = rs1`, `offset_bv = signExtend imm` (even);
* unaligned: `operand = rs1 + signExtend imm`, `offset_bv = 0`.

**Scope (`c_1 = 0`).**  The handshake drops the AND result's hi lane `c[1]`.
The emulator (`emu.rs:1446`) sets `pc = (c as i64 + jmp_offset1)` from the *full*
64-bit `c`, while the circuit uses only `c[0]`; the two agree exactly when the
AND result's hi lane is zero (`c_1 = 0`), i.e. the jump stays inside ZisK's
32-bit PC space without 64-bit wraparound.  This is the JALR analogue of the
32-bit PC-trajectory scope JAL/AUIPC already carry (`h_pc_offset_lt_2_32`); it is
a same-world circuit pin on the committed `c_1` column, NOT a cross-world promise.
Note it is genuinely stronger than `target < 2^32` in the aligned case: a base
`rs1` near `2^64` can wrap to a small target while `mask &&& rs1` keeps its hi
lane, so `c_1 = 0` (equivalently `rs1 < 2^32`) is the load-bearing hypothesis.
-/

namespace ZiskFv.Compliance.Pilot

open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open Interaction
open ZiskFv.Trusted

/-- **JALR lo-lane AND value (`c_1 = 0`).**  On the final `OP_AND` row, with the
    Binary-SM byte witnesses (`h_matches`), the Main/Binary `c`-lane match
    (`h_match_clo`/`h_match_chi`), and the operand bridges
    `a = mask` / `b = operand`, the committed lo lane satisfies
    `(c_0).val = (mask &&& operand).toNat`, provided the AND result's hi lane is
    zero (`h_c1_zero`).  The hi-lane scope is what lets the single 32-bit `c[0]`
    column carry the full masked value.

    The c-byte ranges `hc0..hc7` are circuit facts derived by the caller from the
    Binary SM's `range_conditions` (part of `StaticBinaryTableWfFacts`). -/
theorem jalr_c0_val_eq_masked_operand
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (c0 c1 : FGL) (operand : BitVec 64)
    (h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        row ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_match_clo :
      c0 = row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
            + row.cBytes.free_in_c_2 * 65536 + row.cBytes.free_in_c_3 * 16777216)
    (h_match_chi :
      c1 = row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
            + row.cBytes.free_in_c_6 * 65536 + row.cBytes.free_in_c_7 * 16777216)
    (h_a_mask : ZiskFv.EquivCore.Add.binaryRowA64 row = 0xFFFFFFFFFFFFFFFE#64)
    (h_b_operand : ZiskFv.EquivCore.Add.binaryRowB64 row = operand)
    (hc0 : row.cBytes.free_in_c_0.val < 256) (hc1 : row.cBytes.free_in_c_1.val < 256)
    (hc2 : row.cBytes.free_in_c_2.val < 256) (hc3 : row.cBytes.free_in_c_3.val < 256)
    (hc4 : row.cBytes.free_in_c_4.val < 256) (hc5 : row.cBytes.free_in_c_5.val < 256)
    (hc6 : row.cBytes.free_in_c_6.val < 256) (hc7 : row.cBytes.free_in_c_7.val < 256)
    (h_c1_zero : c1 = 0) :
    c0.val = (0xFFFFFFFFFFFFFFFE#64 &&& operand).toNat := by
  -- (1) The 64-bit packed AND identity: mask &&& operand = ofNat (Σ all c-bytes).
  have h_chunks :=
    ZiskFv.EquivCore.Bridge.Binary.binary_row_and_chunks_eq_bv_and_of_wf row h_matches
  simp only [ZiskFv.EquivCore.Add.binaryRowA64] at h_a_mask
  simp only [ZiskFv.EquivCore.Add.binaryRowB64] at h_b_operand
  rw [h_a_mask, h_b_operand] at h_chunks
  -- `h_chunks : mask &&& operand = BitVec.ofNat 64 (Σ all 8 c-bytes)`
  -- (2) lo-lane value (no field wrap): (c0).val = Σ lo 4 c-bytes (nat).
  have h_lo_nat :
      c0.val = row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536 + row.cBytes.free_in_c_3.val * 16777216 := by
    rw [h_match_clo]
    have h_cast :
        row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
          + row.cBytes.free_in_c_2 * 65536 + row.cBytes.free_in_c_3 * 16777216
        = (((row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
              + row.cBytes.free_in_c_2.val * 65536
              + row.cBytes.free_in_c_3.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast]; apply Nat.mod_eq_of_lt; omega
  -- (3) hi lane is zero at the nat level, from c1 = 0 + ranges.
  have h_hi_nat :
      row.cBytes.free_in_c_4.val + row.cBytes.free_in_c_5.val * 256
        + row.cBytes.free_in_c_6.val * 65536 + row.cBytes.free_in_c_7.val * 16777216 = 0 := by
    have h0 : c1.val = 0 := by rw [h_c1_zero]; rfl
    rw [h_match_chi] at h0
    have h_cast :
        row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
          + row.cBytes.free_in_c_6 * 65536 + row.cBytes.free_in_c_7 * 16777216
        = (((row.cBytes.free_in_c_4.val + row.cBytes.free_in_c_5.val * 256
              + row.cBytes.free_in_c_6.val * 65536
              + row.cBytes.free_in_c_7.val * 16777216 : ℕ) : FGL)) := by push_cast; ring
    rw [h_cast, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)] at h0
    omega
  -- (4) toNat of the packed AND equals the full 8-byte sum (< 2^64, no wrap).
  have h_toNat : (0xFFFFFFFFFFFFFFFE#64 &&& operand).toNat
      = row.cBytes.free_in_c_0.val + row.cBytes.free_in_c_1.val * 256
        + row.cBytes.free_in_c_2.val * 65536 + row.cBytes.free_in_c_3.val * 16777216
        + row.cBytes.free_in_c_4.val * 4294967296 + row.cBytes.free_in_c_5.val * 1099511627776
        + row.cBytes.free_in_c_6.val * 281474976710656
        + row.cBytes.free_in_c_7.val * 72057594037927936 := by
    rw [show (0xFFFFFFFFFFFFFFFE#64 &&& operand)
          = BitVec.and 0xFFFFFFFFFFFFFFFE#64 operand from rfl,
        h_chunks, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [h_lo_nat, h_toNat]; omega

/-- **JALR set-PC next-PC discharge (#100), unified over both lowerings.**
    Composes the set-PC handshake mechanism (`setpc_path_nextPC_discharged`,
    `next_pc = c_0 + jmp_offset1`) with the lo-lane AND value
    (`jalr_c0_val_eq_masked_operand`) and the wide-PC offset cast
    (`ofNat_fgl_pc_plus_offset_eq`) to derive the committed next-row PC's BitVec
    image as `(mask &&& operand) + offset_bv` — the set-PC handshake's
    `c_0 + jmp_offset1` in BitVec form.

    Both ZisK JALR lowerings instantiate this with `operand := binaryRowB64 row`
    (the final `OP_AND` `b` operand) and `offset_bv := jmp_offset1`'s BitVec:
    aligned `(operand = rs1, offset_bv = signExtend imm)` and unaligned
    `(operand = rs1 + signExtend imm, offset_bv = 0)`.  The caller closes the
    discharge by identifying `(mask &&& operand) + offset_bv` with Sail's
    `nextPC = mask &&& (rs1_val + signExtend 64 imm)`:
    * unaligned (`offset_bv = 0`): `(mask &&& operand) + 0 = mask &&& operand` with
      `operand = rs1 + signExtend imm` — definitional;
    * aligned (`operand = rs1`, `offset_bv = signExtend imm`, `imm % 4 = 0` so
      `offset_bv` even): the bit-0 commutation
      `(mask &&& rs1) + off = mask &&& (rs1 + off)` for even `off`.

    No cross-world next-PC promise; every input is a same-world circuit witness,
    scope pin (`h_c1_zero`, `h_no_fgl_wrap`), or decode/ROM pin. -/
theorem jalr_setpc_nextPC_discharged
    (trace : AcceptedZiskTrace numInstructions)
    (i : Fin trace.numInstructions)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (operand offset_bv : BitVec 64)
    (h_idx : i.val + 1 < trace.mainTable.table.length)
    (h_set_pc : (mainOfTable trace.program trace.mainTable).set_pc i.val = 1)
    (h_flag : (mainOfTable trace.program trace.mainTable).flag i.val = 0)
    (h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        row ZiskFv.Airs.Tables.BinaryTable.OP_AND)
    (h_match_clo :
      (mainOfTable trace.program trace.mainTable).c_0 i.val
        = row.cBytes.free_in_c_0 + row.cBytes.free_in_c_1 * 256
            + row.cBytes.free_in_c_2 * 65536 + row.cBytes.free_in_c_3 * 16777216)
    (h_match_chi :
      (mainOfTable trace.program trace.mainTable).c_1 i.val
        = row.cBytes.free_in_c_4 + row.cBytes.free_in_c_5 * 256
            + row.cBytes.free_in_c_6 * 65536 + row.cBytes.free_in_c_7 * 16777216)
    (h_a_mask : ZiskFv.EquivCore.Add.binaryRowA64 row = 0xFFFFFFFFFFFFFFFE#64)
    (h_b_operand : ZiskFv.EquivCore.Add.binaryRowB64 row = operand)
    (hc0 : row.cBytes.free_in_c_0.val < 256) (hc1 : row.cBytes.free_in_c_1.val < 256)
    (hc2 : row.cBytes.free_in_c_2.val < 256) (hc3 : row.cBytes.free_in_c_3.val < 256)
    (hc4 : row.cBytes.free_in_c_4.val < 256) (hc5 : row.cBytes.free_in_c_5.val < 256)
    (hc6 : row.cBytes.free_in_c_6.val < 256) (hc7 : row.cBytes.free_in_c_7.val < 256)
    (h_c1_zero : (mainOfTable trace.program trace.mainTable).c_1 i.val = 0)
    (h_offset_bridge :
      ((mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val
        = offset_bv.toNat)
    (h_no_fgl_wrap :
      ((mainOfTable trace.program trace.mainTable).c_0 i.val).val
        + ((mainOfTable trace.program trace.mainTable).jmp_offset1 i.val).val < GL_prime) :
    (register_type_pc_equiv ▸
        (BitVec.ofNat 64 ((execRowOf trace i)[1]!.pc).val))
      = (0xFFFFFFFFFFFFFFFE#64 &&& operand) + offset_bv := by
  have h_c0 :
      ((mainOfTable trace.program trace.mainTable).c_0 i.val).val
        = (0xFFFFFFFFFFFFFFFE#64 &&& operand).toNat :=
    jalr_c0_val_eq_masked_operand row _ _ operand h_matches h_match_clo h_match_chi
      h_a_mask h_b_operand hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 h_c1_zero
  rw [setpc_path_nextPC_discharged trace i h_idx h_set_pc h_flag,
      ofNat_fgl_pc_plus_offset_eq _ _ (0xFFFFFFFFFFFFFFFE#64 &&& operand) offset_bv
        h_c0 h_offset_bridge h_no_fgl_wrap]

end ZiskFv.Compliance.Pilot
