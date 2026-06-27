import ZiskFv.EquivCore.Bridge.Binary
import ZiskFv.EquivCore.Add

/-!
# Branch FLAG = comparison (#100 / #101)

The branch-flag derivation lemmas: for a Main row whose operation-bus
request is provided by a static-table Binary comparison row, the Main
`flag` column equals the comparison result of the two 64-bit operands.

This is the BRANCH analogue of how SLT/SLTU derive their rd value
(`EquivCore/Sltu.lean::equiv_SLTU_of_static_row`): the SAME comparison
cout produced by the Binary SM, read off the operation-bus `flag` lane
(`compare_flag_lane_of_match`: `m.flag = carry_7`) instead of the `c`
lane. The cout-vs-comparison content is the verified static byte chain
(`static_ltu_chain_flags7_iff_lt` etc.) — so the branch flag inherits
SLT/SLTU's already-verified comparison soundness with no new trust.

Lives downstream of `Bridge/Binary` because it references
`EquivCore.Add.binaryRowA64`/`binaryRowB64` (the packed-operand defs).
Consumed by the BLTU/BGEU next-PC discharge, where the derived flag
drives the branch mux `pc + jmp_offset2 + flag*(jmp_offset1 -
jmp_offset2)` (`Pilot.branch_path_nextPC_field`).
-/

namespace ZiskFv.EquivCore.Bridge.Binary

open ZiskFv.Airs.OperationBus
open ZiskFv.Airs.Main (Valid_Main)
open ZiskFv.Airs.Binary (Valid_Binary)

/-- **BLTU/BGEU branch FLAG = unsigned-comparison.** For a Main row whose
    operation-bus request is provided by a static-table LTU Binary row,
    the Main `flag` column equals the unsigned-LT result of the two
    64-bit operands `r1_val`/`r2_val` (packed from the Binary row's
    `a`/`b` byte columns via `binaryRowA64`/`binaryRowB64`). Combines the
    flag-lane projection (`compare_flag_lane_of_match`: `m.flag =
    carry_7`) with the static LTU chain comparison
    (`static_ltu_chain_flags7_iff_lt` + `lookup_flags7_mod_two_eq_carry`
    + `carry_7_val_lt_2_of_row_core`). The SAME comparison cout SLTU's rd
    value uses, surfaced on the `flag` lane. -/
lemma branch_flag_ltu_of_static_row
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (row : ZiskFv.AirsClean.Binary.BinaryRow FGL)
    (r1_val r2_val : BitVec 64)
    (h_match : matches_entry (opBus_row_Main m r_main)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage row) 1))
    (h_core : ZiskFv.Airs.Binary.core_every_row
      (ZiskFv.AirsClean.Binary.validOfRow row) 0)
    (h_facts : ZiskFv.AirsClean.Binary.StaticBinaryTableWfFacts row)
    (h_mode32_zero : row.mode.mode32 = 0)
    (h_b_op : row.chain.b_op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LTU)
    (h_input_r1_row : r1_val = ZiskFv.EquivCore.Add.binaryRowA64 row)
    (h_input_r2_row : r2_val = ZiskFv.EquivCore.Add.binaryRowB64 row) :
    m.flag r_main = (if BitVec.ult r1_val r2_val then 1 else 0) := by
  set v := ZiskFv.AirsClean.Binary.validOfRow row with hv
  -- (1) Op-bus match in the `opBus_row_Binary` representation.
  have h_match_v : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v 0) := by
    simpa [hv, ZiskFv.AirsClean.Binary.validOfRow,
      ZiskFv.AirsClean.Binary.opBusMessage,
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
      opBus_row_Binary] using h_match
  -- (2) Flag-lane projection: `m.flag = carry_7`.
  have h_flag_eq : m.flag r_main = v.carry_7 0 := compare_flag_lane_of_match h_match_v
  -- (3) Static LTU byte-chain output for this provider row.
  have out := byte_chain_discharge_64_of_static_row row h_facts
    ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_mode32_zero h_b_op
  -- (4) `carry_7 ∈ {0,1}` (so `carry_7.val % 2 = carry_7.val`).
  have h_c7_lt2 : (v.carry_7 0).val < 2 := carry_7_val_lt_2_of_row_core row h_core
  -- Per-byte ranges from the static chain witnesses.
  have ha0 : (v.free_in_a_0 0).val < 256 := chain_a_byte_lt_256 out.chain_0
  have ha1 : (v.free_in_a_1 0).val < 256 := chain_a_byte_lt_256 out.chain_1
  have ha2 : (v.free_in_a_2 0).val < 256 := chain_a_byte_lt_256 out.chain_2
  have ha3 : (v.free_in_a_3 0).val < 256 := chain_a_byte_lt_256 out.chain_3
  have ha4 : (v.free_in_a_4 0).val < 256 := chain_a_byte_lt_256 out.chain_4
  have ha5 : (v.free_in_a_5 0).val < 256 := chain_a_byte_lt_256 out.chain_5
  have ha6 : (v.free_in_a_6 0).val < 256 := chain_a_byte_lt_256 out.chain_6
  have ha7 : (v.free_in_a_7 0).val < 256 := chain_a_byte_lt_256 out.chain_7
  have hb0 : (v.free_in_b_0 0).val < 256 := chain_b_byte_lt_256 out.chain_0
  have hb1 : (v.free_in_b_1 0).val < 256 := chain_b_byte_lt_256 out.chain_1
  have hb2 : (v.free_in_b_2 0).val < 256 := chain_b_byte_lt_256 out.chain_2
  have hb3 : (v.free_in_b_3 0).val < 256 := chain_b_byte_lt_256 out.chain_3
  have hb4 : (v.free_in_b_4 0).val < 256 := chain_b_byte_lt_256 out.chain_4
  have hb5 : (v.free_in_b_5 0).val < 256 := chain_b_byte_lt_256 out.chain_5
  have hb6 : (v.free_in_b_6 0).val < 256 := chain_b_byte_lt_256 out.chain_6
  have hb7 : (v.free_in_b_7 0).val < 256 := chain_b_byte_lt_256 out.chain_7
  -- (5) Static chain comparison: `flags_7 % 2 = 1 ↔ aSum < bSum`, with
  --     `flags_7 % 2` rewritten to `carry_7 % 2`.
  have h_iff := static_ltu_chain_flags7_iff_lt v 0 out
  rw [lookup_flags7_mod_two_eq_carry (ZiskFv.AirsClean.Binary.rowAt v 0) h_core] at h_iff
  have h_c7_rowAt : (ZiskFv.AirsClean.Binary.rowAt v 0).chain.carry_7 = v.carry_7 0 := rfl
  rw [h_c7_rowAt] at h_iff
  -- (6) Bridge `BitVec.ult` to the Nat-sum comparison via the input bridges.
  have h_r1_eq : r1_val = ZiskFv.EquivCore.Add.binaryValidA64 v 0 := by
    rw [h_input_r1_row]
    simp only [hv, ZiskFv.EquivCore.Add.binaryRowA64,
      ZiskFv.EquivCore.Add.binaryValidA64, ZiskFv.AirsClean.Binary.validOfRow]
  have h_r2_eq : r2_val = ZiskFv.EquivCore.Add.binaryValidB64 v 0 := by
    rw [h_input_r2_row]
    simp only [hv, ZiskFv.EquivCore.Add.binaryRowB64,
      ZiskFv.EquivCore.Add.binaryValidB64, ZiskFv.AirsClean.Binary.validOfRow]
  have hA_lt :
      (v.free_in_a_0 0).val + (v.free_in_a_1 0).val * 256
        + (v.free_in_a_2 0).val * 65536 + (v.free_in_a_3 0).val * 16777216
        + (v.free_in_a_4 0).val * 4294967296 + (v.free_in_a_5 0).val * 1099511627776
        + (v.free_in_a_6 0).val * 281474976710656 + (v.free_in_a_7 0).val * 72057594037927936
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
  have hB_lt :
      (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
        + (v.free_in_b_2 0).val * 65536 + (v.free_in_b_3 0).val * 16777216
        + (v.free_in_b_4 0).val * 4294967296 + (v.free_in_b_5 0).val * 1099511627776
        + (v.free_in_b_6 0).val * 281474976710656 + (v.free_in_b_7 0).val * 72057594037927936
        < 2 ^ 64 := by show _ < 18446744073709551616; omega
  have h_r1_toNat :
      r1_val.toNat =
        (v.free_in_a_0 0).val + (v.free_in_a_1 0).val * 256
          + (v.free_in_a_2 0).val * 65536 + (v.free_in_a_3 0).val * 16777216
          + (v.free_in_a_4 0).val * 4294967296 + (v.free_in_a_5 0).val * 1099511627776
          + (v.free_in_a_6 0).val * 281474976710656 + (v.free_in_a_7 0).val * 72057594037927936 := by
    rw [h_r1_eq, ZiskFv.EquivCore.Add.binaryValidA64, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hA_lt
  have h_r2_toNat :
      r2_val.toNat =
        (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
          + (v.free_in_b_2 0).val * 65536 + (v.free_in_b_3 0).val * 16777216
          + (v.free_in_b_4 0).val * 4294967296 + (v.free_in_b_5 0).val * 1099511627776
          + (v.free_in_b_6 0).val * 281474976710656 + (v.free_in_b_7 0).val * 72057594037927936 := by
    rw [h_r2_eq, ZiskFv.EquivCore.Add.binaryValidB64, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hB_lt
  -- (7) Conclude: `m.flag = carry_7 = (if aSum < bSum then 1 else 0)`.
  have h_c7_mod : (v.carry_7 0).val % 2 = (v.carry_7 0).val := Nat.mod_eq_of_lt (by omega)
  rw [h_flag_eq, BitVec.ult_eq_decide, h_r1_toNat, h_r2_toNat]
  by_cases h_lt :
      (v.free_in_a_0 0).val + (v.free_in_a_1 0).val * 256
        + (v.free_in_a_2 0).val * 65536 + (v.free_in_a_3 0).val * 16777216
        + (v.free_in_a_4 0).val * 4294967296 + (v.free_in_a_5 0).val * 1099511627776
        + (v.free_in_a_6 0).val * 281474976710656 + (v.free_in_a_7 0).val * 72057594037927936
      <
      (v.free_in_b_0 0).val + (v.free_in_b_1 0).val * 256
        + (v.free_in_b_2 0).val * 65536 + (v.free_in_b_3 0).val * 16777216
        + (v.free_in_b_4 0).val * 4294967296 + (v.free_in_b_5 0).val * 1099511627776
        + (v.free_in_b_6 0).val * 281474976710656 + (v.free_in_b_7 0).val * 72057594037927936
  · have h1 : (v.carry_7 0).val = 1 := by rw [← h_c7_mod]; exact h_iff.mpr h_lt
    rw [if_pos (decide_eq_true h_lt)]
    exact Fin.ext (by rw [h1]; rfl)
  · have h0 : (v.carry_7 0).val = 0 := by
      rw [← h_c7_mod]
      by_contra hne
      exact h_lt (h_iff.mp (by omega))
    rw [if_neg (by simp [h_lt])]
    exact Fin.ext (by rw [h0]; rfl)

end ZiskFv.EquivCore.Bridge.Binary
