import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.ConstructionAnd
import ZiskFv.Compliance.ConstructionLogic
import ZiskFv.Compliance.ConstructionCompare
import ZiskFv.Compliance.ConstructionIType
import ZiskFv.Compliance.ConstructionShift
import ZiskFv.Compliance.ConstructionAdd
import ZiskFv.Compliance.ConstructionWAlu
import ZiskFv.Compliance.ConstructionLui
import ZiskFv.Compliance.ConstructionAuipc
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionDivuw
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.Compliance.ConstructionRemuw
import ZiskFv.Compliance.ConstructionStore
import ZiskFv.Compliance.ConstructionLoad
import ZiskFv.Compliance.ConstructionBranch
import ZiskFv.Compliance.ConstructionJump
import ZiskFv.Compliance
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.TraceLevelExport.Base
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl
import ZiskFv.Compliance.TraceLevelExport.EnvOf
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.Pilot.JalrNextPC
import ZiskFv.Compliance.Pilot.BranchNextPC
import ZiskFv.EquivCore.Bridge.BranchFlag

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Mem (Valid_Mem)
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open ZiskFv.Tactics.ALUITypeArchetype (itype_imm_subset_holds_main)
open Interaction

-- The M-extension row-computing defs are reducible/semireducible; structure-field
-- elaboration would otherwise whnf-reduce the full per-row ArithMul/ArithDiv
-- computation (a runaway). `seal` blocks that locally without touching the
-- committed construction proofs (which keep the defs as-is in their oleans).
seal mulwArow mulhuArow divuArow divuwArow remuArow remuwArow

set_option maxHeartbeats 8000000

/-- `eRdLui` destination register index derived from `AddressSpec` and decode. -/
theorem eRdLui_rd_idx_of_decode
    {numInstructions : Nat}
    {trace : AcceptedZiskTrace numInstructions}
    {i : Fin trace.numInstructions}
    {rd : regidx}
    (h_store_ind : (mainRowWithRomLui trace i).rom.store_ind = 0)
    (h_store_offset :
      (mainRowWithRomLui trace i).rom.store_offset =
        Transpiler.ind (regidx_to_fin rd)) :
    regidx_to_fin rd =
      Transpiler.wrap_to_regidx (eRdLui trace i).ptr := by
  have h_spec := RomDecodeBinding.mainAddressSpec_at trace ⟨i.val, trace.mainTable_index i⟩
  have h_addr2 := h_spec.2.2.1
  rw [eRdLui, ZiskFv.AirsClean.Main.cMemMessage,
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
  rw [h_addr2, h_store_offset, h_store_ind]
  simp [Transpiler.wrap_to_regidx_ind]

/-- The store address arithmetic bridge reconstructed from decoded ROM offset,
    the source-lane value, and an explicit natural effective-address bound. -/
theorem store_addr_arith_of_decode
    {numInstructions : Nat}
    {trace : AcceptedZiskTrace numInstructions}
    {i : Fin trace.numInstructions}
    {imm : BitVec 12}
    {r1_val : BitVec 64}
    (h_store_offset_imm :
      (mainRowWithRomSt trace i).rom.store_offset =
        ((BitVec.signExtend 64 imm).toNat : FGL))
    (h_a0_value : (mainRowWithRomSt trace i).core.a_0 = lane_lo r1_val)
    (h_addr_bound :
      r1_val.toNat + (BitVec.signExtend 64 imm).toNat < ZiskPhysicalAddressSpaceSize) :
    ((mainRowWithRomSt trace i).rom.store_offset
        + (mainRowWithRomSt trace i).core.a_0).toNat =
      (r1_val + BitVec.signExtend 64 imm).toNat := by
  have h_bound32 : r1_val.toNat + (BitVec.signExtend 64 imm).toNat < 4294967296 := by
    simpa using h_addr_bound
  have h_r1_lt32 : r1_val.toNat < 4294967296 := by omega
  have h_imm_lt32 : (BitVec.signExtend 64 imm).toNat < 4294967296 := by omega
  have h_r1_lt_gl : r1_val.toNat < GL_prime := by omega
  have h_imm_lt_gl : (BitVec.signExtend 64 imm).toNat < GL_prime := by omega
  have h_sum_lt_gl : r1_val.toNat + (BitVec.signExtend 64 imm).toNat < GL_prime := by omega
  have h_sum_lt64 : r1_val.toNat + (BitVec.signExtend 64 imm).toNat < 2 ^ 64 := by omega
  have h_bv_sum :
      (r1_val + BitVec.signExtend 64 imm).toNat =
        r1_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt h_sum_lt64
  rw [h_store_offset_imm, h_a0_value]
  change ((((BitVec.signExtend 64 imm).toNat : FGL) + lane_lo r1_val : FGL).val) =
    (r1_val + BitVec.signExtend 64 imm).toNat
  rw [h_bv_sum]
  rw [Fin.val_add, Fin.val_natCast]
  unfold lane_lo
  rw [Fin.val_mk]
  rw [Nat.mod_eq_of_lt h_imm_lt_gl]
  rw [Nat.mod_eq_of_lt h_r1_lt32]
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

/-- Store `addr2` placement derived from `AddressSpec` and the decoded store selector.

The arithmetic equality is reconstructed locally from decode, source-lane
agreement, and the explicit natural effective-address bound. -/
theorem store_addr2_of_decode
    {numInstructions : Nat}
    {trace : AcceptedZiskTrace numInstructions}
    {i : Fin trace.numInstructions}
    {imm : BitVec 12}
    {r1_val : BitVec 64}
    (h_store_ind : (mainRowWithRomSt trace i).rom.store_ind = 1)
    (h_store_offset_imm :
      (mainRowWithRomSt trace i).rom.store_offset =
        ((BitVec.signExtend 64 imm).toNat : FGL))
    (h_a0_value : (mainRowWithRomSt trace i).core.a_0 = lane_lo r1_val)
    (h_addr_bound :
      r1_val.toNat + (BitVec.signExtend 64 imm).toNat < ZiskPhysicalAddressSpaceSize) :
    (mainRowWithRomSt trace i).rom.addr2.toNat =
      (r1_val + BitVec.signExtend 64 imm).toNat := by
  have h_store_addr_arith :=
    store_addr_arith_of_decode h_store_offset_imm h_a0_value h_addr_bound
  have h_addr2 := (RomDecodeBinding.mainRowWithRomSt_addressSpec trace i).2.2.1
  rw [h_addr2, h_store_ind]
  simpa using h_store_addr_arith

/-- JALR link-value bridge reconstructed from the PC bridge and decoded fallthrough offset. -/
theorem jalr_link_bridge_of_decode
    {numInstructions : Nat}
    {trace : AcceptedZiskTrace numInstructions}
    {i : Fin trace.numInstructions}
    {pc : BitVec 64}
    (h_pc_bridge :
      ((mainOfTable trace.program trace.mainTable).pc i.val).val = pc.toNat)
    (h_jmp2 : (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val = 4)
    (h_pc_bound : pc.toNat < GL_prime - 4) :
    ((mainOfTable trace.program trace.mainTable).pc i.val
        + (mainOfTable trace.program trace.mainTable).jmp_offset2 i.val).val
      = (pc + 4#64).toNat := by
  rw [h_jmp2]
  have h_bv_eq :=
    Pilot.ofNat_fgl_pc_plus_4_eq
      ((mainOfTable trace.program trace.mainTable).pc i.val) pc h_pc_bridge h_pc_bound
  have h_toNat := congrArg BitVec.toNat h_bv_eq
  have h_gl_lt64 : GL_prime < 2 ^ 64 := by
    have h_lit := ZiskFv.PackedBitVec.WidePCNoWrap.GL_prime_lt_pow_64
    have h_two64 : 2 ^ 64 = 18446744073709551616 := by norm_num
    omega
  have h_val_lt64 : (((mainOfTable trace.program trace.mainTable).pc i.val + 4 : FGL).val)
      < 2 ^ 64 :=
    Nat.lt_trans (Fin.isLt _) h_gl_lt64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_val_lt64] at h_toNat
  exact h_toNat

/-! ## Strengthened control-flow + U-type arms (branches, JAL/JALR, LUI/AUIPC)

These arms reach the same channel-balance conclusion as the 22 above, but via a
DIRECT lift rather than an explicit `OpEnvelope`/global-theorem invocation: the
matching `construction_<op>_sound` already proves the `bus_effect`-form per-step
conclusion over the real trace row, and `state_effect_via_channels` is `@[reducible]`-
defeq to `bus_effect.2`.  Hence `rw [state_effect_via_channels_eq_bus_effect_2]`
followed by the construction theorem yields the EXACT channel-balance proposition
the OLD global theorem produces for these arms (for branches this IS the
`Equivalence.<B>.equiv_<B>` the global dispatcher `zisk_riscv_compliant_program_bus_branch`
itself dispatches to; for LUI/AUIPC/JAL/JALR it is the channel-balance lift of the
same concrete `eRdLui` rd-write entry the `bus_effect`-form arm uses).

Non-vacuity: `execRow` (and `exec_row` for branches) remains a genuine ∀-binder
inside each `RowData_<op>`; no `False.elim`, no contradictory binder; the
conclusion is over the real `mainOfTable` row.  These are strictly stronger than
the corresponding `bus_effect`-form arms (channel-balance form, same data). -/

/-- **BLTU/BGEU branch FLAG provided.** Trace-level wrapper of
    `branch_flag_ltu_of_static_row`: sources the static-table LTU Binary
    provider row backing the Main op-bus request (via
    `main_request_compare_provided`, the SAME provider `stepStrong_sltu` uses),
    unpacks its core/wf/spec facts and the operand packings (the
    `stepStrong_sltu` provider block), and concludes the Main `flag` column
    equals the unsigned-LT comparison of the two register operands. The flag is
    the SAME comparison cout SLTU's rd value uses, surfaced on the `flag` lane —
    no new trust over the SLTU route. -/
theorem branch_flag_ltu_provided
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (r1 r2 : regidx) (r1_val r2_val : BitVec 64)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = OP_LTU)
    (h_m32 :
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0)
    (h_a_lo_t :
      (mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok r2_val (binding i)) :
    (mainOfTable trace.program trace.mainTable).flag i.val
      = if BitVec.ult r1_val r2_val then 1 else 0 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_compare_provided trace i h_main_active (Or.inr h_main_op)
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LTU : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LTU, ZiskFv.Trusted.OP_LTU] using h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LTU (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LTU])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LTU h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LTU :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.EquivCore.Bridge.Binary.branch_flag_ltu_of_static_row
    m i.val providerInput r1_val r2_val h_match h_core h_facts h_row_m32 h_bop
    h_input_r1_row h_input_r2_row

/-- **BLT/BGE branch FLAG provided.** Signed sibling of `branch_flag_ltu_provided`:
    sources the static-table OP_LT Binary provider row (via
    `main_request_compare_provided`, the SAME provider SLT uses), unpacks its
    facts and operand packings, and concludes the Main `flag` column equals the
    signed-LT comparison of the two register operands. No new trust over SLT. -/
theorem branch_flag_lt_provided
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (r1 r2 : regidx) (r1_val r2_val : BitVec 64)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = OP_LT)
    (h_m32 :
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0)
    (h_a_lo_t :
      (mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok r2_val (binding i)) :
    (mainOfTable trace.program trace.mainTable).flag i.val
      = if BitVec.slt r1_val r2_val then 1 else 0 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_compare_provided trace i h_main_active (Or.inl h_main_op)
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_LT : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_LT, ZiskFv.Trusted.OP_LT] using h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_LT (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_LT])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_LT h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_LT :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.EquivCore.Bridge.Binary.branch_flag_lt_of_static_row
    m i.val providerInput r1_val r2_val h_match h_core h_facts h_row_m32 h_bop
    h_input_r1_row h_input_r2_row

/-- **BEQ/BNE branch FLAG provided.** Equality sibling of `branch_flag_ltu_provided`:
    sources the static-table OP_EQ Binary provider row (via
    `main_request_compare_provided`, the SAME provider BEQ/BNE use), unpacks its
    facts and operand packings, and concludes the Main `flag` column equals the
    signed-LT comparison of the two register operands. No new trust over SLT. -/
theorem branch_flag_eq_provided
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (r1 r2 : regidx) (r1_val r2_val : BitVec 64)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = OP_EQ)
    (h_m32 :
      (mainOfTable trace.program trace.mainTable).m32 i.val = 0)
    (h_a_lo_t :
      (mainOfTable trace.program trace.mainTable).a_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_a_hi_t :
      (mainOfTable trace.program trace.mainTable).a_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r1)))
    (h_b_lo_t :
      (mainOfTable trace.program trace.mainTable).b_0 i.val =
        ZiskFv.Trusted.lane_lo
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_b_hi_t :
      (mainOfTable trace.program trace.mainTable).b_1 i.val =
        ZiskFv.Trusted.lane_hi
          ((ZiskFv.EquivCore.Bridge.SailStateBridge.sail_to_rv64 (binding i)).xreg
            (regidx_to_fin r2)))
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok r2_val (binding i)) :
    (mainOfTable trace.program trace.mainTable).flag i.val
      = if r1_val == r2_val then 1 else 0 := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_eq_provided trace i h_main_active h_main_op
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_EQ : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_EQ, ZiskFv.Trusted.OP_EQ] using h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_EQ (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_EQ])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_EQ h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_EQ :=
    allByteMatchesOfStaticOut64_local h_out
  have h_input_r1_row :
      r1_val = ZiskFv.EquivCore.Add.binaryRowA64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r1_packed_a_row
        m providerInput i.val (regidx_to_fin r1) r1_val
        h_matches h_m32_zero h_a_lo_t h_a_hi_t h_match h_input_r1
  have h_input_r2_row :
      r2_val = ZiskFv.EquivCore.Add.binaryRowB64 providerInput := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      ZiskFv.EquivCore.Bridge.Binary.input_r2_packed_b_row
        m providerInput i.val (regidx_to_fin r2) r2_val
        h_matches h_m32_zero h_b_lo_t h_b_hi_t h_match h_input_r2
  exact ZiskFv.EquivCore.Bridge.Binary.branch_flag_eq_of_static_row
    m i.val providerInput r1_val r2_val h_match h_core h_facts h_row_m32 h_bop
    h_input_r1_row h_input_r2_row

/-- Strengthened `beq` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.beq` from the trace's `RowData_beq` (the same
    `BranchInstrOperands` + `BranchPromises` `construction_beq_sound` builds) and
    invoke `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_branch`
    conjunct.  `aeneasBridgeTrust` is flat decode pins carried as `RowData_beq`
    residuals; `NoKnownDefect` comes from the locally-assembled `NoKnownDefect`. -/
theorem stepStrong_beq
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_beq trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.BTYPE (d.toClaim.imm, d.toClaim.r2, d.toClaim.r1, bop.BEQ)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.toClaim.imm, d.toClaim.r1, d.toClaim.r2, d.toInputs.misa_val, Pilot.execRowOf trace i⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.toInputs.beq_input.imm d.toInputs.beq_input.r1_val d.toInputs.beq_input.r2_val d.toInputs.beq_input.PC
      ops.misa_val
      (PureSpec.execute_BEQ_pure d.toInputs.beq_input).nextPC
      (PureSpec.execute_BEQ_pure d.toInputs.beq_input).throws
      (PureSpec.execute_BEQ_pure d.toInputs.beq_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED. `flag = (r1 == r2 ? 1 : 0)` from the
      -- OP_EQ Binary provider (`branch_flag_eq_provided`); flag1-taken cast.
      nextPC_matches := by
        have h_flag : m.flag i.val
            = if d.toInputs.beq_input.r1_val == d.toInputs.beq_input.r2_val
              then 1 else 0 :=
          branch_flag_eq_provided trace binding i d.toClaim.r1 d.toClaim.r2
            d.toInputs.beq_input.r1_val d.toInputs.beq_input.r2_val
            d.toDecode.h_main_active d.toDecode.h_main_op d.toDecode.h_m32
            d.toInputs.h_a_lo_t d.toInputs.h_a_hi_t d.toInputs.h_b_lo_t d.toInputs.h_b_hi_t
            d.toInputs.h_input_r1 d.toInputs.h_input_r2
        have h_off_bridge :
            (m.jmp_offset1 i.val).val =
              (BitVec.signExtend 64 d.toInputs.beq_input.imm).toNat := by
          simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset1_imm
        have h_cast := Pilot.branch_nextPC_flag1_taken trace i
          (d.toInputs.beq_input.r1_val == d.toInputs.beq_input.r2_val)
          d.toInputs.beq_input.PC (BitVec.signExtend 64 d.toInputs.beq_input.imm)
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag d.toDecode.h_jmp_offset2
          h_off_bridge d.toInputs.h_pc_bridge d.toInputs.h_no_wrap
          d.toInputs.h_pc_bound
        show (register_type_pc_equiv ▸
            (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
          = (PureSpec.execute_BEQ_pure d.toInputs.beq_input).nextPC
        rw [h_cast]
        exact (PureSpec.execute_BEQ_pure_nextPC_of_success
          d.toInputs.beq_input d.toInputs.h_success).symm
      not_throws :=
        PureSpec.execute_BEQ_pure_succ_throws
          d.toInputs.beq_input d.toInputs.h_success
      success := d.toInputs.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.beq d.toInputs.beq_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bne` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bne
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_bne trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.BTYPE (d.toClaim.imm, d.toClaim.r2, d.toClaim.r1, bop.BNE)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.toClaim.imm, d.toClaim.r1, d.toClaim.r2, d.toInputs.misa_val, Pilot.execRowOf trace i⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.toInputs.bne_input.imm d.toInputs.bne_input.r1_val d.toInputs.bne_input.r2_val d.toInputs.bne_input.PC
      ops.misa_val
      (PureSpec.execute_BNE_pure d.toInputs.bne_input).nextPC
      (PureSpec.execute_BNE_pure d.toInputs.bne_input).throws
      (PureSpec.execute_BNE_pure d.toInputs.bne_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED. `flag = (r1 == r2 ? 1 : 0)` from the
      -- OP_EQ Binary provider; `neg` polarity (taken on flag=0), flag0-taken cast.
      nextPC_matches := by
        have h_flag : m.flag i.val
            = if d.toInputs.bne_input.r1_val == d.toInputs.bne_input.r2_val
              then 1 else 0 :=
          branch_flag_eq_provided trace binding i d.toClaim.r1 d.toClaim.r2
            d.toInputs.bne_input.r1_val d.toInputs.bne_input.r2_val
            d.toDecode.h_main_active d.toDecode.h_main_op d.toDecode.h_m32
            d.toInputs.h_a_lo_t d.toInputs.h_a_hi_t d.toInputs.h_b_lo_t d.toInputs.h_b_hi_t
            d.toInputs.h_input_r1 d.toInputs.h_input_r2
        have h_off_bridge :
            (m.jmp_offset2 i.val).val =
              (BitVec.signExtend 64 d.toInputs.bne_input.imm).toNat := by
          simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset2_imm
        have h_cast := Pilot.branch_nextPC_flag0_taken trace i
          (d.toInputs.bne_input.r1_val == d.toInputs.bne_input.r2_val)
          d.toInputs.bne_input.PC (BitVec.signExtend 64 d.toInputs.bne_input.imm)
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag d.toDecode.h_jmp_offset1
          h_off_bridge d.toInputs.h_pc_bridge d.toInputs.h_no_wrap
          d.toInputs.h_pc_bound
        show (register_type_pc_equiv ▸
            (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
          = (PureSpec.execute_BNE_pure d.toInputs.bne_input).nextPC
        rw [h_cast]
        exact (PureSpec.execute_BNE_pure_nextPC_of_success
          d.toInputs.bne_input d.toInputs.h_success).symm
      not_throws :=
        PureSpec.execute_BNE_pure_succ_throws
          d.toInputs.bne_input d.toInputs.h_success
      success := d.toInputs.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bne d.toInputs.bne_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, d.toDecode.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `blt` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_blt
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_blt trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.BTYPE (d.toClaim.imm, d.toClaim.r2, d.toClaim.r1, bop.BLT)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.toClaim.imm, d.toClaim.r1, d.toClaim.r2, d.toInputs.misa_val, Pilot.execRowOf trace i⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.toInputs.blt_input.imm d.toInputs.blt_input.r1_val d.toInputs.blt_input.r2_val d.toInputs.blt_input.PC
      ops.misa_val
      (PureSpec.execute_BLT_pure d.toInputs.blt_input).nextPC
      (PureSpec.execute_BLT_pure d.toInputs.blt_input).throws
      (PureSpec.execute_BLT_pure d.toInputs.blt_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED. `flag = (r1 <s r2 ? 1 : 0)` from the
      -- OP_LT Binary provider (`branch_flag_lt_provided`); flag1-taken cast.
      nextPC_matches := by
        have h_flag : m.flag i.val
            = if BitVec.slt d.toInputs.blt_input.r1_val d.toInputs.blt_input.r2_val
              then 1 else 0 :=
          branch_flag_lt_provided trace binding i d.toClaim.r1 d.toClaim.r2
            d.toInputs.blt_input.r1_val d.toInputs.blt_input.r2_val
            d.toDecode.h_main_active d.toDecode.h_main_op d.toDecode.h_m32
            d.toInputs.h_a_lo_t d.toInputs.h_a_hi_t d.toInputs.h_b_lo_t d.toInputs.h_b_hi_t
            d.toInputs.h_input_r1 d.toInputs.h_input_r2
        have h_off_bridge :
            (m.jmp_offset1 i.val).val =
              (BitVec.signExtend 64 d.toInputs.blt_input.imm).toNat := by
          simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset1_imm
        have h_cast := Pilot.branch_nextPC_flag1_taken trace i
          (BitVec.slt d.toInputs.blt_input.r1_val d.toInputs.blt_input.r2_val)
          d.toInputs.blt_input.PC (BitVec.signExtend 64 d.toInputs.blt_input.imm)
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag d.toDecode.h_jmp_offset2
          h_off_bridge d.toInputs.h_pc_bridge d.toInputs.h_no_wrap
          d.toInputs.h_pc_bound
        show (register_type_pc_equiv ▸
            (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
          = (PureSpec.execute_BLT_pure d.toInputs.blt_input).nextPC
        rw [h_cast]
        exact (PureSpec.execute_BLT_pure_nextPC_of_success
          d.toInputs.blt_input d.toInputs.h_success).symm
      not_throws :=
        PureSpec.execute_BLT_pure_succ_throws
          d.toInputs.blt_input d.toInputs.h_success
      success := d.toInputs.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.blt d.toInputs.blt_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bge` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bge
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_bge trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.BTYPE (d.toClaim.imm, d.toClaim.r2, d.toClaim.r1, bop.BGE)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.toClaim.imm, d.toClaim.r1, d.toClaim.r2, d.toInputs.misa_val, Pilot.execRowOf trace i⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.toInputs.bge_input.imm d.toInputs.bge_input.r1_val d.toInputs.bge_input.r2_val d.toInputs.bge_input.PC
      ops.misa_val
      (PureSpec.execute_BGE_pure d.toInputs.bge_input).nextPC
      (PureSpec.execute_BGE_pure d.toInputs.bge_input).throws
      (PureSpec.execute_BGE_pure d.toInputs.bge_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED. `flag = (r1 <s r2 ? 1 : 0)` from the
      -- OP_LT Binary provider; `neg` polarity (taken on flag=0), flag0-taken cast.
      nextPC_matches := by
        have h_flag : m.flag i.val
            = if BitVec.slt d.toInputs.bge_input.r1_val d.toInputs.bge_input.r2_val
              then 1 else 0 :=
          branch_flag_lt_provided trace binding i d.toClaim.r1 d.toClaim.r2
            d.toInputs.bge_input.r1_val d.toInputs.bge_input.r2_val
            d.toDecode.h_main_active d.toDecode.h_main_op d.toDecode.h_m32
            d.toInputs.h_a_lo_t d.toInputs.h_a_hi_t d.toInputs.h_b_lo_t d.toInputs.h_b_hi_t
            d.toInputs.h_input_r1 d.toInputs.h_input_r2
        have h_off_bridge :
            (m.jmp_offset2 i.val).val =
              (BitVec.signExtend 64 d.toInputs.bge_input.imm).toNat := by
          simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset2_imm
        have h_cast := Pilot.branch_nextPC_flag0_taken trace i
          (BitVec.slt d.toInputs.bge_input.r1_val d.toInputs.bge_input.r2_val)
          d.toInputs.bge_input.PC (BitVec.signExtend 64 d.toInputs.bge_input.imm)
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag d.toDecode.h_jmp_offset1
          h_off_bridge d.toInputs.h_pc_bridge d.toInputs.h_no_wrap
          d.toInputs.h_pc_bound
        show (register_type_pc_equiv ▸
            (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
          = (PureSpec.execute_BGE_pure d.toInputs.bge_input).nextPC
        rw [h_cast]
        exact (PureSpec.execute_BGE_pure_nextPC_of_success
          d.toInputs.bge_input d.toInputs.h_success).symm
      not_throws :=
        PureSpec.execute_BGE_pure_succ_throws
          d.toInputs.bge_input d.toInputs.h_success
      success := d.toInputs.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bge d.toInputs.bge_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, d.toDecode.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bltu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bltu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_bltu trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.BTYPE (d.toClaim.imm, d.toClaim.r2, d.toClaim.r1, bop.BLTU)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.toClaim.imm, d.toClaim.r1, d.toClaim.r2, d.toInputs.misa_val, Pilot.execRowOf trace i⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.toInputs.bltu_input.imm d.toInputs.bltu_input.r1_val d.toInputs.bltu_input.r2_val d.toInputs.bltu_input.PC
      ops.misa_val
      (PureSpec.execute_BLTU_pure d.toInputs.bltu_input).nextPC
      (PureSpec.execute_BLTU_pure d.toInputs.bltu_input).throws
      (PureSpec.execute_BLTU_pure d.toInputs.bltu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED. `flag = (r1 <u r2 ? 1 : 0)` from the
      -- LTU Binary provider (`branch_flag_ltu_provided`); the set_pc=0 flag-mux
      -- cast (`branch_nextPC_flag1_taken`, taken on flag=1, `jmp_offset2 = 4`,
      -- `jmp_offset1 = signExtend imm`) gives the Sail conditional next-PC, which
      -- `execute_BLTU_pure_nextPC_of_success` identifies with the pure-spec value.
      nextPC_matches := by
        have h_flag : m.flag i.val
            = if BitVec.ult d.toInputs.bltu_input.r1_val d.toInputs.bltu_input.r2_val
              then 1 else 0 :=
          branch_flag_ltu_provided trace binding i d.toClaim.r1 d.toClaim.r2
            d.toInputs.bltu_input.r1_val d.toInputs.bltu_input.r2_val
            d.toDecode.h_main_active d.toDecode.h_main_op d.toDecode.h_m32
            d.toInputs.h_a_lo_t d.toInputs.h_a_hi_t d.toInputs.h_b_lo_t d.toInputs.h_b_hi_t
            d.toInputs.h_input_r1 d.toInputs.h_input_r2
        have h_off_bridge :
            (m.jmp_offset1 i.val).val =
              (BitVec.signExtend 64 d.toInputs.bltu_input.imm).toNat := by
          simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset1_imm
        have h_cast := Pilot.branch_nextPC_flag1_taken trace i
          (BitVec.ult d.toInputs.bltu_input.r1_val d.toInputs.bltu_input.r2_val)
          d.toInputs.bltu_input.PC (BitVec.signExtend 64 d.toInputs.bltu_input.imm)
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag d.toDecode.h_jmp_offset2
          h_off_bridge d.toInputs.h_pc_bridge d.toInputs.h_no_wrap
          d.toInputs.h_pc_bound
        show (register_type_pc_equiv ▸
            (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
          = (PureSpec.execute_BLTU_pure d.toInputs.bltu_input).nextPC
        rw [h_cast]
        exact (PureSpec.execute_BLTU_pure_nextPC_of_success
          d.toInputs.bltu_input d.toInputs.h_success).symm
      not_throws :=
        PureSpec.execute_BLTU_pure_succ_throws
          d.toInputs.bltu_input d.toInputs.h_success
      success := d.toInputs.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bltu d.toInputs.bltu_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, d.toDecode.h_jmp_offset2⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `bgeu` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_bgeu
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_bgeu trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.BTYPE (d.toClaim.imm, d.toClaim.r2, d.toClaim.r1, bop.BGEU)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels ⟨Pilot.execRowOf trace i, []⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨d.toClaim.imm, d.toClaim.r1, d.toClaim.r2, d.toInputs.misa_val, Pilot.execRowOf trace i⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state d.toInputs.bgeu_input.imm d.toInputs.bgeu_input.r1_val d.toInputs.bgeu_input.r2_val d.toInputs.bgeu_input.PC
      ops.misa_val
      (PureSpec.execute_BGEU_pure d.toInputs.bgeu_input).nextPC
      (PureSpec.execute_BGEU_pure d.toInputs.bgeu_input).throws
      (PureSpec.execute_BGEU_pure d.toInputs.bgeu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_r1_eq := d.toInputs.h_input_r1
      input_r2_eq := d.toInputs.h_input_r2
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED. `flag = (r1 <u r2 ? 1 : 0)` from the
      -- LTU Binary provider; BGEU is the `neg` polarity (taken on flag=0): the
      -- cast (`branch_nextPC_flag0_taken`, `jmp_offset1 = 4`, taken offset on
      -- `jmp_offset2 = signExtend imm`) gives the Sail conditional next-PC, which
      -- `execute_BGEU_pure_nextPC_of_success` identifies with the pure-spec value.
      nextPC_matches := by
        have h_flag : m.flag i.val
            = if BitVec.ult d.toInputs.bgeu_input.r1_val d.toInputs.bgeu_input.r2_val
              then 1 else 0 :=
          branch_flag_ltu_provided trace binding i d.toClaim.r1 d.toClaim.r2
            d.toInputs.bgeu_input.r1_val d.toInputs.bgeu_input.r2_val
            d.toDecode.h_main_active d.toDecode.h_main_op d.toDecode.h_m32
            d.toInputs.h_a_lo_t d.toInputs.h_a_hi_t d.toInputs.h_b_lo_t d.toInputs.h_b_hi_t
            d.toInputs.h_input_r1 d.toInputs.h_input_r2
        have h_off_bridge :
            (m.jmp_offset2 i.val).val =
              (BitVec.signExtend 64 d.toInputs.bgeu_input.imm).toNat := by
          simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset2_imm
        have h_cast := Pilot.branch_nextPC_flag0_taken trace i
          (BitVec.ult d.toInputs.bgeu_input.r1_val d.toInputs.bgeu_input.r2_val)
          d.toInputs.bgeu_input.PC (BitVec.signExtend 64 d.toInputs.bgeu_input.imm)
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag d.toDecode.h_jmp_offset1
          h_off_bridge d.toInputs.h_pc_bridge d.toInputs.h_no_wrap
          d.toInputs.h_pc_bound
        show (register_type_pc_equiv ▸
            (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
          = (PureSpec.execute_BGEU_pure d.toInputs.bgeu_input).nextPC
        rw [h_cast]
        exact (PureSpec.execute_BGEU_pure_nextPC_of_success
          d.toInputs.bgeu_input d.toInputs.h_success).symm
      not_throws :=
        PureSpec.execute_BGEU_pure_succ_throws
          d.toInputs.bgeu_input d.toInputs.h_success
      success := d.toInputs.h_success }
  let env : OpEnvelope state m i.val := OpEnvelope.bgeu d.toInputs.bgeu_input ops promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, d.toDecode.h_jmp_offset1⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.1

/-- Strengthened `lui` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.lui` from the trace's `RowData_lui` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_nomem` conjunct.

    The `OpEnvelope.lui` arm's `provenance`/`row_mode` are BUILT from the five
    Main-row mode pins already carried as `RowData_lui` residuals
    (`mainRowProvenance_of_pins` + `luiRowMode_of_extracted_shape`).  This is PATH
    1 (trace-built): the consumed provenance fields reduce to exactly those five
    honest decode residuals, so the conversion adds no trust over the prior
    direct-lift arm.  `aeneasBridgeTrust` is the LUI tuple
    `⟨⟨provenance⟩, row_mode, h_imm_lo_nat, h_imm_hi_nat⟩`; `memoryTimeline`
    trivially; `NoKnownDefect` from the locally-assembled `NoKnownDefect` (non-defect). -/
theorem stepStrong_lui
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_lui trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.UTYPE (d.toClaim.imm, d.toClaim.rd, uop.LUI)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf trace i, [eRdLui trace i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace i
  -- (a) Main per-row Spec ⇒ the LUI Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, h_b0, _h_c1, h_b1, _h_set_flag, h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_lui_subset :
      ZiskFv.Tactics.UTypeArchetype.lui_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_b0, h_b1, h_clear_flag, h_handshake⟩
  -- (b1) provenance + row_mode built from the five decode pins.
  let provenance : ZiskFv.Compliance.MainRowProvenance m i.val :=
    mainRowProvenance_of_pins m i.val ZiskFv.Compliance.ExtractedConst.opCopyB
      false false false false
      (by simpa [ZiskFv.Trusted.OP_COPYB, ZiskFv.Compliance.natF,
        ZiskFv.Compliance.ExtractedConst.opCopyB] using d.toDecode.h_main_op)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_main_active)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_m32)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_set_pc)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_store_pc)
  let row_mode : ZiskFv.Compliance.MainRowProvenance.LuiRowMode provenance :=
    { op_eq := rfl, internal_eq := rfl, m32_eq := rfl, set_pc_eq := rfl, store_pc_eq := rfl }
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.UTypePromises
      state d.toInputs.lui_input.imm d.toInputs.lui_input.rd d.toInputs.lui_input.PC
      (PureSpec.execute_LUI_pure d.toInputs.lui_input).nextPC
      d.toClaim.imm d.toClaim.rd (Pilot.execRowOf trace i) e_rd (d.toInputs.lui_input.PC + 4#64) :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound
      rd_mult := by rfl
      rd_as := by rfl
      nextPC_eq := rfl
      rd_idx := d.toInputs.h_input_rd.trans
        (eRdLui_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset) }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.lui d.toInputs.lui_input d.toClaim.imm d.toClaim.rd next_pc (Pilot.execRowOf trace i) e_rd store_pc_mem
      provenance row_mode h_lui_subset d.toDecode.h_imm_lo_nat d.toDecode.h_imm_hi_nat promises
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨⟨provenance⟩, row_mode, d.toDecode.h_imm_lo_nat, d.toDecode.h_imm_hi_nat⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.1

/-- Strengthened `auipc` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.auipc` from the trace's `RowData_auipc` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_nomem` conjunct.

    Same PATH-1 provenance construction as `stepStrong_lui`: the AUIPC
    `provenance`/`row_mode` are BUILT from the five mode pins
    (`mainRowProvenance_of_pins` + `auipcRowMode_of_extracted_shape`-shape record).
    `aeneasBridgeTrust` is the AUIPC tuple
    `⟨⟨provenance⟩, row_mode, h_offset_bridge, h_pc_bridge⟩`; `NoKnownDefect` from
    the locally-assembled `NoKnownDefect` (non-defect). -/
theorem stepStrong_auipc
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_auipc trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.UTYPE (d.toClaim.imm, d.toClaim.rd, uop.AUIPC)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf trace i, [eRdLui trace i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace i
  -- (a) Main per-row Spec ⇒ the AUIPC Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨h_c0, _h_b0, h_c1, _h_b1, h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- #100: `flag = 1` is DERIVED (not pinned) from the OP_FLAG decode pins
  -- (`is_external_op = 0`, `op = OP_FLAG = 0`) and the Main `internal_op0_sets_flag`
  -- constraint (`h_set_flag`), exactly as `auipc_archetype_pc_advance` does.
  have h_flag : m.flag i.val = 1 :=
    ZiskFv.Airs.Main.flag_eq_one_of_internal_op_zero m i.val d.toDecode.h_main_active
      (by simpa [ZiskFv.Trusted.OP_FLAG] using d.toDecode.h_main_op) h_set_flag
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_auipc_subset :
      ZiskFv.Tactics.UTypeArchetype.auipc_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0, h_c1, h_set_flag, h_handshake⟩
  -- (b1) provenance + row_mode built from the five decode pins.
  let provenance : ZiskFv.Compliance.MainRowProvenance m i.val :=
    mainRowProvenance_of_pins m i.val ZiskFv.Compliance.ExtractedConst.opFlag
      false false false true
      (by simpa [ZiskFv.Trusted.OP_FLAG, ZiskFv.Compliance.natF,
        ZiskFv.Compliance.ExtractedConst.opFlag] using d.toDecode.h_main_op)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_main_active)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_m32)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_set_pc)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_store_pc)
  let row_mode : ZiskFv.Compliance.MainRowProvenance.AuipcRowMode provenance :=
    { op_eq := rfl, internal_eq := rfl, m32_eq := rfl, set_pc_eq := rfl, store_pc_eq := rfl }
  have h_offset_bridge :
      (m.jmp_offset2 i.val).val =
        (BitVec.signExtend 64 (d.toInputs.auipc_input.imm ++ (0 : BitVec 12))).toNat := by
    simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset2_imm
  have h_row_core :
      (mainRowWithRomLui trace i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.UTypePromises
      state d.toInputs.auipc_input.imm d.toInputs.auipc_input.rd d.toInputs.auipc_input.PC
      (PureSpec.execute_AUIPC_pure d.toInputs.auipc_input).nextPC
      d.toClaim.imm d.toClaim.rd (Pilot.execRowOf trace i) e_rd (PureSpec.execute_AUIPC_pure d.toInputs.auipc_input).nextPC :=
    { input_imm_eq := d.toInputs.h_input_imm
      input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED from the in-circuit transition
      -- certificate via the FLAG-PATH lemma (set_pc=0, flag=1 ⇒ pc + jmp_offset1),
      -- then `jmp_offset1 = 4` and the `pc + 4` wide-PC cast give AUIPC's
      -- Sail `nextPC = PC + 4#64`.
      nextPC_matches := by
        have hstep := Pilot.flag_path_nextPC_discharged trace i
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag
        rw [hstep, d.toDecode.h_jmp1]
        exact Pilot.ofNat_fgl_pc_plus_4_eq _ d.toInputs.auipc_input.PC
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound
      rd_mult := by rfl
      rd_as := by rfl
      nextPC_eq := rfl
      rd_idx := d.toInputs.h_input_rd.trans
        (eRdLui_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset) }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.auipc d.toInputs.auipc_input d.toClaim.imm d.toClaim.rd (Pilot.execRowOf trace i) e_rd
      (PureSpec.execute_AUIPC_pure d.toInputs.auipc_input).nextPC next_pc store_pc_mem
      provenance row_mode h_auipc_subset h_offset_bridge d.toInputs.h_pc_bridge promises
      d.toInputs.h_no_wrap d.toInputs.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨⟨provenance⟩, row_mode, h_offset_bridge, d.toInputs.h_pc_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.1

/-- Strengthened `jal` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.jal` from the trace's `RowData_jal` and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.

    Same PATH-1 provenance construction as `stepStrong_lui`/`stepStrong_auipc`:
    the JAL `provenance`/`row_mode` are BUILT from the five mode pins
    (`mainRowProvenance_of_pins`).  `aeneasBridgeTrust` is the JAL tuple
    `⟨⟨provenance⟩, row_mode, h_jmp2, h_pc_bridge⟩`; `NoKnownDefect` from the
    locally-assembled `NoKnownDefect` (non-defect). -/
theorem stepStrong_jal
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_jal trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.JAL (d.toClaim.imm, d.toClaim.rd)) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf trace i, [eRdLui trace i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace i
  -- (a) Main per-row Spec ⇒ the JAL Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨h_c0, _h_b0, h_c1, _h_b1, h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- #100: `flag = 1` is DERIVED (not pinned) from the OP_FLAG decode pins
  -- and the Main `internal_op0_sets_flag` constraint (`h_set_flag`).
  have h_flag : m.flag i.val = 1 :=
    ZiskFv.Airs.Main.flag_eq_one_of_internal_op_zero m i.val d.toDecode.h_main_active
      (by simpa [ZiskFv.Trusted.OP_FLAG] using d.toDecode.h_main_op) h_set_flag
  let nextPC_val : BitVec 64 :=
    d.toInputs.jal_input.PC + BitVec.signExtend 64 d.toInputs.jal_input.imm
  have h_nextPC_option :
      (PureSpec.execute_JAL_pure d.toInputs.jal_input).nextPC = .some nextPC_val :=
    PureSpec.execute_JAL_pure_succ_nextPC d.toInputs.jal_input d.toInputs.h_success
  -- #100: the field-level no-wrap bound (`pc.val + jmp_offset1.val < GL_prime`),
  -- in column form for `ofNat_fgl_pc_plus_offset_eq`, from the input-facing
  -- target bound via the PC / offset row-shape bridges.
  have h_offset_bridge :
      (m.jmp_offset1 i.val).val =
        (BitVec.signExtend 64 d.toInputs.jal_input.imm).toNat := by
    simpa [hm, d.toInputs.h_input_imm] using d.toDecode.h_jmp_offset1_imm
  have h_no_wrap_fgl :
      ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).pc i.val).val
        + ((ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable).jmp_offset1
            i.val).val
        < GL_prime := by
    rw [d.toInputs.h_pc_bridge, h_offset_bridge]
    exact d.toInputs.h_no_fgl_wrap
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_c0, h_c1, h_set_flag, h_handshake⟩
  -- (b1) provenance + row_mode built from the five decode pins.
  let provenance : ZiskFv.Compliance.MainRowProvenance m i.val :=
    mainRowProvenance_of_pins m i.val ZiskFv.Compliance.ExtractedConst.opFlag
      false false false true
      (by simpa [ZiskFv.Trusted.OP_FLAG, ZiskFv.Compliance.natF,
        ZiskFv.Compliance.ExtractedConst.opFlag] using d.toDecode.h_main_op)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_main_active)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_m32)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_set_pc)
      (by simpa [ZiskFv.Compliance.boolF] using d.toDecode.h_store_pc)
  let row_mode : ZiskFv.Compliance.MainRowProvenance.JalRowMode provenance :=
    { op_eq := rfl, internal_eq := rfl, m32_eq := rfl, set_pc_eq := rfl, store_pc_eq := rfl }
  have h_row_core :
      (mainRowWithRomLui trace i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state d.toInputs.jal_input.PC d.toInputs.jal_input.rd d.toInputs.misa_val
      (PureSpec.execute_JAL_pure d.toInputs.jal_input).success
      (PureSpec.execute_JAL_pure d.toInputs.jal_input).nextPC
      d.toClaim.rd (Pilot.execRowOf trace i) e_rd nextPC_val :=
    { input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      -- #100: next-PC residual DISCHARGED from the in-circuit transition
      -- certificate via the FLAG-PATH lemma (set_pc=0, flag=1 ⇒ pc + jmp_offset1),
      -- then the signed-offset wide-PC cast (`jmp_offset1 = signExtend imm` +
      -- target no-wrap) gives JAL's taken target `PC + signExtend 64 imm`,
      -- with `nextPC_val` chosen as that computed target.
      nextPC_matches := by
        have hstep := Pilot.flag_path_nextPC_discharged trace i
          d.toDecode.h_idx d.toDecode.h_set_pc h_flag
        rw [hstep]
        simpa [nextPC_val] using (Pilot.ofNat_fgl_pc_plus_offset_eq _ _
          d.toInputs.jal_input.PC (BitVec.signExtend 64 d.toInputs.jal_input.imm)
          d.toInputs.h_pc_bridge h_offset_bridge h_no_wrap_fgl)
      rd_mult := by rfl
      rd_as := by rfl
      success := d.toInputs.h_success
      nextPC_option := h_nextPC_option
      rd_idx := d.toInputs.h_input_rd.trans
        (eRdLui_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset) }
  have h_not_throws : (PureSpec.execute_JAL_pure d.toInputs.jal_input).throws = false :=
    PureSpec.execute_JAL_pure_succ_throws
      d.toInputs.jal_input d.toInputs.h_success
  let env : OpEnvelope state m i.val :=
    OpEnvelope.jal d.toInputs.jal_input d.toClaim.imm d.toClaim.rd d.toInputs.misa_val next_pc (Pilot.execRowOf trace i) e_rd
      nextPC_val store_pc_mem provenance row_mode h_jal_subset d.toDecode.h_jmp2 d.toInputs.h_pc_bridge
      promises d.toInputs.h_input_imm h_not_throws d.toInputs.h_pc_bound d.toInputs.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨⟨provenance⟩, row_mode, d.toDecode.h_jmp2, d.toInputs.h_pc_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `jalr` step (channel-balance form), via the OpEnvelope route:
    CONSTRUCT `OpEnvelope.jalr` from the trace's `RowData_jalr` (mirroring
    `construction_jalr_sound`'s internal `next_pc` / `e_rd` / `store_pc_mem` /
    `pins` / `h_jalr_subset` / `promises` derivations) and invoke
    `zisk_riscv_compliant_program_bus`, projecting the `exec_eq_remaining`
    conjunct.  The non-defect arm carries no defect obligation (`True`);
    `NoKnownDefect` is assembled locally via `noKnownDefect_of_shapes`.  JALR's
    `aeneasBridgeTrust` is flat decode pins already in
    `RowData_jalr` (no `MainRowProvenance`). -/
theorem stepStrong_jalr
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_jalr trace binding i)
    (_h_known : True) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.JALR (d.toClaim.imm, d.toClaim.rs1, d.toClaim.rd))) (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨Pilot.execRowOf trace i, [eRdLui trace i]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let e_rd := eRdLui trace i
  -- (a) Main per-row Spec ⇒ the JALR Main constraint subset.
  have h_spec := mainSpec_at trace binding i
  have h_add_subset : ZiskFv.Airs.Main.add_subset_holds m i.val :=
    ZiskFv.AirsClean.Main.add_subset_holds_of_spec_rowAt m i.val h_spec
  obtain ⟨_h_c0, _h_b0, _h_c1, _h_b1, _h_set_flag, _h_clear_flag, h_disjoint,
      h_flag_bool, h_ext_bool⟩ := h_add_subset
  -- (a) the handshake is definitional: pick `next_pc` as its RHS.
  let next_pc : FGL :=
    m.set_pc i.val * (m.c_0 i.val + m.jmp_offset1 i.val)
      + (1 - m.set_pc i.val) * (m.pc i.val + m.jmp_offset2 i.val)
      + m.flag i.val * (m.jmp_offset1 i.val - m.jmp_offset2 i.val)
  have h_handshake :
      ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc := rfl
  have h_jalr_subset :
      ZiskFv.Airs.Main.flag_boolean m i.val
      ∧ ZiskFv.Airs.Main.is_external_op_boolean m i.val
      ∧ ZiskFv.Airs.Main.flag_set_pc_disjoint m i.val
      ∧ ZiskFv.Airs.Main.pc_handshake_with_next_pc m i.val next_pc :=
    ⟨h_flag_bool, h_ext_bool, h_disjoint, h_handshake⟩
  -- (a) `StorePcMemoryWitness` from the real Clean Main `c` message row.
  have h_row_core :
      (mainRowWithRomLui trace i).core =
        ZiskFv.AirsClean.Main.rowAt m i.val := by
    have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
      trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
    simpa [mainRowWithRomLui, m,
      ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get (idx := ⟨i.val, trace.mainTable_index i⟩)] using this.symm
  let store_pc_mem : ZiskFv.Compliance.StorePcMemoryWitness m i.val e_rd :=
    { row := mainRowWithRomLui trace i
      row_eq := h_row_core
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let pins : ZiskFv.Compliance.MainRowPins m i.val 1 OP_AND :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  -- (b) Binary `OP_AND` provider witnesses for the JALR row (mirrors
  --     `stepStrong_and`): the static Binary table row backing the masked-AND.
  obtain ⟨providerTable, _h_pt_mem, providerRow, h_provider_row,
      h_component, h_table_spec, h_match⟩ :=
    main_request_logic_provided
      trace i d.toDecode.h_main_active (Or.inl d.toDecode.h_main_op)
  let providerInput :=
    ZiskFv.AirsClean.Binary.staticLookupComponent.rowInput
      (providerTable.environment providerRow)
  obtain ⟨h_core, h_facts⟩ :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_core_and_wf_of_table_spec
      h_component h_table_spec h_provider_row
  have h_static :
      ZiskFv.AirsClean.Binary.StaticBinaryTableSpecFacts providerInput :=
    ZiskFv.AirsClean.BinaryFamily.staticBinary_spec_facts_of_table_spec
      h_component h_table_spec h_provider_row
  have h_m32_zero : m.m32 i.val = 0 := d.toDecode.h_m32
  have h_emit :
      providerInput.chain.b_op + 16 * providerInput.mode.mode32 =
        (ZiskFv.Airs.Tables.BinaryTable.OP_AND : FGL) := by
    have h_match_op := h_match
    simp only [ZiskFv.Airs.OperationBus.matches_entry,
      ZiskFv.Airs.OperationBus.opBus_row_Main] at h_match_op
    have h_op_match :
        m.op i.val = providerInput.chain.b_op + 16 * providerInput.mode.mode32 :=
      h_match_op.2.1
    rw [← h_op_match]
    simpa [ZiskFv.Airs.Tables.BinaryTable.OP_AND, ZiskFv.Trusted.OP_AND] using
      d.toDecode.h_main_op
  obtain ⟨h_row_m32, h_bop, _⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.logic_row_mode_pins_of_emit_op_lt_16_of_static_spec
      providerInput h_static ZiskFv.Airs.Tables.BinaryTable.OP_AND (by
        simp [ZiskFv.Airs.Tables.BinaryTable.OP_AND])
      h_core h_emit
  have h_out :=
    ZiskFv.EquivCore.Bridge.Binary.byte_chain_discharge_64_of_static_row
      providerInput h_facts
      ZiskFv.Airs.Tables.BinaryTable.OP_AND h_core h_row_m32 h_bop
  have h_matches :
      ZiskFv.EquivCore.Bridge.Binary.all_byte_matches_wf_at_row
        providerInput ZiskFv.Airs.Tables.BinaryTable.OP_AND :=
    allByteMatchesOfStaticOut64_local h_out
  -- (c) lane projections: `a = mask`, `b = operand` (committed `b`-lane packing),
  --     and the carry-free `c` lanes (from `flag = 0`).
  have h_a_mask :
      ZiskFv.EquivCore.Add.binaryRowA64 providerInput = 0xFFFFFFFFFFFFFFFE#64 := by
    have h_a_pack : ZiskFv.EquivCore.Add.binaryRowA64 providerInput
        = BitVec.ofNat 64 ((m.a_0 i.val).val + (m.a_1 i.val).val * 4294967296) := by
      simpa [ZiskFv.EquivCore.Add.binaryRowA64] using
        (ZiskFv.EquivCore.Bridge.Binary.main_a_packing_of_match
          m providerInput i.val h_matches h_m32_zero h_match).symm
    rw [h_a_pack, d.toDecode.h_a_mask_lo, d.toDecode.h_a_mask_hi]
    decide
  have h_b_operand :
      ZiskFv.EquivCore.Add.binaryRowB64 providerInput
        = BitVec.ofNat 64 ((m.b_0 i.val).val + (m.b_1 i.val).val * 4294967296) := by
    simpa [ZiskFv.EquivCore.Add.binaryRowB64] using
      (ZiskFv.EquivCore.Bridge.Binary.main_b_packing_of_match
        m providerInput i.val h_matches h_m32_zero h_match).symm
  obtain ⟨h_match_clo, h_match_chi⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.main_c_lanes_carryfree_of_match
      m providerInput i.val h_match d.toDecode.h_flag
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ :=
    ZiskFv.EquivCore.Bridge.Binary.cByte_ranges_of_all_byte_matches_row
      providerInput h_matches
  let nextPC_val : BitVec 64 :=
    0xFFFFFFFFFFFFFFFE &&&
      (d.toInputs.jalr_input.rs1_val + BitVec.signExtend 64 d.toInputs.jalr_input.imm)
  have h_nextPC_option :
      (PureSpec.execute_JALR_pure d.toInputs.jalr_input).nextPC = .some nextPC_val :=
    PureSpec.execute_JALR_pure_succ_nextPC d.toInputs.jalr_input d.toInputs.h_success
  -- (e) #100: the cross-world next-PC residual is DISCHARGED from the accepted
  --     trace's in-circuit set-PC handshake composed with the masked-AND
  --     target-value derivation (`jalr_setpc_nextPC_discharged`), then bridged to
  --     Sail's `mask &&& (rs1 + signExtend imm)` via the per-lowering operand
  --     identity (`h_operand_offset`) and the success-branch target (`h_target`).
  have h_nextPC_disch :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((Pilot.execRowOf trace i)[1]!.pc).val))
        = nextPC_val := by
    have hoo := d.toInputs.h_operand_offset
    rw [← hm] at hoo
    rw [ZiskFv.Compliance.Pilot.jalr_setpc_nextPC_discharged
          trace i providerInput
          (BitVec.ofNat 64 ((m.b_0 i.val).val + (m.b_1 i.val).val * 4294967296))
          d.toClaim.offset_bv
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_flag
          h_matches h_match_clo h_match_chi h_a_mask h_b_operand
          hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
          d.toDecode.h_c1_zero d.toDecode.h_offset_bridge
          d.toDecode.h_offset_even d.toDecode.h_no_fgl_wrap,
        hoo]
    simp [nextPC_val]
  let promises : ZiskFv.EquivCore.Promises.JumpPromises
      state d.toInputs.jalr_input.PC d.toInputs.jalr_input.rd d.toInputs.misa_val
      (PureSpec.execute_JALR_pure d.toInputs.jalr_input).success
      (PureSpec.execute_JALR_pure d.toInputs.jalr_input).nextPC
      d.toClaim.rd (Pilot.execRowOf trace i) e_rd nextPC_val :=
    { input_rd_eq := d.toInputs.h_input_rd
      input_pc_eq := d.toInputs.h_input_pc
      input_misa_eq := d.toInputs.h_input_misa
      misa_c_zero := d.toInputs.h_misa_c
      -- exec artifacts: now `rfl` (`Pilot.execRowOf` is a concrete two-entry list).
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches := h_nextPC_disch
      rd_mult := by rfl
      rd_as := by rfl
      success := d.toInputs.h_success
      nextPC_option := h_nextPC_option
      rd_idx := d.toInputs.h_input_rd.trans
        (eRdLui_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset) }
  have h_link_bridge :=
    jalr_link_bridge_of_decode d.toInputs.h_pc_bridge d.toDecode.h_jmp2 d.toInputs.h_pc_bound
  let env : OpEnvelope state m i.val :=
    OpEnvelope.jalr d.toInputs.jalr_input d.toClaim.imm d.toClaim.rs1 d.toClaim.rd d.toInputs.misa_val d.toInputs.mseccfg (Pilot.execRowOf trace i) e_rd
      nextPC_val next_pc store_pc_mem pins d.toDecode.h_flag d.toDecode.h_m32 d.toDecode.h_set_pc d.toDecode.h_store_pc
      h_jalr_subset promises d.toInputs.h_input_imm d.toInputs.h_input_rs1 d.toInputs.h_cur_privilege d.toInputs.h_mseccfg
      h_link_bridge d.toInputs.h_pc_bound d.toInputs.h_pc_offset_lt_2_32
  have h_bridge : env.aeneasBridgeTrust :=
    ⟨d.toDecode.h_flag, d.toDecode.h_m32, d.toDecode.h_set_pc, d.toDecode.h_store_pc, h_link_bridge⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env :=
    noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-! ## Strengthened store arms (SB/SH/SW/SD, channel-balance form) — OpEnvelope route

CONVERTED from the direct-lift route to the OpEnvelope route: each arm CONSTRUCTS
`OpEnvelope.<store>` from the trace's committed Main row and invokes
`zisk_riscv_compliant_program_bus`, projecting `exec_eq_remaining` (the 12th
conjunct).

The store `OpEnvelope.<store>` constructor carries `{mainRowVar : Var
MainRowWithRom}` / `{mainEnv : Environment}` implicit binders whose `eval mainEnv
mainRowVar` appears in five hypotheses (`h_main_row`/`h_main_spec`/`h_store_pc`/
`h_main_c_match`/`h_addr2`).  We instantiate `mainRowVar := mainConstVar
(mainRowWithRomSt …)` and `mainEnv := emptyEnv`; by `eval_mainConstVar` this
`eval` reduces to the concrete trace row `mainRowWithRomSt trace i`, so the
five hypotheses become exactly the facts `construction_<store>_sound` already
proves (Spec at the row, `store_pc = 0`, the self-referential `c`-emission match,
and the derived `addr2` placement bridge).  This `mainConstVar`-of-the-real-row
pattern is the analogue of the M-ext/control "placeholder-env + real row" build
and sidesteps the prior
whnf BLOWUP (the `Eq.mpr` cast over a free `MainRowWithRom` motive) because the row
is a `.const` literal of the committed trace row, not an opaque eval-binder.

Non-vacuous: `execRow` is a genuine ∀-binder; the `c`-emission match is
`matches_memory_entry_refl` over the real `busSt` row; the high-byte RMW residuals
(`h_m*`, the #76 sub-doubleword preservation reads) are carried verbatim as
`RowData_<store>` binders, NOT laundered. -/

/-- Empty environment used only to instantiate the store `OpEnvelope` arms'
    `{mainEnv}` implicit binder; `eval_mainConstVar` makes the choice irrelevant. -/
private def emptyMainEnv : Environment FGL :=
  { get := fun _ => 0, data := fun _ _ => #[] }

/-- Strengthened `sb` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sb
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sb trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.STORE
        (d.toClaim.sb_input.imm, regidx.Regidx d.toClaim.sb_input.r2, regidx.Regidx d.toClaim.sb_input.r1, 1))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace i (Pilot.execRowOf trace i)).exec_row,
           [ (busSt trace i (Pilot.execRowOf trace i)).e0
           , (busSt trace i (Pilot.execRowOf trace i)).e1
           , (busSt trace i (Pilot.execRowOf trace i)).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace i (Pilot.execRowOf trace i)
  have h_core : (mainRowWithRomSt trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.toClaim.sb_input.r2_val := d.toInputs.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.toClaim.sb_input.r2_val := d.toInputs.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.sb_state_assumptions d.toClaim.sb_input state)
      (PureSpec.execute_STOREB_pure d.toClaim.sb_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sb d.toClaim.sb_input d.toInputs.regs bus pins d.toDecode.h_main_ind_width d.toInputs.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by
        have h_a0_value :
            (mainRowWithRomSt trace i).core.a_0 = lane_lo d.toClaim.sb_input.r1_val := by
          rw [h_core]
          simpa [ZiskFv.AirsClean.Main.rowAt] using d.toInputs.h_a0_value
        simpa only [eval_mainConstVar] using
          store_addr2_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset_imm
            h_a0_value d.toInputs.h_store_addr_bound)
      h_b0' h_b1' d.toInputs.h_m1 d.toInputs.h_m2 d.toInputs.h_m3 d.toInputs.h_m4 d.toInputs.h_m5 d.toInputs.h_m6 d.toInputs.h_m7
  have h_bridge : env.aeneasBridgeTrust := ⟨d.toDecode.h_main_ind_width, h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sh` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sh
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sh trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.STORE
        (d.toClaim.sh_input.imm, regidx.Regidx d.toClaim.sh_input.r2, regidx.Regidx d.toClaim.sh_input.r1, 2))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace i (Pilot.execRowOf trace i)).exec_row,
           [ (busSt trace i (Pilot.execRowOf trace i)).e0
           , (busSt trace i (Pilot.execRowOf trace i)).e1
           , (busSt trace i (Pilot.execRowOf trace i)).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace i (Pilot.execRowOf trace i)
  have h_core : (mainRowWithRomSt trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.toClaim.sh_input.r2_val := d.toInputs.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.toClaim.sh_input.r2_val := d.toInputs.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.sh_state_assumptions d.toClaim.sh_input state)
      (PureSpec.execute_STOREH_pure d.toClaim.sh_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sh d.toClaim.sh_input d.toInputs.regs bus pins d.toDecode.h_main_ind_width d.toInputs.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by
        have h_a0_value :
            (mainRowWithRomSt trace i).core.a_0 = lane_lo d.toClaim.sh_input.r1_val := by
          rw [h_core]
          simpa [ZiskFv.AirsClean.Main.rowAt] using d.toInputs.h_a0_value
        simpa only [eval_mainConstVar] using
          store_addr2_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset_imm
            h_a0_value d.toInputs.h_store_addr_bound)
      h_b0' h_b1' d.toInputs.h_m2 d.toInputs.h_m3 d.toInputs.h_m4 d.toInputs.h_m5 d.toInputs.h_m6 d.toInputs.h_m7
  have h_bridge : env.aeneasBridgeTrust := ⟨d.toDecode.h_main_ind_width, h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sw` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sw
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sw trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.STORE
        (d.toClaim.sw_input.imm, regidx.Regidx d.toClaim.sw_input.r2, regidx.Regidx d.toClaim.sw_input.r1, 4))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace i (Pilot.execRowOf trace i)).exec_row,
           [ (busSt trace i (Pilot.execRowOf trace i)).e0
           , (busSt trace i (Pilot.execRowOf trace i)).e1
           , (busSt trace i (Pilot.execRowOf trace i)).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace i (Pilot.execRowOf trace i)
  have h_core : (mainRowWithRomSt trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.toClaim.sw_input.r2_val := d.toInputs.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.toClaim.sw_input.r2_val := d.toInputs.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.sw_state_assumptions d.toClaim.sw_input state)
      (PureSpec.execute_STOREW_pure d.toClaim.sw_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sw d.toClaim.sw_input d.toInputs.regs bus pins d.toDecode.h_main_ind_width d.toInputs.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by
        have h_a0_value :
            (mainRowWithRomSt trace i).core.a_0 = lane_lo d.toClaim.sw_input.r1_val := by
          rw [h_core]
          simpa [ZiskFv.AirsClean.Main.rowAt] using d.toInputs.h_a0_value
        simpa only [eval_mainConstVar] using
          store_addr2_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset_imm
            h_a0_value d.toInputs.h_store_addr_bound)
      h_b0' h_b1' d.toInputs.h_m4 d.toInputs.h_m5 d.toInputs.h_m6 d.toInputs.h_m7
  have h_bridge : env.aeneasBridgeTrust := ⟨d.toDecode.h_main_ind_width, h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.2.2.2

/-- Strengthened `sd` step (channel-balance form), via the OpEnvelope route. -/
theorem stepStrong_sd
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_sd trace binding i)
    (_h_known : True) :
    execute_instruction (instruction.STORE
        (d.toClaim.sd_input.imm, regidx.Regidx d.toClaim.sd_input.r2, regidx.Regidx d.toClaim.sd_input.r1, 8))
        (binding i)
      = ZiskFv.Channels.state_effect_via_channels
          ⟨(busSt trace i (Pilot.execRowOf trace i)).exec_row,
           [ (busSt trace i (Pilot.execRowOf trace i)).e0
           , (busSt trace i (Pilot.execRowOf trace i)).e1
           , (busSt trace i (Pilot.execRowOf trace i)).e2 ]⟩ (binding i) := by
  set m := ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable with hm
  set state := binding i with hstate
  let bus := busSt trace i (Pilot.execRowOf trace i)
  have h_core : (mainRowWithRomSt trace i).core =
      ZiskFv.AirsClean.Main.rowAt m i.val := mainRowWithRomSt_core trace binding i
  have h_main_spec :
      ZiskFv.AirsClean.Main.Spec (mainRowWithRomSt trace i).core := by
    rw [h_core]; exact mainSpec_at trace binding i
  have h_core_store_pc : (mainRowWithRomSt trace i).core.store_pc = 0 := by
    rw [h_core]; simpa [ZiskFv.AirsClean.Main.rowAt] using d.toDecode.h_store_pc
  let pins : ZiskFv.Compliance.MainRowPins m i.val 0 OP_COPYB :=
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
  have h_main_c_match :
      ZiskFv.Airs.MemoryBus.matches_memory_entry bus.e2
        (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
          (ZiskFv.AirsClean.Main.cMemMessage (mainRowWithRomSt trace i)) 1 2) :=
    ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _
  have h_b0' : m.b_0 i.val = ZiskFv.Trusted.lane_lo d.toClaim.sd_input.r2_val := d.toInputs.h_b0_value
  have h_b1' : m.b_1 i.val = ZiskFv.Trusted.lane_hi d.toClaim.sd_input.r2_val := d.toInputs.h_b1_value
  let promises : ZiskFv.EquivCore.Promises.StorePromises
      state d.toInputs.regs.mstatus d.toInputs.regs.pmaRegion d.toInputs.regs.misa d.toInputs.regs.mseccfg
      (PureSpec.sd_state_assumptions d.toClaim.sd_input state)
      (PureSpec.execute_STORED_pure d.toClaim.sd_input).nextPC
      bus.exec_row bus.e0 bus.e1 bus.e2 :=
    { risc_v_assumptions := d.toInputs.h_risc_v_assumptions
      opcode_assumptions_ := d.toInputs.h_opcode_assumptions
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl }
  let env : OpEnvelope state m i.val :=
    OpEnvelope.sd d.toClaim.sd_input d.toInputs.regs bus pins d.toInputs.h_opcode_assumptions promises
      (mainRowVar := mainConstVar (mainRowWithRomSt trace i)) (mainEnv := emptyMainEnv)
      (by simpa only [eval_mainConstVar] using h_core)
      (by simpa only [eval_mainConstVar] using h_main_spec)
      (by simpa only [eval_mainConstVar] using h_core_store_pc)
      (by simpa only [eval_mainConstVar] using h_main_c_match)
      (by
        have h_a0_value :
            (mainRowWithRomSt trace i).core.a_0 = lane_lo d.toClaim.sd_input.r1_val := by
          rw [h_core]
          simpa [ZiskFv.AirsClean.Main.rowAt] using d.toInputs.h_a0_value
        simpa only [eval_mainConstVar] using
          store_addr2_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset_imm
            h_a0_value d.toInputs.h_store_addr_bound)
      h_b0' h_b1'
  have h_bridge : env.aeneasBridgeTrust := ⟨h_b0', h_b1'⟩
  have h_mem : env.memoryTimelineConstructionEvidence := by trivial
  have h_known : Defects.NoKnownDefect env := noKnownDefect_of_shapes env (fun h => h) (fun h => h) trivial
  exact (zisk_riscv_compliant_program_bus env h_bridge h_mem h_known).2.2.2.2.2.2.2.2.1


end ZiskFv.Compliance
