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
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBinding
import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl

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

theorem busSub_rd_idx_of_decode
    {numInstructions : Nat}
    {trace : AcceptedZiskTrace numInstructions}
    {i : Fin trace.numInstructions}
    {execRow : List (Interaction.ExecutionBusEntry FGL)}
    {rd : regidx}
    (h_store_ind : (mainRowWithRomSub trace i).rom.store_ind = 0)
    (h_store_offset :
      (mainRowWithRomSub trace i).rom.store_offset =
        Transpiler.ind (regidx_to_fin rd)) :
    regidx_to_fin rd =
      Transpiler.wrap_to_regidx (busSub trace i execRow).e2.ptr := by
  have h_spec := RomDecodeBinding.mainAddressSpec_at trace ⟨i.val, trace.mainTable_index i⟩
  have h_addr2 := h_spec.2.2.1
  rw [busSub, ZiskFv.AirsClean.Main.cMemMessage,
    ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry]
  rw [h_addr2, h_store_offset, h_store_ind]
  simp [Transpiler.wrap_to_regidx_ind]

/-- The `OpEnvelope.fence` env CONSTRUCTED from a `RowData_fence`.  Both the
    `RowOutsideDefectRegion` fence obligation AND `stepStrong_fence` reference THIS env,
    so the threaded `NoKnownDefect` obligation is the genuine `NoKnownDefect` of the
    exact env the proof feeds to `zisk_riscv_compliant_program_bus`. -/
noncomputable def fenceEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_fence trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.fence d.toInputs.fence_input d.toClaim.fm d.toClaim.fenceP d.toClaim.fenceS d.toClaim.rs d.toClaim.rd (Pilot.execRowOf trace i)
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    { input_pc_eq := d.toInputs.h_input_pc
      input_priv_eq := d.toInputs.h_input_priv
      exec_len := by rfl
      e0_mult := by rfl
      e1_mult := by rfl
      nextPC_matches :=
        Pilot.sequential_nextPC_discharged trace i _ d.toDecode.h_idx
          d.toDecode.h_set_pc d.toDecode.h_jmp1 d.toDecode.h_jmp2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound }

/-- The `OpEnvelope.mul` env CONSTRUCTED from a `RowData_mul`.  Both the
    `RowOutsideDefectRegion` mul obligation AND `stepStrong_mul` reference THIS env, so
    the threaded `NoKnownDefect` obligation is the genuine `NoKnownDefect` of the
    exact env the proof feeds to `zisk_riscv_compliant_program_bus`.  (Mirrors
    `fenceEnvOf`: a specific-env obligation, SATISFIABLE for an honest row.) -/
noncomputable def mulEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.mul d.toInputs.mul_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd d.toClaim.srs1 d.toClaim.srs2 bus d.toInputs.v d.toInputs.r_a
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    d.toInputs.h_match_primary
    -- #100: DERIVE the bundled `nextPC_matches` from the in-circuit transition
    -- certificate (kernel-only `sequential_nextPC_discharged`) and re-attach it to
    -- the 14 caller-supplied value/data promises. MUL's Sail nextPC = PC + 4#64.
    (d.toInputs.promises.withNextPC (PureSpec.execute_MULH_mul_pure d.toInputs.mul_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.mul_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges d.toInputs.h_rs1_value d.toInputs.h_rs2_value

/-- **Satisfiability / non-vacuity witness for the threaded MUL obligation.**

    The `RowOutsideDefectRegion (.mul d)` obligation — `Defects.NoKnownDefect (mulEnvOf
    …)` — is DISCHARGED from `RowData_mul.h_not_forge` (the honest product-sign
    shape).  Concretely: for the `.mul` env, the arith-div defect predicate is
    `False` and the FENCE defect predicate's negation is `True`, while the
    arith-mul defect predicate is exactly the two exceptional product-sign shapes
    that `h_not_forge` rules out.  Hence the threaded obligation is SATISFIABLE for
    every honest MUL row, so the `.mul` arm of `root_soundness`
    is NON-VACUOUS (it is not discharged by a contradictory binder).  This lemma is
    the Lean-checked anti-vacuity guard for the strong-export MUL arm. -/
theorem mul_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i) :
    Defects.NoKnownDefect (mulEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simpa [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, mulEnvOf]
        using d.toInputs.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulEnvOf]
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulEnvOf]

/-- The `OpEnvelope.mulh` env CONSTRUCTED from a `RowData_mulh`.  Mirrors
    `mulEnvOf`: a specific-env obligation, SATISFIABLE for an honest signed MULH
    row.  Carries the SIGN-RANGE RESIDUAL `h_sign_a`/`h_sign_b`. -/
noncomputable def mulhEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.mulh d.toInputs.mulh_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (MULH Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_MULH_mulh_pure d.toInputs.mulh_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.mulh_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges d.toInputs.h_rs1_value d.toInputs.h_rs2_value
    d.toInputs.h_sign_a d.toInputs.h_sign_b

/-- The `OpEnvelope.mulhsu` env CONSTRUCTED from a `RowData_mulhsu`.  Only ONE
    sign-range residual `h_sign_a` (op2 unsigned, table-pinned `nb = 0`). -/
noncomputable def mulhsuEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.mulhsu d.toInputs.mulhsu_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a
    ⟨d.toDecode.h_main_active, d.toDecode.h_main_op⟩
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (MULHSU Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_MULH_mulhsu_pure d.toInputs.mulhsu_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.mulhsu_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges d.toInputs.h_rs1_value d.toInputs.h_rs2_value
    d.toInputs.h_sign_a

/-- **Non-vacuity / satisfiability witness for the threaded MULH obligation.**
    For an honest MULH row, `h_not_forge` rules out the two exceptional shapes the
    narrowed `MaliciousSignedMulWitnessShape` admits for op 181, so
    `NoKnownDefect (mulhEnvOf …)` is TRUE — the `.mulh` strong arm is NON-VACUOUS. -/
theorem mulh_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i) :
    Defects.NoKnownDefect (mulhEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simpa [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, mulhEnvOf]
        using d.toInputs.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulhEnvOf]
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulhEnvOf]

/-- Satisfiability witness for the threaded MULHSU obligation (companion of
    `mulh_noKnownDefect_of_rowData`). -/
theorem mulhsu_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i) :
    Defects.NoKnownDefect (mulhsuEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simpa [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, mulhsuEnvOf]
        using d.toInputs.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulhsuEnvOf]
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulhsuEnvOf]

/-- The `OpEnvelope.div` env CONSTRUCTED from a `RowData_div`.  Both the
    `RowOutsideDefectRegion` div obligation AND `stepStrong_div` reference THIS env, so
    the threaded `NoKnownDefect` obligation is the genuine `NoKnownDefect` of the
    exact env the proof feeds to `zisk_riscv_compliant_program_bus`.  (Mirrors
    `mulEnvOf`: a specific-env obligation, SATISFIABLE for an honest signed DIV
    row whose `|r| ≠ |op2|`.) -/
noncomputable def divEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_div trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.div d.toInputs.div_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_primary
    -- #100: DERIVE the bundled `nextPC_matches` (DIV Sail nextPC = PC + 4#64); see `mulEnvOf`.
    -- The DivRemForge value-defect gate is untouched.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_div_pure d.toInputs.div_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.div_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints d.toInputs.h_boundary
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- The `OpEnvelope.rem` env CONSTRUCTED from a `RowData_rem` (secondary lane). -/
noncomputable def remEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.rem d.toInputs.rem_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (REM Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_rem_pure d.toInputs.rem_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.rem_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds d.toInputs.h_row_constraints
    d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- The `OpEnvelope.divw` env CONSTRUCTED from a `RowData_divw` (W-mode primary). -/
noncomputable def divwEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.divw d.toInputs.divw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_primary
    -- #100: DERIVE the bundled `nextPC_matches` (DIVW Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_divw_pure d.toInputs.divw_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.divw_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds
    d.toInputs.h_row_constraints d.toInputs.h_boundary d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin d.toInputs.h_m32_v d.toInputs.h_div_v
    d.toInputs.h_a23 d.toInputs.h_b23 d.toInputs.h_d23 d.toInputs.h_c23 d.toInputs.h_byte_lo d.toInputs.h_sext_choice
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- The `OpEnvelope.remw` env CONSTRUCTED from a `RowData_remw` (W-mode secondary). -/
noncomputable def remwEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  let bus := busSub trace i (Pilot.execRowOf trace i)
  OpEnvelope.remw d.toInputs.remw_input d.toClaim.r1 d.toClaim.r2 d.toClaim.rd bus d.toInputs.v d.toInputs.r_a d.toDecode.pins
    d.toInputs.h_match_secondary
    -- #100: DERIVE the bundled `nextPC_matches` (REMW Sail nextPC = PC + 4#64); see `mulEnvOf`.
    (d.toInputs.promises.withNextPC (PureSpec.execute_DIVREM_remw_pure d.toInputs.remw_input).nextPC
      (by
        exact Pilot.sequential_nextPC_discharged trace i d.toInputs.remw_input.PC
          d.toDecode.h_idx d.toDecode.h_set_pc d.toDecode.h_jmp_offset1 d.toDecode.h_jmp_offset2
          d.toInputs.h_pc_bridge d.toInputs.h_pc_bound)
      (d.toInputs.promises.input_rd_eq.trans
        (busSub_rd_idx_of_decode d.toDecode.h_store_ind d.toDecode.h_store_offset)))
    d.toDecode.arith_mem d.toDecode.bounds
    d.toInputs.h_row_constraints d.toInputs.arith_table d.toInputs.arith_chunk_ranges d.toInputs.arith_carry_ranges
    d.toInputs.h_na_bool d.toInputs.h_nb_bool d.toInputs.h_nr_bool d.toInputs.h_np_xor d.toInputs.h_nr_pin d.toInputs.h_m32_v d.toInputs.h_div_v
    d.toInputs.h_a23 d.toInputs.h_b23 d.toInputs.h_d23 d.toInputs.h_c23 d.toInputs.h_byte_lo d.toInputs.h_sext_choice
    d.toInputs.h_rs1_value d.toInputs.h_rs2_value d.toInputs.h_r_le d.toInputs.h_r_sign

/-- **Non-vacuity / satisfiability witness for the threaded DIV obligation.**

    The `RowOutsideDefectRegion (.div d)` obligation — `Defects.NoKnownDefect (divEnvOf
    …)` — is DISCHARGED from `RowData_div.h_not_forge` (the narrowed honest shape
    nonzero-divisor `|r| ≠ |op2|` shape).  Concretely: for the `.div` env the
    arith-MUL defect predicate is `False` (not a mul env) and the FENCE defect
    predicate's negation is `True`, while the arith-DIV defect predicate is exactly
    the nonzero-divisor `|r| = |op2|` false-positive forge that `h_not_forge` rules
    out.  Hence the threaded obligation is SATISFIABLE for honest signed DIV rows,
    including divisor-zero rows handled by the boundary constraints.  This is the
    Lean-checked anti-vacuity guard for the strong-export DIV arm. -/
theorem div_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_div trace binding i) :
    Defects.NoKnownDefect (divEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, divEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simpa [Defects.Blocks, Defects.ArithDivDynamicWitnessShape,
        Defects.signedRemainderInt, divEnvOf] using d.toInputs.h_not_forge
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, divEnvOf]

/-- Satisfiability witness for the threaded REM obligation (companion of
    `div_noKnownDefect_of_rowData`; secondary remainder lane). -/
theorem rem_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i) :
    Defects.NoKnownDefect (remEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, remEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape,
        Defects.signedRemainderInt, remEnvOf]
      intro _ h_eq
      exact d.toInputs.h_not_forge h_eq
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, remEnvOf]

/-- Satisfiability witness for the threaded DIVW obligation (W-mode analogue of
    `div_noKnownDefect_of_rowData`; narrowed shape `|r₃₂| ≠ |op2₃₂|`). -/
theorem divw_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i) :
    Defects.NoKnownDefect (divwEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, divwEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simpa [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, divwEnvOf]
        using d.toInputs.h_not_forge
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, divwEnvOf]

/-- Satisfiability witness for the threaded REMW obligation (companion of
    `divw_noKnownDefect_of_rowData`; W-mode secondary remainder lane). -/
theorem remw_noKnownDefect_of_rowData
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i) :
    Defects.NoKnownDefect (remwEnvOf trace binding i d) := by
  intro id
  cases id with
  | arithMulSignedWitnessSoundness =>
      simp [Defects.Blocks, Defects.MaliciousSignedMulWitnessShape, remwEnvOf]
  | arithDivDynamicWitnessSoundness =>
      simpa [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, remwEnvOf]
        using d.toInputs.h_not_forge
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, remwEnvOf]

/-! ### Bridge lemmas: row-data forge predicates ≡ OpEnvelope defect shapes

Each bridge is `Iff.rfl`: the row-data predicate (over the `Inputs_<op>` arith
witness / `Claim_<op>` fields) and the `OpEnvelope`-based defect shape at the
corresponding `<op>EnvOf` env are DEFINITIONALLY the same proposition.  These are
the faithfulness audit for the `RowOutsideDefectRegion` re-expression (plan step B):
they witness that lifting the three known-defect conditions off `OpEnvelope`
onto the row data changed no meaning — the `Iff.rfl` proofs would fail if the
re-expressed predicate were even slightly weaker or stronger than the original
`OpEnvelope` shape. -/

theorem signedMulForge_iff_mulShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i) :
    Defects.SignedMulForge d.toInputs.v d.toInputs.r_a
      ↔ Defects.MaliciousSignedMulWitnessShape (mulEnvOf trace binding i d) := Iff.rfl

theorem signedMulForge_iff_mulhShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulh trace binding i) :
    Defects.SignedMulForge d.toInputs.v d.toInputs.r_a
      ↔ Defects.MaliciousSignedMulWitnessShape (mulhEnvOf trace binding i d) := Iff.rfl

theorem signedMulForge_iff_mulhsuShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i) :
    Defects.SignedMulForge d.toInputs.v d.toInputs.r_a
      ↔ Defects.MaliciousSignedMulWitnessShape (mulhsuEnvOf trace binding i d) := Iff.rfl

theorem divRemForge_iff_divShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_div trace binding i) :
    Defects.DivRemForge d.toInputs.div_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (divEnvOf trace binding i d) := Iff.rfl

theorem divRemForge_iff_remShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i) :
    Defects.DivRemForge d.toInputs.rem_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (remEnvOf trace binding i d) := Iff.rfl

theorem divRemForgeW_iff_divwShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i) :
    Defects.DivRemForgeW d.toInputs.divw_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (divwEnvOf trace binding i d) := Iff.rfl

theorem divRemForgeW_iff_remwShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i) :
    Defects.DivRemForgeW d.toInputs.remw_input.r2_val d.toInputs.v d.toInputs.r_a
      ↔ Defects.ArithDivDynamicWitnessShape (remwEnvOf trace binding i d) := Iff.rfl

theorem fenceKnownGood_iff_fenceShape
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_fence trace binding i) :
    Defects.FenceKnownGood d.toClaim.fm d.toClaim.rs d.toClaim.rd
      ↔ Defects.FenceKnownGoodShape (fenceEnvOf trace binding i d) := Iff.rfl


end ZiskFv.Compliance
