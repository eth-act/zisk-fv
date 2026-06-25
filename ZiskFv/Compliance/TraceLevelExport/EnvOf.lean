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

/-- The `OpEnvelope.fence` env CONSTRUCTED from a `RowData_fence`.  Both the
    `StepNoKnownDefect` fence obligation AND `stepStrong_fence` reference THIS env,
    so the threaded `NoKnownDefect` obligation is the genuine `NoKnownDefect` of the
    exact env the proof feeds to `zisk_riscv_compliant_program_bus`. -/
noncomputable def fenceEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_fence trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.fence d.fence_input d.fm d.fenceP d.fenceS d.rs d.rd d.exec_row
    ⟨d.h_main_active, d.h_main_op⟩
    { input_pc_eq := d.h_input_pc
      input_priv_eq := d.h_input_priv
      exec_len := d.h_exec_len
      e0_mult := d.h_e0_mult
      e1_mult := d.h_e1_mult
      nextPC_matches := d.h_nextPC_matches }

/-- The `OpEnvelope.mul` env CONSTRUCTED from a `RowData_mul`.  Both the
    `StepNoKnownDefect` mul obligation AND `stepStrong_mul` reference THIS env, so
    the threaded `NoKnownDefect` obligation is the genuine `NoKnownDefect` of the
    exact env the proof feeds to `zisk_riscv_compliant_program_bus`.  (Mirrors
    `fenceEnvOf`: a specific-env obligation, SATISFIABLE for an honest row.) -/
noncomputable def mulEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mul trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.mul d.mul_input d.r1 d.r2 d.rd d.srs1 d.srs2 d.bus d.v d.r_a
    ⟨d.h_main_active, d.h_main_op⟩
    d.h_match_primary d.promises d.arith_mem d.bounds d.h_row_constraints
    d.arith_table d.arith_chunk_ranges d.arith_carry_ranges d.h_rs1_value d.h_rs2_value

/-- **Satisfiability / non-vacuity witness for the threaded MUL obligation.**

    The `StepNoKnownDefect (.mul d)` obligation — `Defects.NoKnownDefect (mulEnvOf
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
        using d.h_not_forge
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
  OpEnvelope.mulh d.mulh_input d.r1 d.r2 d.rd d.bus d.v d.r_a
    ⟨d.h_main_active, d.h_main_op⟩
    d.h_match_secondary d.promises d.arith_mem d.bounds d.h_row_constraints
    d.arith_table d.arith_chunk_ranges d.arith_carry_ranges d.h_rs1_value d.h_rs2_value
    d.h_sign_a d.h_sign_b

/-- The `OpEnvelope.mulhsu` env CONSTRUCTED from a `RowData_mulhsu`.  Only ONE
    sign-range residual `h_sign_a` (op2 unsigned, table-pinned `nb = 0`). -/
noncomputable def mulhsuEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_mulhsu trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.mulhsu d.mulhsu_input d.r1 d.r2 d.rd d.bus d.v d.r_a
    ⟨d.h_main_active, d.h_main_op⟩
    d.h_match_secondary d.promises d.arith_mem d.bounds d.h_row_constraints
    d.arith_table d.arith_chunk_ranges d.arith_carry_ranges d.h_rs1_value d.h_rs2_value
    d.h_sign_a

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
        using d.h_not_forge
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
        using d.h_not_forge
  | arithDivDynamicWitnessSoundness =>
      simp [Defects.Blocks, Defects.ArithDivDynamicWitnessShape, mulhsuEnvOf]
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, mulhsuEnvOf]

/-- The `OpEnvelope.div` env CONSTRUCTED from a `RowData_div`.  Both the
    `StepNoKnownDefect` div obligation AND `stepStrong_div` reference THIS env, so
    the threaded `NoKnownDefect` obligation is the genuine `NoKnownDefect` of the
    exact env the proof feeds to `zisk_riscv_compliant_program_bus`.  (Mirrors
    `mulEnvOf`: a specific-env obligation, SATISFIABLE for an honest signed DIV
    row whose `|r| ≠ |op2|`.) -/
noncomputable def divEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_div trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.div d.div_input d.r1 d.r2 d.rd d.bus d.v d.r_a d.pins
    d.h_match_primary d.promises d.arith_mem d.bounds d.h_row_constraints d.h_boundary
    d.arith_table d.arith_chunk_ranges d.arith_carry_ranges
    d.h_na_bool d.h_nb_bool d.h_nr_bool d.h_np_xor d.h_nr_pin
    d.h_rs1_value d.h_rs2_value d.h_r_le d.h_r_sign

/-- The `OpEnvelope.rem` env CONSTRUCTED from a `RowData_rem` (secondary lane). -/
noncomputable def remEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_rem trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.rem d.rem_input d.r1 d.r2 d.rd d.bus d.v d.r_a d.pins
    d.h_match_secondary d.promises d.arith_mem d.bounds d.h_row_constraints
    d.arith_table d.arith_chunk_ranges d.arith_carry_ranges
    d.h_na_bool d.h_nb_bool d.h_nr_bool d.h_np_xor d.h_nr_pin
    d.h_rs1_value d.h_rs2_value d.h_r_le d.h_r_sign

/-- The `OpEnvelope.divw` env CONSTRUCTED from a `RowData_divw` (W-mode primary). -/
noncomputable def divwEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_divw trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.divw d.divw_input d.r1 d.r2 d.rd d.bus d.v d.r_a d.pins
    d.h_match_primary d.promises d.arith_mem d.bounds
    d.h_row_constraints d.h_boundary d.arith_table d.arith_chunk_ranges d.arith_carry_ranges
    d.h_na_bool d.h_nb_bool d.h_nr_bool d.h_np_xor d.h_nr_pin d.h_m32_v d.h_div_v
    d.h_a23 d.h_b23 d.h_d23 d.h_c23 d.h_byte_lo d.h_sext_choice
    d.h_rs1_value d.h_rs2_value d.h_r_le d.h_r_sign

/-- The `OpEnvelope.remw` env CONSTRUCTED from a `RowData_remw` (W-mode secondary). -/
noncomputable def remwEnvOf
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (d : RowData_remw trace binding i) :
    OpEnvelope (binding i)
      (ZiskFv.AirsClean.FullEnsemble.mainOfTable trace.program trace.mainTable) i.val :=
  OpEnvelope.remw d.remw_input d.r1 d.r2 d.rd d.bus d.v d.r_a d.pins
    d.h_match_secondary d.promises d.arith_mem d.bounds
    d.h_row_constraints d.arith_table d.arith_chunk_ranges d.arith_carry_ranges
    d.h_na_bool d.h_nb_bool d.h_nr_bool d.h_np_xor d.h_nr_pin d.h_m32_v d.h_div_v
    d.h_a23 d.h_b23 d.h_d23 d.h_c23 d.h_byte_lo d.h_sext_choice
    d.h_rs1_value d.h_rs2_value d.h_r_le d.h_r_sign

/-- **Non-vacuity / satisfiability witness for the threaded DIV obligation.**

    The `StepNoKnownDefect (.div d)` obligation — `Defects.NoKnownDefect (divEnvOf
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
        Defects.signedRemainderInt, divEnvOf] using d.h_not_forge
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
      exact d.h_not_forge h_eq
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
        using d.h_not_forge
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
        using d.h_not_forge
  | fenceIncomplete =>
      simp [Defects.Blocks, Defects.FenceKnownGoodShape, remwEnvOf]


end ZiskFv.Compliance
