import ZiskFv.AirsClean.BinaryExtension.Bridge
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Lookup-aware BinaryExtension Clean component

Static-table variant of the BinaryExtension component. The plain
`BinaryExtension.component` exposes only the operation-bus provider row because
the AIR has no F-only local assertions. This component uses
`mainWithStaticBinaryExtensionTable`, so its `Spec` records the eight decoded
BinaryExtensionTable memberships for the same row that provides the op-bus
message.
-/

namespace ZiskFv.AirsClean.BinaryExtension

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

abbrev StaticBinaryExtensionTableSpecFacts
    (row : BinaryExtensionRow FGL) : Prop :=
      ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 0
          a_byte := row.aCols.free_in_a_0
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsLo.free_in_c_0
          c_hi_byte := row.cColsLo.free_in_c_1
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 1
          a_byte := row.aCols.free_in_a_1
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsLo.free_in_c_2
          c_hi_byte := row.cColsLo.free_in_c_3
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 2
          a_byte := row.aCols.free_in_a_2
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsLo.free_in_c_4
          c_hi_byte := row.cColsLo.free_in_c_5
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 3
          a_byte := row.aCols.free_in_a_3
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsLo.free_in_c_6
          c_hi_byte := row.cColsLo.free_in_c_7
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 4
          a_byte := row.aCols.free_in_a_4
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsHi.free_in_c_8
          c_hi_byte := row.cColsHi.free_in_c_9
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 5
          a_byte := row.aCols.free_in_a_5
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsHi.free_in_c_10
          c_hi_byte := row.cColsHi.free_in_c_11
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 6
          a_byte := row.aCols.free_in_a_6
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsHi.free_in_c_12
          c_hi_byte := row.cColsHi.free_in_c_13
          op_is_shift := row.flags.op_is_shift }
    ∧ ZiskFv.AirsClean.BinaryExtensionTable.binaryExtensionTable.Spec
        { op := row.flags.op
          byte_index := 7
          a_byte := row.aCols.free_in_a_7
          shift_amount := row.flags.free_in_b
          c_lo_byte := row.cColsHi.free_in_c_14
          c_hi_byte := row.cColsHi.free_in_c_15
          op_is_shift := row.flags.op_is_shift }

def staticLookupCircuit : GeneralFormalCircuit FGL BinaryExtensionRow unit :=
  { binaryExtensionWithStaticTableElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithStaticBinaryExtensionTable, main,
        opBusMessageExpr, aLo, aHi, OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row ∧ StaticBinaryExtensionTableSpecFacts row
    ProverAssumptions := fun row _ _ =>
      Spec row ∧ StaticBinaryExtensionTableSpecFacts row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h_holds
        exact ⟨
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h0,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h1,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h2,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h3,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h4,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h5,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h6,
          by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h7 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      rcases h_assumptions with
        ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨ by simpa [sub_eq_add_neg] using h0
            , by simpa [sub_eq_add_neg] using h1
            , by simpa [sub_eq_add_neg] using h2
            , by simpa [sub_eq_add_neg] using h3
            , by simpa [sub_eq_add_neg] using h4
            , by simpa [sub_eq_add_neg] using h5
            , by simpa [sub_eq_add_neg] using h6
            , by simpa [sub_eq_add_neg] using h7 ⟩ }

def shiftStaticLookupCircuit : GeneralFormalCircuit FGL BinaryExtensionRow unit :=
  { binaryExtensionWithStaticTableAndShiftRangeElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithStaticBinaryExtensionTableAndShiftRange,
        mainWithStaticBinaryExtensionTable, main, opBusMessageExpr, aLo, aHi,
        OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ =>
      Spec row ∧ StaticBinaryExtensionTableSpecFacts row ∧ ShiftB0RangeSpecFact row
    ProverAssumptions := fun row _ _ =>
      Spec row ∧ StaticBinaryExtensionTableSpecFacts row ∧ ShiftB0RangeSpecFact row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h_b0⟩ := h_holds
        exact ⟨
          ⟨ by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h0,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h1,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h2,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h3,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h4,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h5,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h6,
            by simpa [StaticBinaryExtensionTableSpecFacts, sub_eq_add_neg] using h7 ⟩,
          by simpa [ShiftB0RangeSpecFact] using h_b0 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      rcases h_assumptions with ⟨h_static, h_b0⟩
      rcases h_static with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨ by simpa [sub_eq_add_neg] using h0
            , by simpa [sub_eq_add_neg] using h1
            , by simpa [sub_eq_add_neg] using h2
            , by simpa [sub_eq_add_neg] using h3
            , by simpa [sub_eq_add_neg] using h4
            , by simpa [sub_eq_add_neg] using h5
            , by simpa [sub_eq_add_neg] using h6
            , by simpa [sub_eq_add_neg] using h7
            , by simpa [ShiftB0RangeSpecFact] using h_b0 ⟩ }

def staticLookupComponent : Air.Flat.Component FGL := ⟨ staticLookupCircuit ⟩

def shiftStaticLookupComponent : Air.Flat.Component FGL := ⟨ shiftStaticLookupCircuit ⟩

theorem staticLookupComponent_interactionsWith_opBus :
    staticLookupComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)]⟩ ∈
    staticLookupComponent.exposedChannels
  simp only [staticLookupComponent, staticLookupCircuit,
    binaryExtensionWithStaticTableElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

theorem shiftStaticLookupComponent_interactionsWith_opBus :
    shiftStaticLookupComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr shiftStaticLookupComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed
        (opBusMessageExpr shiftStaticLookupComponent.rowInputVar)).toRaw)]⟩ ∈
    shiftStaticLookupComponent.exposedChannels
  simp only [shiftStaticLookupComponent, shiftStaticLookupCircuit,
    binaryExtensionWithStaticTableAndShiftRangeElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

theorem staticLookupComponent_spec
    (env : Environment FGL) :
    staticLookupComponent.Spec env =
      (Spec (staticLookupComponent.rowInput env)
        ∧ StaticBinaryExtensionTableSpecFacts
          (staticLookupComponent.rowInput env)) := by
  rfl

theorem shiftStaticLookupComponent_spec
    (env : Environment FGL) :
    shiftStaticLookupComponent.Spec env =
      (Spec (shiftStaticLookupComponent.rowInput env)
        ∧ StaticBinaryExtensionTableSpecFacts
          (shiftStaticLookupComponent.rowInput env)
        ∧ ShiftB0RangeSpecFact
          (shiftStaticLookupComponent.rowInput env)) := by
  rfl

theorem static_table_wf_facts_of_spec_facts
    (row : BinaryExtensionRow FGL)
    (h_specs : StaticBinaryExtensionTableSpecFacts row) :
    StaticBinaryExtensionTableWfFacts row := by
  rcases h_specs with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨ ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h0
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h1
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h2
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h3
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h4
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h5
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h6
        , ZiskFv.AirsClean.BinaryExtensionTable.spec_wf_properties h7 ⟩

theorem static_table_op_val_ne_bitwise_of_spec_facts
    (row : BinaryExtensionRow FGL)
    (h_specs : StaticBinaryExtensionTableSpecFacts row) :
    row.flags.op.val ≠ 14 ∧ row.flags.op.val ≠ 15 ∧ row.flags.op.val ≠ 16 := by
  exact ZiskFv.AirsClean.BinaryExtensionTable.spec_op_val_ne_bitwise h_specs.1

/-- A row accepted by the lookup-aware BinaryExtension component cannot carry
    Binary-table bitwise opcodes (`AND`/`OR`/`XOR`, values 14/15/16). -/
theorem staticLookupComponent_op_val_ne_bitwise_of_spec
    (env : Environment FGL)
    (h_spec : staticLookupComponent.Spec env) :
    (staticLookupComponent.rowInput env).flags.op.val ≠ 14
      ∧ (staticLookupComponent.rowInput env).flags.op.val ≠ 15
      ∧ (staticLookupComponent.rowInput env).flags.op.val ≠ 16 := by
  rw [staticLookupComponent_spec] at h_spec
  exact static_table_op_val_ne_bitwise_of_spec_facts
    (staticLookupComponent.rowInput env) h_spec.2

theorem flags_eval_op
    (env : Environment FGL) (flags : BinaryExtensionFlags (Expression FGL)) :
    (eval env flags).op = Expression.eval env flags.op := by
  rw [ProvableStruct.eval_eq_eval]
  cases flags
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go, ProvableType.eval_field]

theorem row_eval_flags_op
    (env : Environment FGL) (row : Var BinaryExtensionRow FGL) :
    (eval env row).flags.op = Expression.eval env row.flags.op := by
  rw [ProvableStruct.eval_eq_eval]
  cases row
  simp only [ProvableStruct.eval, ProvableStruct.fromComponents,
    ProvableStruct.components, ProvableStruct.toComponents,
    ProvableStruct.eval.go]
  exact flags_eval_op env _

/-- Evaluating the static BinaryExtension op-bus expression preserves the
    row's opcode slot. Kept local to avoid unfolding the full row expression
    in Binary-family balance proofs. -/
theorem staticLookupComponent_eval_opBusMessageExpr_op
    (env : Environment FGL) :
    (eval env (opBusMessageExpr staticLookupComponent.rowInputVar)).op =
      (staticLookupComponent.rowInput env).flags.op := by
  rw [ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
  change Expression.eval env staticLookupComponent.rowInputVar.flags.op =
    (staticLookupComponent.rowInput env).flags.op
  rw [← row_eval_flags_op env staticLookupComponent.rowInputVar]
  exact congrArg (fun row : BinaryExtensionRow FGL => row.flags.op)
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset staticLookupComponent.Input 0 env))

theorem shiftStaticLookupComponent_eval_opBusMessageExpr_op
    (env : Environment FGL) :
    (eval env (opBusMessageExpr shiftStaticLookupComponent.rowInputVar)).op =
      (shiftStaticLookupComponent.rowInput env).flags.op := by
  rw [ZiskFv.Channels.OperationBus.OpBusMessage.eval_op]
  change Expression.eval env shiftStaticLookupComponent.rowInputVar.flags.op =
    (shiftStaticLookupComponent.rowInput env).flags.op
  rw [← row_eval_flags_op env shiftStaticLookupComponent.rowInputVar]
  exact congrArg (fun row : BinaryExtensionRow FGL => row.flags.op)
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset shiftStaticLookupComponent.Input 0 env))

end ZiskFv.AirsClean.BinaryExtension
