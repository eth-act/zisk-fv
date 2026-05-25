import ZiskFv.AirsClean.Binary.Constraints
import ZiskFv.AirsClean.Binary.Soundness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Binary Clean Component (Phase C6)

Packages ZisK's Binary AIR as a Clean `Air.Flat.Component`.

The component covers the 7 F-typed constraints and the operation-bus push.
BinaryTable lookup semantics still flow through the existing table-soundness
boundary until the Binary-family terminal phase.
-/

namespace ZiskFv.AirsClean.Binary

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

def circuit : GeneralFormalCircuit FGL BinaryRow unit :=
  { binaryElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h_holds
        exact ⟨ by simpa [sub_eq_add_neg] using h0
              , by simpa [sub_eq_add_neg] using h1
              , by simpa [sub_eq_add_neg] using h2
              , by simpa [sub_eq_add_neg] using h3
              , by simpa [sub_eq_add_neg] using h4
              , by simpa [sub_eq_add_neg] using h5
              , by simpa [sub_eq_add_neg] using h6 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      simpa [sub_eq_add_neg] using h_assumptions }

def component : Air.Flat.Component FGL := ⟨ circuit ⟩

abbrev StaticBinaryTableSpecFacts (row : BinaryRow FGL) : Prop :=
      ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 2 * row.mode.use_first_byte
          op := row.chain.b_op
          a_byte := row.aBytes.free_in_a_0
          b_byte := row.bBytes.free_in_b_0
          cin := 0
          c_byte := row.cBytes.free_in_c_0
          flags := row.chain.carry_0 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 0
          op := row.chain.b_op
          a_byte := row.aBytes.free_in_a_1
          b_byte := row.bBytes.free_in_b_1
          cin := row.chain.carry_0
          c_byte := row.cBytes.free_in_c_1
          flags := row.chain.carry_1 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 0
          op := row.chain.b_op
          a_byte := row.aBytes.free_in_a_2
          b_byte := row.bBytes.free_in_b_2
          cin := row.chain.carry_1
          c_byte := row.cBytes.free_in_c_2
          flags := row.chain.carry_2 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := row.mode.mode32
          op := row.chain.b_op
          a_byte := row.aBytes.free_in_a_3
          b_byte := row.bBytes.free_in_b_3
          cin := row.chain.carry_2
          c_byte := row.cBytes.free_in_c_3
          flags := row.chain.carry_3 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 0
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_4
          b_byte := row.bBytes.free_in_b_4
          cin := row.chain.carry_3
          c_byte := row.cBytes.free_in_c_4
          flags := row.chain.carry_4 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 0
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_5
          b_byte := row.bBytes.free_in_b_5
          cin := row.chain.carry_4
          c_byte := row.cBytes.free_in_c_5
          flags := row.chain.carry_5 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 0
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_6
          b_byte := row.bBytes.free_in_b_6
          cin := row.chain.carry_5
          c_byte := row.cBytes.free_in_c_6
          flags := row.chain.carry_6 }
      ∧ ZiskFv.AirsClean.BinaryTable.binaryTable.Spec
        { pos_ind := 1 - row.mode.mode32
          op := row.chain.b_op_or_sext
          a_byte := row.aBytes.free_in_a_7
          b_byte := row.bBytes.free_in_b_7
          cin := row.chain.carry_6
          c_byte := row.cBytes.free_in_c_7
          flags := row.chain.carry_7 }

def staticLookupCircuit : GeneralFormalCircuit FGL BinaryRow unit :=
  { binaryWithStaticBinaryTableElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (opBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithStaticBinaryTable, main, opBusMessageExpr,
        OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row ∧ StaticBinaryTableSpecFacts row
    ProverAssumptions := fun row _ _ => Spec row ∧ StaticBinaryTableSpecFacts row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
          h_holds
        exact ⟨ ⟨ by simpa [sub_eq_add_neg] using h0
                  , by simpa [sub_eq_add_neg] using h1
                  , by simpa [sub_eq_add_neg] using h2
                  , by simpa [sub_eq_add_neg] using h3
                  , by simpa [sub_eq_add_neg] using h4
                  , by simpa [sub_eq_add_neg] using h5
                  , by simpa [sub_eq_add_neg] using h6 ⟩
              , ⟨ by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h7
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h8
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h9
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h10
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h11
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h12
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h13
                  , by simpa [StaticBinaryTableSpecFacts, sub_eq_add_neg] using h14 ⟩ ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      rcases h_assumptions with ⟨hSpec, hStatic⟩
      rcases hSpec with ⟨h0, h1, h2, h3, h4, h5, h6⟩
      rcases hStatic with ⟨h7, h8, h9, h10, h11, h12, h13, h14⟩
      exact ⟨ by simpa [sub_eq_add_neg] using h0
            , by simpa [sub_eq_add_neg] using h1
            , by simpa [sub_eq_add_neg] using h2
            , by simpa [sub_eq_add_neg] using h3
            , by simpa [sub_eq_add_neg] using h4
            , by simpa [sub_eq_add_neg] using h5
            , by simpa [sub_eq_add_neg] using h6
            , by simpa [sub_eq_add_neg] using h7
            , by simpa [sub_eq_add_neg] using h8
            , by simpa [sub_eq_add_neg] using h9
            , by simpa [sub_eq_add_neg] using h10
            , by simpa [sub_eq_add_neg] using h11
            , by simpa [sub_eq_add_neg] using h12
            , by simpa [sub_eq_add_neg] using h13
            , by simpa [sub_eq_add_neg] using h14 ⟩ }

def staticLookupComponent : Air.Flat.Component FGL := ⟨ staticLookupCircuit ⟩

theorem staticLookupComponent_interactionsWith_opBus :
    staticLookupComponent.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr staticLookupComponent.rowInputVar)).toRaw)]⟩ ∈
    staticLookupComponent.exposedChannels
  simp only [staticLookupComponent, staticLookupCircuit,
    binaryWithStaticBinaryTableElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

theorem staticLookupComponent_spec
    (env : Environment FGL) :
    staticLookupComponent.Spec env =
      (Spec (staticLookupComponent.rowInput env)
        ∧ StaticBinaryTableSpecFacts (staticLookupComponent.rowInput env)) := by
  rfl

theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, binaryElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

theorem spec_via_component (row : BinaryRow FGL)
    (h0 : row.mode.mode32 * (1 + -row.mode.mode32) = 0)
    (h1 : row.chain.carry_7 * (1 + -row.chain.carry_7) = 0)
    (h2 : row.mode.result_is_a * (1 + -row.mode.result_is_a) = 0)
    (h3 : row.mode.use_first_byte * (1 + -row.mode.use_first_byte) = 0)
    (h4 : row.mode.c_is_signed * (1 + -row.mode.c_is_signed) = 0)
    (h5 :
      row.chain.b_op_or_sext
        + -(row.mode.mode32 * (row.mode.c_is_signed + 512 + -row.chain.b_op)
            + row.chain.b_op) = 0)
    (h6 : row.mode.mode32_and_c_is_signed
        + -(row.mode.mode32 * row.mode.c_is_signed) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, binaryElaborated,
    circuit_norm] at hsound
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { aBytes := {
        free_in_a_0 := .const row.aBytes.free_in_a_0
        free_in_a_1 := .const row.aBytes.free_in_a_1
        free_in_a_2 := .const row.aBytes.free_in_a_2
        free_in_a_3 := .const row.aBytes.free_in_a_3
        free_in_a_4 := .const row.aBytes.free_in_a_4
        free_in_a_5 := .const row.aBytes.free_in_a_5
        free_in_a_6 := .const row.aBytes.free_in_a_6
        free_in_a_7 := .const row.aBytes.free_in_a_7 }
      bBytes := {
        free_in_b_0 := .const row.bBytes.free_in_b_0
        free_in_b_1 := .const row.bBytes.free_in_b_1
        free_in_b_2 := .const row.bBytes.free_in_b_2
        free_in_b_3 := .const row.bBytes.free_in_b_3
        free_in_b_4 := .const row.bBytes.free_in_b_4
        free_in_b_5 := .const row.bBytes.free_in_b_5
        free_in_b_6 := .const row.bBytes.free_in_b_6
        free_in_b_7 := .const row.bBytes.free_in_b_7 }
      cBytes := {
        free_in_c_0 := .const row.cBytes.free_in_c_0
        free_in_c_1 := .const row.cBytes.free_in_c_1
        free_in_c_2 := .const row.cBytes.free_in_c_2
        free_in_c_3 := .const row.cBytes.free_in_c_3
        free_in_c_4 := .const row.cBytes.free_in_c_4
        free_in_c_5 := .const row.cBytes.free_in_c_5
        free_in_c_6 := .const row.cBytes.free_in_c_6
        free_in_c_7 := .const row.cBytes.free_in_c_7 }
      chain := {
        carry_0 := .const row.chain.carry_0
        carry_1 := .const row.chain.carry_1
        carry_2 := .const row.chain.carry_2
        carry_3 := .const row.chain.carry_3
        carry_4 := .const row.chain.carry_4
        carry_5 := .const row.chain.carry_5
        carry_6 := .const row.chain.carry_6
        carry_7 := .const row.chain.carry_7
        b_op := .const row.chain.b_op
        b_op_or_sext := .const row.chain.b_op_or_sext }
      mode := {
        mode32 := .const row.mode.mode32
        result_is_a := .const row.mode.result_is_a
        use_first_byte := .const row.mode.use_first_byte
        c_is_signed := .const row.mode.c_is_signed
        mode32_and_c_is_signed := .const row.mode.mode32_and_c_is_signed } }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end ZiskFv.AirsClean.Binary
