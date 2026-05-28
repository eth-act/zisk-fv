import ZiskFv.AirsClean.Main.Constraints
import ZiskFv.AirsClean.Main.Soundness
import ZiskFv.AirsClean.Main.Bridge
import ZiskFv.AirsClean.Completeness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# Main Clean Component

Packages the Main AIR's per-row constraints plus its assume-side operation-bus
emission as a Clean `Air.Flat.Component`.

The base `Constraints.main` definition remains the extracted nine F-typed
constraints. This component uses `mainWithOpBus`, which appends the
PIL-faithful operation-bus emission with multiplicity `-is_external_op`.

## Trust note

No axioms.
-/

namespace ZiskFv.AirsClean.Main

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

def circuit : GeneralFormalCircuit FGL MainRow unit :=
  { mainWithOpBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    ProverAssumptions := fun row _ _ => Spec row
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h_holds
        exact ⟨ by simpa [sub_eq_add_neg] using h0
              , by simpa [sub_eq_add_neg] using h1
              , by simpa [sub_eq_add_neg] using h2
              , by simpa [sub_eq_add_neg] using h3
              , by simpa [sub_eq_add_neg] using h4
              , by simpa [sub_eq_add_neg] using h5
              , by simpa [sub_eq_add_neg] using h6
              , by simpa [sub_eq_add_neg] using h7
              , by simpa [sub_eq_add_neg] using h8 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel]
      simpa [sub_eq_add_neg] using h_assumptions }

def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-! ## T4.1 — Main with ROM + memory-bus consumer emissions -/

/-- The extra boolean obligations introduced by `mainWithRom`, beyond the
    original nine Main constraints. These are not part of Main's per-row
    soundness `Spec`; a future honest-prover completeness project may consume
    them separately. -/
@[reducible]
def RomBoolSpec (row : MainRowWithRom FGL) : Prop :=
  row.core.m32 * (1 - row.core.m32) = 0
  ∧ row.core.set_pc * (1 - row.core.set_pc) = 0
  ∧ row.core.store_pc * (1 - row.core.store_pc) = 0
  ∧ row.rom.a_src_imm * (1 - row.rom.a_src_imm) = 0
  ∧ row.rom.a_src_mem * (1 - row.rom.a_src_mem) = 0
  ∧ row.rom.is_precompiled * (1 - row.rom.is_precompiled) = 0
  ∧ row.rom.b_src_imm * (1 - row.rom.b_src_imm) = 0
  ∧ row.rom.b_src_mem * (1 - row.rom.b_src_mem) = 0
  ∧ row.rom.store_mem * (1 - row.rom.store_mem) = 0
  ∧ row.rom.store_ind * (1 - row.rom.store_ind) = 0
  ∧ row.rom.b_src_ind * (1 - row.rom.b_src_ind) = 0
  ∧ row.rom.a_src_reg * (1 - row.rom.a_src_reg) = 0
  ∧ row.rom.b_src_reg * (1 - row.rom.b_src_reg) = 0
  ∧ row.rom.store_reg * (1 - row.rom.store_reg) = 0

/-- Soundness-only wrapper for Main plus ROM lookup plus memory-bus consumer
    emissions. Clean's `GeneralFormalCircuit` also requires a completeness
    proof; that honest-prover side is intentionally not claimed here yet. -/
theorem mainWithRomAndMemBus_soundness (length : ℕ) (program : Program length) :
    GeneralFormalCircuit.Soundness FGL
      (mainWithRomAndMemBusElaborated length program)
      (fun _ _ => True)
      (fun row _ _ => Spec row.core) := by
  circuit_proof_start
  refine ⟨?_, ?_⟩
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, _h_m32, _h_set_pc,
      _h_store_pc, _h_a_src_imm, _h_a_src_mem, _h_is_precompiled,
      _h_b_src_imm, _h_b_src_mem, _h_store_mem, _h_store_ind, _h_b_src_ind,
      _h_a_src_reg, _h_b_src_reg, _h_store_reg, _h_rom⟩ := h_holds
    exact ⟨ by simpa [sub_eq_add_neg] using h0
          , by simpa [sub_eq_add_neg] using h1
          , by simpa [sub_eq_add_neg] using h2
          , by simpa [sub_eq_add_neg] using h3
          , by simpa [sub_eq_add_neg] using h4
          , by simpa [sub_eq_add_neg] using h5
          , by simpa [sub_eq_add_neg] using h6
          , by simpa [sub_eq_add_neg] using h7
          , by simpa [sub_eq_add_neg] using h8 ⟩
  · simp only [MemBusChannel, circuit_norm]

/-! ### Structural ROM projections for T4

These lemmas expose obligations already asserted by
`mainWithRomAndMemBus`. They are intentionally narrower than a
"well-formed program" promise: the ROM lookup conclusion is exact
membership in the program-parameterised `romStaticTable`, and the boolean
facts are only the per-row flag boolean assertions present in `main.pil`.
-/

theorem romBoolSpec_of_mainWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomAndMemBus length program row).operations offset)) :
    env (row.core.m32 * (1 - row.core.m32)) = 0
  ∧ env (row.core.set_pc * (1 - row.core.set_pc)) = 0
  ∧ env (row.core.store_pc * (1 - row.core.store_pc)) = 0
  ∧ env (row.rom.a_src_imm * (1 - row.rom.a_src_imm)) = 0
  ∧ env (row.rom.a_src_mem * (1 - row.rom.a_src_mem)) = 0
  ∧ env (row.rom.is_precompiled * (1 - row.rom.is_precompiled)) = 0
  ∧ env (row.rom.b_src_imm * (1 - row.rom.b_src_imm)) = 0
  ∧ env (row.rom.b_src_mem * (1 - row.rom.b_src_mem)) = 0
  ∧ env (row.rom.store_mem * (1 - row.rom.store_mem)) = 0
  ∧ env (row.rom.store_ind * (1 - row.rom.store_ind)) = 0
  ∧ env (row.rom.b_src_ind * (1 - row.rom.b_src_ind)) = 0
  ∧ env (row.rom.a_src_reg * (1 - row.rom.a_src_reg)) = 0
  ∧ env (row.rom.b_src_reg * (1 - row.rom.b_src_reg)) = 0
  ∧ env (row.rom.store_reg * (1 - row.rom.store_reg)) = 0 := by
  simp only [mainWithRomAndMemBus, mainWithRom, main, circuit_norm] at h_holds
  exact ⟨ h_holds.1 (row.core.m32 * (1 - row.core.m32)) (by simp)
        , h_holds.1 (row.core.set_pc * (1 - row.core.set_pc)) (by simp)
        , h_holds.1 (row.core.store_pc * (1 - row.core.store_pc)) (by simp)
        , h_holds.1 (row.rom.a_src_imm * (1 - row.rom.a_src_imm)) (by simp)
        , h_holds.1 (row.rom.a_src_mem * (1 - row.rom.a_src_mem)) (by simp)
        , h_holds.1 (row.rom.is_precompiled * (1 - row.rom.is_precompiled)) (by simp)
        , h_holds.1 (row.rom.b_src_imm * (1 - row.rom.b_src_imm)) (by simp)
        , h_holds.1 (row.rom.b_src_mem * (1 - row.rom.b_src_mem)) (by simp)
        , h_holds.1 (row.rom.store_mem * (1 - row.rom.store_mem)) (by simp)
        , h_holds.1 (row.rom.store_ind * (1 - row.rom.store_ind)) (by simp)
        , h_holds.1 (row.rom.b_src_ind * (1 - row.rom.b_src_ind)) (by simp)
        , h_holds.1 (row.rom.a_src_reg * (1 - row.rom.a_src_reg)) (by simp)
        , h_holds.1 (row.rom.b_src_reg * (1 - row.rom.b_src_reg)) (by simp)
        , h_holds.1 (row.rom.store_reg * (1 - row.rom.store_reg)) (by simp) ⟩

/-- Main as a Clean `GeneralFormalCircuit` exposing the ROM lookup and
    the 3 memory-bus consumer emissions. Soundness comes from
    `mainWithRomAndMemBus_soundness`; completeness is the declared
    completeness-direction axiom
    `mainWithRomAndMemBus_circuit_completeness` (per plan policy:
    zisk-fv is soundness-only; the axiom is in the tolerated allowlist
    until T4.4 wires this Component through the global theorem). -/
def circuitWithRomAndMemBus
    (length : ℕ) (program : Program length) :
    GeneralFormalCircuit FGL MainRowWithRom unit :=
  { mainWithRomAndMemBusElaborated length program with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row.core
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := mainWithRomAndMemBus_soundness length program
    completeness :=
      ZiskFv.AirsClean.Main.mainWithRomAndMemBus_circuit_completeness length program }

/-- Main as a Clean `Air.Flat.Component` exposing the ROM lookup and
    the 3 memory-bus consumer interactions. Used by the T4.1
    memory-family ensemble. -/
def componentWithRomAndMemBus
    (length : ℕ) (program : Program length) :
    Air.Flat.Component FGL :=
  ⟨ circuitWithRomAndMemBus length program ⟩

/-! ### Unified Main component for the full T7 ensemble -/

/-- Soundness wrapper for the unified Main component. The added
    operation-bus emission is an exposed channel interaction, not a new
    Main constraint; the row-local Main/ROM/memory soundness is inherited
    from `mainWithRomAndMemBus_soundness`. -/
theorem mainWithRomMemAndOpBus_soundness (length : ℕ) (program : Program length) :
    GeneralFormalCircuit.Soundness FGL
      (mainWithRomMemAndOpBusElaborated length program)
      (fun _ _ => True)
      (fun row _ _ => Spec row.core) := by
  intro offset env input_var input h_input h_assumptions h_holds
  have h_mem :
      ConstraintsHold.Soundness env
        ((mainWithRomAndMemBus length program input_var).operations offset) := by
    simpa [mainWithRomMemAndOpBus, circuit_norm] using h_holds
  have h_sound :=
    mainWithRomAndMemBus_soundness length program
      offset env input_var input h_input h_assumptions h_mem
  simpa [mainWithRomMemAndOpBus, circuit_norm, OpBusChannel, MemBusChannel] using h_sound

/-- Main as one Clean `GeneralFormalCircuit` exposing both Main channel
    surfaces from the same `MainRowWithRom`: the operation-bus consumer
    interaction and the ROM/memory-bus consumer interactions. -/
def circuitWithRomMemAndOpBus
    (length : ℕ) (program : Program length) :
    GeneralFormalCircuit FGL MainRowWithRom unit :=
  { mainWithRomMemAndOpBusElaborated length program with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row.core
    ProverAssumptions := fun _ _ _ => True
    ProverSpec := fun _ _ _ => True
    soundness := mainWithRomMemAndOpBus_soundness length program
    completeness := by
      intro offset env input_var h_env input h_input h_assumptions
      have h_mem_env :
          env.UsesLocalWitnessesCompleteness offset
            ((mainWithRomAndMemBus length program input_var).operations offset) := by
        simp [mainWithRomMemAndOpBus, circuit_norm] at h_env ⊢
      have h_mem :=
        ZiskFv.AirsClean.Main.mainWithRomAndMemBus_circuit_completeness
          length program offset env input_var h_mem_env input h_input h_assumptions
      simpa [mainWithRomMemAndOpBus, circuit_norm, OpBusChannel, MemBusChannel] using h_mem }

/-- Unified Main component used by the T7 full ensemble. -/
def componentWithRomMemAndOpBus
    (length : ℕ) (program : Program length) :
    Air.Flat.Component FGL :=
  ⟨ circuitWithRomMemAndOpBus length program ⟩

/-- Project the generic Clean component `Spec` for the unified
    ROM/memory/op-bus Main component to the concrete Main-row `Spec`. -/
theorem componentWithRomMemAndOpBus_spec
    (length : ℕ) (program : Program length) (env : Environment FGL) :
    (componentWithRomMemAndOpBus length program).Spec env =
      Spec ((componentWithRomMemAndOpBus length program).rowInput env).core := by
  rfl

theorem componentWithRomMemAndOpBus_interactionsWith_memBus
    (length : ℕ) (program : Program length) :
    (componentWithRomMemAndOpBus length program).operations.interactionsWith
        MemBusChannel.toRaw =
      [ ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [ ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomMemAndOpBus length program).rowInputVar.rom.store_mem
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_ind
              + (componentWithRomMemAndOpBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar)).toRaw) ]⟩ ∈
    (componentWithRomMemAndOpBus length program).exposedChannels
  simp [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
    mainWithRomMemAndOpBusElaborated, Component.exposedChannels, expose,
    List.map_cons, List.map_nil]

theorem componentWithRomMemAndOpBus_interactionsWith_opBus
    (length : ℕ) (program : Program length) :
    (componentWithRomMemAndOpBus length program).operations.interactionsWith
        OpBusChannel.toRaw =
      [((OpBusChannel.emitted
          (-(componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)
          (opBusMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar.core)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.emitted
          (-(componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)
          (opBusMessageExpr (componentWithRomMemAndOpBus length program).rowInputVar.core)).toRaw)]⟩ ∈
    (componentWithRomMemAndOpBus length program).exposedChannels
  simp [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
    mainWithRomMemAndOpBusElaborated, Component.exposedChannels, expose,
    List.map_cons, List.map_nil]

theorem is_external_op_boolean_of_mainWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (row : Var MainRowWithRom FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds :
      Operations.ConstraintsHold env
        ((mainWithRomMemAndOpBus length program row).operations offset)) :
    env (row.core.is_external_op * (1 - row.core.is_external_op)) = 0 := by
  simp only [mainWithRomMemAndOpBus, mainWithRomAndMemBus, mainWithRom,
    main, circuit_norm] at h_holds
  exact h_holds.1 (row.core.is_external_op * (1 - row.core.is_external_op))
    (Or.inr (Or.inl rfl))

theorem is_external_op_boolean_of_componentWithRomMemAndOpBus_constraints
    (length : ℕ) (program : Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomMemAndOpBus length program).operations.ConstraintsHold env) :
    env ((componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op
        * (1 - (componentWithRomMemAndOpBus length program).rowInputVar.core.is_external_op)) = 0 := by
  have h_row :
      (componentWithRomMemAndOpBus length program).rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff
      (component := componentWithRomMemAndOpBus length program) env).mp h_holds
  exact is_external_op_boolean_of_mainWithRomMemAndOpBus_constraints
    length program
    (componentWithRomMemAndOpBus length program).rowInputVar
    (componentWithRomMemAndOpBus length program).rowOffset env (by
      simpa only [componentWithRomMemAndOpBus, circuitWithRomMemAndOpBus,
        Component.rowOperations] using h_row)

theorem romBoolSpec_of_componentWithRomAndMemBus_constraints
    (length : ℕ) (program : Program length)
    (env : Environment FGL)
    (h_holds :
      (componentWithRomAndMemBus length program).operations.ConstraintsHold env) :
    env ((componentWithRomAndMemBus length program).rowInputVar.core.m32
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.core.m32)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.core.set_pc
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.core.set_pc)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.core.store_pc
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.core.store_pc)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_imm
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_imm)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.is_precompiled
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.is_precompiled)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_imm
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_imm)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.store_mem)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.store_ind)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg)) = 0
  ∧ env ((componentWithRomAndMemBus length program).rowInputVar.rom.store_reg
        * (1 - (componentWithRomAndMemBus length program).rowInputVar.rom.store_reg)) = 0 := by
  have h_row :
      (componentWithRomAndMemBus length program).rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff
      (component := componentWithRomAndMemBus length program) env).mp h_holds
  exact romBoolSpec_of_mainWithRomAndMemBus_constraints
    length program
    (componentWithRomAndMemBus length program).rowInputVar
    (componentWithRomAndMemBus length program).rowOffset env (by
      simpa only [componentWithRomAndMemBus, circuitWithRomAndMemBus,
        Component.rowOperations] using h_row)

theorem componentWithRomAndMemBus_interactionsWith_memBus
    (length : ℕ) (program : Program length) :
    (componentWithRomAndMemBus length program).operations.interactionsWith
        MemBusChannel.toRaw =
      [ ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [ ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.a_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.a_src_reg))
            (aMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.b_src_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.b_src_reg))
            (bMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw)
      , ((MemBusChannel.emitted
            (-((componentWithRomAndMemBus length program).rowInputVar.rom.store_mem
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_ind
              + (componentWithRomAndMemBus length program).rowInputVar.rom.store_reg))
            (cMemMessageExpr (componentWithRomAndMemBus length program).rowInputVar)).toRaw) ]⟩ ∈
    (componentWithRomAndMemBus length program).exposedChannels
  simp only [componentWithRomAndMemBus, circuitWithRomAndMemBus,
    mainWithRomAndMemBusElaborated, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

theorem component_eval_opBusMessageExpr
    (env : Environment FGL) :
    eval env (opBusMessageExpr component.rowInputVar) =
      opBusMessage (component.rowInput env) := by
  rw [eval_opBusMessageExpr]
  exact congrArg opBusMessage
    (by
      simpa only [Air.Flat.Component.rowInput, Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env))

/-- The Main component exposes exactly its one operation-bus interaction.
    This keeps later C7 balance projections from unfolding the nine local
    constraints just to recover the channel message. -/
theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.emitted (-component.rowInputVar.is_external_op)
          (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.emitted (-component.rowInputVar.is_external_op)
          (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, mainWithOpBusElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

/-- Project the `is_external_op` boolean assertion from the concrete
    `mainWithOpBus` operations without unfolding the whole Component `Spec`.

This is the local Main-side fact C7 needs to prove that Main op-bus
interactions have only multiplicity `-1` or `0`. -/
theorem is_external_op_boolean_of_mainWithOpBus_constraints
    (row : Var MainRow FGL) (offset : ℕ) (env : Environment FGL)
    (h_holds : Operations.ConstraintsHold env ((mainWithOpBus row).operations offset)) :
    env (row.is_external_op * (1 - row.is_external_op)) = 0 := by
  simp only [mainWithOpBus, main, circuit_norm] at h_holds
  exact h_holds (row.is_external_op * (1 - row.is_external_op)) (Or.inr (Or.inl rfl))

/-- Component-level adapter for the Main `is_external_op` boolean assertion.

This is the Clean-flat idiom: first project `component.operations` to the
per-row `rowOperations` via `Component.constraintsHold_iff`, then unfold only
the local Main component wrapper. -/
theorem is_external_op_boolean_of_component_constraints
    (env : Environment FGL)
    (h_holds : component.operations.ConstraintsHold env) :
    env (component.rowInputVar.is_external_op * (1 - component.rowInputVar.is_external_op)) = 0 := by
  have h_row : component.rowOperations.ConstraintsHold env :=
    (Component.constraintsHold_iff (component := component) env).mp h_holds
  exact is_external_op_boolean_of_mainWithOpBus_constraints
    component.rowInputVar component.rowOffset env (by
      simpa only [component, circuit, Component.rowOperations] using h_row)

theorem spec_via_component (row : MainRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  exact h_constraints

end ZiskFv.AirsClean.Main
