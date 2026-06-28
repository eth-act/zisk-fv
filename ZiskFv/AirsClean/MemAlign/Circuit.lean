import ZiskFv.AirsClean.MemAlign.Constraints
import ZiskFv.AirsClean.MemAlign.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlign Clean Component

Packages the MemAlign AIR per-row constraints and its unified memory-bus
interaction as a Clean `Air.Flat.Component`.

The channel emission is structural: it adds no new row-level soundness
obligation because `MemBusChannel.Guarantees` is `True`. Cross-row
continuity remains in `CrossRow.lean`.

## Trust note

No axioms. Completeness is a constructibility claim for rows equal to
`memAlignRowOf ...`: a concrete phase, Boolean flags/selectors, registers, and
address fields with `value_0`, `value_1`, `preL1`, and `pc` computed by the
builder. Cross-row continuity remains outside this row-local proof.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- Honest MemAlign phase: prove row, up-to-down transition,
    down-to-up transition, or idle. -/
inductive MemAlignPhase
  | prove
  | upToDown
  | downToUp
  | idle
deriving DecidableEq, Repr

namespace MemAlignPhase

/-- Field selector for the prover row phase. -/
@[simp]
def selProve : MemAlignPhase → FGL
  | prove => 1
  | upToDown => 0
  | downToUp => 0
  | idle => 0

/-- Field selector for the up-to-down transition phase. -/
@[simp]
def selUpToDown : MemAlignPhase → FGL
  | prove => 0
  | upToDown => 1
  | downToUp => 0
  | idle => 0

/-- Field selector for the down-to-up transition phase. -/
@[simp]
def selDownToUp : MemAlignPhase → FGL
  | prove => 0
  | upToDown => 0
  | downToUp => 1
  | idle => 0

end MemAlignPhase

/-- Four-byte lane reconstruction used by the MemAlign honest-row builder. -/
def memAlignLane (r0 r1 r2 r3 : FGL) : FGL :=
  r0 + r1 * 256 + r2 * 65536 + r3 * 16777216

/-- Honest value_0 for MemAlign, computed from phase, selectors, and registers. -/
def memAlignValue0Of (phase : MemAlignPhase)
    (sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7 : Bool)
    (reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7 : FGL) : FGL :=
  phase.selProve *
    (boolF sel_0 * memAlignLane reg_0 reg_1 reg_2 reg_3 +
     boolF sel_1 * memAlignLane reg_1 reg_2 reg_3 reg_4 +
     boolF sel_2 * memAlignLane reg_2 reg_3 reg_4 reg_5 +
     boolF sel_3 * memAlignLane reg_3 reg_4 reg_5 reg_6 +
     boolF sel_4 * memAlignLane reg_4 reg_5 reg_6 reg_7 +
     boolF sel_5 * memAlignLane reg_5 reg_6 reg_7 reg_0 +
     boolF sel_6 * memAlignLane reg_6 reg_7 reg_0 reg_1 +
     boolF sel_7 * memAlignLane reg_7 reg_0 reg_1 reg_2) +
  (phase.selUpToDown + phase.selDownToUp) * memAlignLane reg_0 reg_1 reg_2 reg_3

/-- Honest value_1 for MemAlign, computed from phase, selectors, and registers. -/
def memAlignValue1Of (phase : MemAlignPhase)
    (sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7 : Bool)
    (reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7 : FGL) : FGL :=
  phase.selProve *
    (boolF sel_0 * memAlignLane reg_4 reg_5 reg_6 reg_7 +
     boolF sel_1 * memAlignLane reg_5 reg_6 reg_7 reg_0 +
     boolF sel_2 * memAlignLane reg_6 reg_7 reg_0 reg_1 +
     boolF sel_3 * memAlignLane reg_7 reg_0 reg_1 reg_2 +
     boolF sel_4 * memAlignLane reg_0 reg_1 reg_2 reg_3 +
     boolF sel_5 * memAlignLane reg_1 reg_2 reg_3 reg_4 +
     boolF sel_6 * memAlignLane reg_2 reg_3 reg_4 reg_5 +
     boolF sel_7 * memAlignLane reg_3 reg_4 reg_5 reg_6) +
  (phase.selUpToDown + phase.selDownToUp) * memAlignLane reg_4 reg_5 reg_6 reg_7

/-- Honest row for MemAlign: phase and Boolean flags are encoded as field bits.
    Dependent `pc`, `preL1`, `sel_*`, and `value_*` columns are computed; address
    and register columns outside these equations are supplied by the caller. -/
def memAlignRowOf (phase : MemAlignPhase) (isBoot wr reset : Bool)
    (sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7 : Bool)
    (reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7 : FGL)
    (addr offset width step delta_addr pcVal : FGL) : MemAlignRow FGL :=
  { addr := addr
    offset := offset
    width := width
    wr := boolF wr
    pc := if isBoot then 0 else pcVal
    reset := boolF reset
    sel_up_to_down := phase.selUpToDown
    sel_down_to_up := phase.selDownToUp
    reg_0 := reg_0
    reg_1 := reg_1
    reg_2 := reg_2
    reg_3 := reg_3
    reg_4 := reg_4
    reg_5 := reg_5
    reg_6 := reg_6
    reg_7 := reg_7
    sel_0 := boolF sel_0
    sel_1 := boolF sel_1
    step := step
    sel_2 := boolF sel_2
    sel_3 := boolF sel_3
    sel_4 := boolF sel_4
    sel_5 := boolF sel_5
    sel_6 := boolF sel_6
    sel_7 := boolF sel_7
    sel_prove := phase.selProve
    preL1 := boolF isBoot
    delta_addr := delta_addr
    value_0 := memAlignValue0Of phase sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
      reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7
    value_1 := memAlignValue1Of phase sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
      reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7 }

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
def circuit : GeneralFormalCircuit FGL MemAlignRow unit :=
  { memAlignWithMemBusElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built by `memAlignRowOf`: phase and Boolean
    -- columns are honest, while unconstrained address/register data remains free.
    ProverAssumptions := fun row _ _ =>
      ∃ phase isBoot wr reset sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
        reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7
        addr offset width step delta_addr pcVal,
        row = memAlignRowOf phase isBoot wr reset
          sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
          reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7
          addr offset width step delta_addr pcVal
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
          h12, h13, h14, h15⟩ := h_holds
        exact ⟨ by simpa only [sub_eq_add_neg] using h0
              , by simpa only [sub_eq_add_neg] using h1
              , by simpa only [sub_eq_add_neg] using h2
              , by simpa only [sub_eq_add_neg] using h3
              , by simpa only [sub_eq_add_neg] using h4
              , by simpa only [sub_eq_add_neg] using h5
              , by simpa only [sub_eq_add_neg] using h6
              , by simpa only [sub_eq_add_neg] using h7
              , by simpa only [sub_eq_add_neg] using h8
              , by simpa only [sub_eq_add_neg] using h9
              , by simpa only [sub_eq_add_neg] using h10
              , by simpa only [sub_eq_add_neg] using h11
              , by simpa only [sub_eq_add_neg] using h12
              , by simpa only [sub_eq_add_neg] using h13
              , by simpa only [sub_eq_add_neg] using h14
              , by simpa only [sub_eq_add_neg] using h15 ⟩
      · intro _
        trivial
    completeness := by
      circuit_proof_start_core
      simp only [mainWithMemBus, main, circuit_norm, selAssumeExpr,
        memBusMessageExpr, MemBusChannel]
      obtain ⟨phase, isBoot, wr, reset, sel_0, sel_1, sel_2, sel_3,
        sel_4, sel_5, sel_6, sel_7, reg_0, reg_1, reg_2, reg_3,
        reg_4, reg_5, reg_6, reg_7, addr, offset, width, step,
        delta_addr, pcVal, hrow⟩ := h_assumptions
      rw [hrow] at h_input
      simp only [circuit_norm] at h_input
      injection h_input with h_addr h_offset h_width h_wr h_pc h_reset h_sel_up_to_down
        h_sel_down_to_up h_reg_0 h_reg_1 h_reg_2 h_reg_3 h_reg_4 h_reg_5
        h_reg_6 h_reg_7 h_sel_0 h_sel_1 h_step h_sel_2 h_sel_3 h_sel_4
        h_sel_5 h_sel_6 h_sel_7 h_sel_prove h_preL1 h_delta_addr
        h_value_0 h_value_1
      cases isBoot <;> cases phase <;>
        simp [h_wr, h_pc, h_reset, h_sel_up_to_down, h_sel_down_to_up, h_reg_0,
          h_reg_1, h_reg_2, h_reg_3, h_reg_4, h_reg_5, h_reg_6, h_reg_7, h_sel_0,
          h_sel_1, h_sel_2, h_sel_3, h_sel_4, h_sel_5, h_sel_6, h_sel_7,
          h_sel_prove, h_preL1, h_value_0, h_value_1, memAlignValue0Of,
          memAlignValue1Of, memAlignLane] <;>
        ring_nf <;>
        simp }

def component : Air.Flat.Component FGL := { circuit := circuit }

/-- Project the generic Clean component `Spec` to the concrete MemAlign row
    `Spec`. -/
theorem component_spec (env : Environment FGL) :
    component.Spec env = Spec (component.rowInput env) := by
  rfl

/-- The MemAlign component exposes exactly its one memory-bus interaction. -/
theorem component_interactionsWith_memBus :
    component.operations.interactionsWith MemBusChannel.toRaw =
      [((MemBusChannel.emitted
          (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
          (memBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨MemBusChannel.toRaw,
      [((MemBusChannel.emitted
          (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
          (memBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, memAlignWithMemBusElaborated,
    Component.exposedChannels, expose, List.mem_singleton, List.map_cons,
    List.map_nil]

theorem spec_via_component (row : MemAlignRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  exact h_constraints

end ZiskFv.AirsClean.MemAlign
