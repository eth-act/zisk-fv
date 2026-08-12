import Clean.Air.FlatComponent
import Clean.Utils.Tactics
import ZiskFv.AirsClean.RangeTables
import ZiskFv.Channels.SpecifiedRanges

/-!
# `SpecifiedRanges` bus-102 static provider slice — the register-step descent

The source-linked, bounded provider for Main's three register-step range hints
(`main.pil:333-335`). Like `SpecifiedRangesSlice` (bus 103, 16-bit) this is deliberately a slice,
not a claim to extract the whole virtual `SpecifiedRanges` AIR: its membership predicate is the
exact constructive `rangeTable24` model and its range id is the manifest's bus 102.

## Why this slice exists — it is load-bearing, not decorative

`main.pil:333-335` range-checks `<slot>_mem_step - <slot>_reg_prev_mem_step - 1` into `[0,
MAX_RANGE]` with `MAX_RANGE = (1 << 24) - 1`, for the a, b and store register slots. That is the
**strict descent** on the register-access timestamp chain.

Without it, `<slot>_reg_prev_mem_step` is a free witness column that nothing constrains — its only
other use is as the `timestamp` of `aRegPreMessageExpr` and its siblings. Balance alone then admits
a forged trace. A Main row's register-pre push and its memory pull carry the *same* value lanes,
and the pull's timestamp is pinned (`1 + main_step * 4`, with `main_step = i` from
`MainStepIndexFixedFacts.main_step_eq_index`) while the push's is free. So for two rows `A`, `B`
touching one register, setting `a_reg_prev_mem_step_A := ts_B` and `a_reg_prev_mem_step_B := ts_A`
with a common arbitrary value makes `A`'s pull match `B`'s push and vice versa — a closed 2-cycle
that never touches `RegisterBoundary.bootMessage`. Every interaction is matched,
`BalancedChannels` holds, and both rows read a value nothing ever wrote.

The descent kills exactly that: a cycle would have to be strictly decreasing.

This is the #169/#19 range-fidelity axis. Modelling the check is a trust **narrowing** — it adds a
constraint the real circuit has and our model was missing, so the set of accepted traces shrinks
toward the real one.
-/

namespace ZiskFv.AirsClean.RegisterStepRangeSlice

open Goldilocks
open Air.Flat
open Circuit (lookup)
open ZiskFv.AirsClean.RangeTables
open ZiskFv.Channels.SpecifiedRanges

/-- The provider's static lookup is the exact 24-bit range table. -/
@[circuit_norm]
def main (value : Expression FGL) : Circuit FGL Unit := do
  lookup (Table.fromStatic rangeTable24) value
  RegisterStepRangeChannel.push (registerStepMessage value)

/-- The bounded provider derives its own static membership; it carries no caller-supplied
assumption. -/
def circuit : GeneralFormalCircuit FGL field unit where
  name := "SpecifiedRangesSlice102"
  main := main
  channelsWithRequirements := [RegisterStepRangeChannel.toRaw]
  exposedChannels value _ :=
    expose RegisterStepRangeChannel
      [RegisterStepRangeChannel.pushed (registerStepMessage value)]
  Assumptions := fun _ _ => True
  Spec := fun value _ _ => rangeTable24.Spec value
  ProverAssumptions := fun value _ _ => rangeTable24.Spec value
  ProverSpec := fun _ _ _ => True
  soundness := by
    circuit_proof_start
    refine ⟨?_, ?_⟩
    · simpa only [Table.fromStatic, StaticTable.toTable, rangeTable24,
        rangeStaticTable] using h_holds
    · intro _
      simpa [RegisterStepRangeChannel, registerStepMessage,
        registerStepRangeId] using h_holds
  completeness := by
    circuit_proof_start [Lookup.completeness_def]
    simpa only [Table.fromStatic, StaticTable.toTable, rangeTable24,
      rangeStaticTable] using h_assumptions

/-- The bus-102 provider component for the full ensemble. -/
def component : Component FGL := { circuit }

theorem component_interactionsWith_rangeChannel :
    component.operations.interactionsWith RegisterStepRangeChannel.toRaw =
      [((RegisterStepRangeChannel.pushed
        (registerStepMessage component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨RegisterStepRangeChannel.toRaw,
      [((RegisterStepRangeChannel.pushed
        (registerStepMessage component.rowInputVar)).toRaw)]⟩ ∈ component.exposedChannels
  simp only [component, circuit, Component.exposedChannels, expose,
    List.mem_singleton, List.map_cons, List.map_nil]

end ZiskFv.AirsClean.RegisterStepRangeSlice
