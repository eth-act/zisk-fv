import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.Airs.MemoryBus.MemAlignBridge

/-!
# Trace-local MemAlign skippable-prove bridge

This lower-level bridge deliberately does not import `Compliance.Defects`: the
full-ensemble memory-bus route needs the exact selector consequence without a
dependency cycle. `Compliance.Defects.MemAlignSkippableProveForge` mirrors this
shape at the public defect boundary, and the trace-level dispatcher transports
its negation into this route.
-/

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- Route-level form of the #1142 forge: a non-pull, nonzero general-MemAlign
    interaction matched to a Main load entry without the prove-side pins. -/
def MemAlignSkippableProveForge
    {length : Nat} (program : ZiskFv.AirsClean.ZiskInstructionRom.Program length)
    (witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble)
    (entry : Interaction.MemoryBusEntry FGL) : Prop :=
  ∃ providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw,
    providerInteraction.mult ≠ -1
      ∧ providerInteraction.mult ≠ 0
      ∧ ∃ providerTable ∈ witness.allTables,
        providerInteraction ∈ providerTable.interactionsWith MemBusChannel.toRaw
          ∧ ∃ providerRow ∈ providerTable.table,
            providerTable.component.Spec (providerTable.environment providerRow)
              ∧ providerTable.component = ZiskFv.AirsClean.MemAlign.component
              ∧ providerInteraction =
                ((MemBusChannel.emitted
                  (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
                    - ZiskFv.AirsClean.MemAlign.selAssumeExpr
                      ZiskFv.AirsClean.MemAlign.component.rowInputVar)
                  (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                    ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
                  (providerTable.environment providerRow)
              ∧ ∃ multiplicity,
                ZiskFv.Airs.MemoryBus.matches_memory_entry entry
                  (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
                    (Eval.eval (providerTable.environment providerRow)
                      (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
                        ZiskFv.AirsClean.MemAlign.component.rowInputVar))
                    multiplicity 2)
                ∧ ¬ (
                  (Eval.eval (providerTable.environment providerRow)
                    ZiskFv.AirsClean.MemAlign.component.rowInputVar).sel_prove = 1
                  ∧ (Eval.eval (providerTable.environment providerRow)
                    ZiskFv.AirsClean.MemAlign.component.rowInputVar).sel_up_to_down = 0
                  ∧ (Eval.eval (providerTable.environment providerRow)
                    ZiskFv.AirsClean.MemAlign.component.rowInputVar).sel_down_to_up = 0)

/-- Negating the exact route-level forge returns the prove pins needed by the
    general MemAlign load-provider adapter. -/
theorem memAlign_selected_prove_pins_of_not_skippable_prove_forge
    {length : Nat} {program : ZiskFv.AirsClean.ZiskInstructionRom.Program length}
    {witness : EnsembleWitness (fullRv64imEnsemble length program).ensemble}
    {entry : Interaction.MemoryBusEntry FGL}
    (h_not_forge : ¬ MemAlignSkippableProveForge program witness entry)
    {providerInteraction : Interaction FGL}
    (h_providerInteraction : providerInteraction ∈ witness.interactionsWith MemBusChannel.toRaw)
    (h_nonpull : providerInteraction.mult ≠ -1)
    (h_nonzero : providerInteraction.mult ≠ 0)
    {providerTable : Table FGL} (h_providerTable : providerTable ∈ witness.allTables)
    (h_providerTableInteraction : providerInteraction ∈
      providerTable.interactionsWith MemBusChannel.toRaw)
    {providerRow : Array FGL} (h_providerRow : providerRow ∈ providerTable.table)
    (h_spec : providerTable.component.Spec (providerTable.environment providerRow))
    (h_component : providerTable.component = ZiskFv.AirsClean.MemAlign.component)
    (h_providerEval : providerInteraction =
      ((MemBusChannel.emitted
        (ZiskFv.AirsClean.MemAlign.component.rowInputVar.sel_prove
          - ZiskFv.AirsClean.MemAlign.selAssumeExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar)
        (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
          ZiskFv.AirsClean.MemAlign.component.rowInputVar)).toRaw).eval
        (providerTable.environment providerRow))
    {multiplicity : FGL}
    (h_entry : ZiskFv.Airs.MemoryBus.matches_memory_entry entry
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (Eval.eval (providerTable.environment providerRow)
          (ZiskFv.AirsClean.MemAlign.memBusMessageExpr
            ZiskFv.AirsClean.MemAlign.component.rowInputVar))
        multiplicity 2)) :
    (Eval.eval (providerTable.environment providerRow)
      ZiskFv.AirsClean.MemAlign.component.rowInputVar).sel_prove = 1
    ∧ (Eval.eval (providerTable.environment providerRow)
      ZiskFv.AirsClean.MemAlign.component.rowInputVar).sel_up_to_down = 0
    ∧ (Eval.eval (providerTable.environment providerRow)
      ZiskFv.AirsClean.MemAlign.component.rowInputVar).sel_down_to_up = 0 := by
  by_contra h_pins
  apply h_not_forge
  exact ⟨providerInteraction, h_providerInteraction, h_nonpull, h_nonzero,
    providerTable, h_providerTable, h_providerTableInteraction, providerRow,
    h_providerRow, h_spec, h_component, h_providerEval, multiplicity, h_entry, h_pins⟩

end ZiskFv.AirsClean.FullEnsemble
