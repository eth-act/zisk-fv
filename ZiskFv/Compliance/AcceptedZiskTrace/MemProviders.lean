import ZiskFv.Compliance.AcceptedZiskTrace.Spec
import ZiskFv.Compliance.AcceptedZiskTrace.MainTable
import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridges

/-!
# Derived memory-bus provider coverage

Accepted traces derive the full memory-bus provider branch split from
`channels_balanced` plus derived `spec_holds`. The mutable-Mem specialization
keeps the remaining phase-1 residue explicit: callers must rule out the named
non-mutable branches (MemAlign family, Main self-provider, RegisterBoundary).
-/

namespace ZiskFv.Compliance

open Air.Flat
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.Channels.MemoryBus (MemBusChannel)

/-- The accepted trace exposes the full active-Main memory-bus provider branch
    split. The non-Mem branches remain visible in
    `ActiveMainMemProviderRowMatchSpec`; this theorem only derives the branch
    split from accepted trace data. -/
theorem AcceptedZiskTrace.activeMainMemProviderRowMatchSpec_of_active_main_eval
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL} :
    trace.mainTable.component.Spec (trace.mainTable.environment mainRow)
      ∧ ActiveMainMemProviderRowMatchSpec trace.program trace.witness trace.mainTable
        mainRow mainInteraction mainMsg multiplicity as :=
  ZiskFv.AirsClean.FullEnsemble.activeMainMemProviderRowMatchSpec_of_active_main_eval
    trace.witness trace.channels_balanced trace.spec_holds trace.mainTable_mem
    h_mainRow h_mainInteraction h_mainEval h_active

/-- If the caller supplies the narrow syntactic residue excluding the
    non-mutable provider branches, the accepted trace gives the mutable-Mem
    provider branch for the selected active Main memory-bus interaction. -/
theorem AcceptedZiskTrace.activeMainMutableMemProviderRowMatchSpec_of_active_main_eval_no_nonmutable
    {n : Nat} (trace : AcceptedZiskTrace n)
    {mainRow : Array FGL}
    (h_mainRow : mainRow ∈ trace.mainTable.table)
    {mainInteraction : Interaction FGL}
    (h_mainInteraction :
      mainInteraction ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw)
    {mainMult : Expression FGL}
    {mainMsg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL)}
    (h_mainEval :
      mainInteraction =
        ((MemBusChannel.emitted mainMult mainMsg).toRaw).eval
          (trace.mainTable.environment mainRow))
    (h_active : mainInteraction.mult = -1)
    {multiplicity as : FGL}
    (h_no_nonmutable :
      ¬ ActiveMainNonMutableMemProviderRowMatchSpec trace.program trace.witness
        trace.mainTable mainRow mainInteraction mainMsg multiplicity as) :
    trace.mainTable.component.Spec (trace.mainTable.environment mainRow)
      ∧ ActiveMainMutableMemProviderRowMatchSpec trace.program trace.witness trace.mainTable
        mainRow mainInteraction mainMsg multiplicity as := by
  have h_match :=
    trace.activeMainMemProviderRowMatchSpec_of_active_main_eval
      h_mainRow h_mainInteraction h_mainEval h_active
      (multiplicity := multiplicity) (as := as)
  exact ⟨h_match.1,
    activeMainMutableMemProviderRowMatchSpec_of_no_nonmutable
      h_match.2 h_no_nonmutable⟩

end ZiskFv.Compliance
