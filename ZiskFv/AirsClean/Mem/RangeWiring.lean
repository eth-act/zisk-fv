import Extraction.LookupWiring
import Clean.Air.Balance
import ZiskFv.AirsClean.RangeTables
import ZiskFv.AirsClean.Mem.SidecarColumns
import ZiskFv.AirsClean.Mem.GeneratedTransition
import ZiskFv.Channels.SpecifiedRanges

/-!
# Source-linked Mem range wiring

The generated `LookupWiring` links validate the PIL hint tuple against the
extracted accumulator constraint. This module is the small live-model bridge:
it associates only those validated links with the Mem table cells and their
canonical `ProverData` keys. It carries no proof premise and does not assert
range membership; balance plus the static provider supplies that in PR 2b.
-/

namespace ZiskFv.AirsClean.Mem

open Goldilocks
open Extraction.LookupWiring
open ZiskFv.Channels.SpecifiedRanges

structure MemRangeWiring where
  link : ValidatedLink
  rawColumn : Nat
  proverDataKey : String
  source : Expression FGL

@[reducible]
def distanceBase0Wiring : MemRangeWiring :=
  ⟨link_Mem_29, MemRangeSidecarRawColumn.distanceBase0,
    MemRawSidecarDataKey.Segment.distanceBase0, memDistanceBase0Expr⟩

@[reducible]
def distanceBase1Wiring : MemRangeWiring :=
  ⟨link_Mem_30, MemRangeSidecarRawColumn.distanceBase1,
    MemRawSidecarDataKey.Segment.distanceBase1, memDistanceBase1Expr⟩

@[reducible]
def distanceEnd0Wiring : MemRangeWiring :=
  ⟨link_Mem_31, MemRangeSidecarRawColumn.distanceEnd0,
    MemRawSidecarDataKey.Segment.distanceEnd0, memDistanceEnd0Expr⟩

@[reducible]
def distanceEnd1Wiring : MemRangeWiring :=
  ⟨link_Mem_32, MemRangeSidecarRawColumn.distanceEnd1,
    MemRawSidecarDataKey.Segment.distanceEnd1, memDistanceEnd1Expr⟩

@[reducible]
def memRangeWirings : List MemRangeWiring :=
  [distanceBase0Wiring, distanceBase1Wiring, distanceEnd0Wiring, distanceEnd1Wiring]

/-- The only live range emissions are the four constraint-validated links,
materialized at their canonical table-resident raw cells. -/
@[reducible]
def rangeMessages : List (SpecifiedRangeMessage (Expression FGL)) :=
  memRangeWirings.map (fun wiring => memDistanceMessage wiring.source)

/-- c29 is the kernel-checked direct-template link for `distance_base[0]`. -/
theorem distanceBase0Wiring_link : distanceBase0Wiring.link = link_Mem_29 := rfl

/-- c30 is the kernel-checked direct-template link for `distance_base[1]`. -/
theorem distanceBase1Wiring_link : distanceBase1Wiring.link = link_Mem_30 := rfl

/-- c31 is the kernel-checked direct-template link for `distance_end[0]`. -/
theorem distanceEnd0Wiring_link : distanceEnd0Wiring.link = link_Mem_31 := rfl

/-- c32 is the kernel-checked direct-template link for `distance_end[1]`. -/
theorem distanceEnd1Wiring_link : distanceEnd1Wiring.link = link_Mem_32 := rfl

/-! ## Concrete provider-balance demonstration -/

/-- One table's shared prover data supplies the c29 range value. -/
def distanceBase0DemoData : ProverData FGL := fun key width =>
  if key = MemRawSidecarDataKey.Segment.distanceBase0 then
    match width with
    | 1 => #[![7]]
    | _ => #[]
  else #[]

@[reducible]
def distanceBase0DemoRow : MemRow FGL :=
  { addr := 0, step := 0, sel := 0, addr_changes := 0, step_dual := 0, sel_dual := 0
    value_0 := 0, value_1 := 0, wr := 0, previous_step := 0, increment_0 := 0
    increment_1 := 0, read_same_addr := 0 }

@[reducible]
def distanceBase0DemoEnvironment : Environment FGL :=
  Environment.fromArray
    (memFixedColumns.materialize 0
      (memRawRowWithProverData distanceBase0DemoData distanceBase0DemoRow))
    distanceBase0DemoData

@[reducible]
def distanceBase0DemoValue : FGL :=
  Expression.eval distanceBase0DemoEnvironment distanceBase0Wiring.source

theorem distanceBase0DemoValue_eq : distanceBase0DemoValue = 7 := by
  rw [show distanceBase0Wiring.source = memDistanceBase0Expr by rfl,
    eval_memDistanceBase0Expr_materialize]
  simp [distanceBase0DemoData, proverDataScalar, proverDataColumn]

@[reducible]
def distanceBase0DemoMessage : SpecifiedRangeMessage FGL :=
  memDistanceMessage distanceBase0DemoValue

@[reducible]
def distanceBase0DemoInteractions : List (Interaction FGL) :=
  [ SpecifiedRangesSliceChannel.pulledValue distanceBase0DemoMessage
  , SpecifiedRangesSliceChannel.pushedValue distanceBase0DemoMessage ]

private theorem distanceBase0DemoProviderMembership :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec distanceBase0DemoValue := by
  rw [distanceBase0DemoValue_eq]
  norm_num [ZiskFv.AirsClean.RangeTables.rangeTable16,
    ZiskFv.AirsClean.RangeTables.rangeStaticTable]

private theorem distanceBase0DemoInteractions_balanced :
    BalancedInteractions distanceBase0DemoInteractions := by
  refine balancedInteractions_of_present ?_
    [(toElements distanceBase0DemoMessage).toArray] ?_ ?_
  · left
    rw [show ringChar FGL = GL_prime from ringChar.eq FGL GL_prime]
    decide
  · intro interaction h_interaction
    simp [distanceBase0DemoInteractions] at h_interaction
    rcases h_interaction with rfl | rfl <;> rfl
  · intro msg h_msg
    simp only [List.mem_singleton] at h_msg
    subst msg
    simp [distanceBase0DemoInteractions, balanceOf]

private theorem distanceBase0DemoInteractions_requirements :
    ∀ interaction ∈ distanceBase0DemoInteractions,
      interaction.channel = SpecifiedRangesSliceChannel.toRaw ∧
        interaction.Requirements distanceBase0DemoData := by
  intro interaction h_interaction
  simp [distanceBase0DemoInteractions] at h_interaction
  rcases h_interaction with rfl | rfl
  · constructor
    · rfl
    · simp [Interaction.Requirements, Channel.toRaw]
  · constructor
    · rfl
    · simpa [Interaction.Requirements, Channel.toRaw, distanceBase0DemoMessage,
        memDistanceMessage] using distanceBase0DemoProviderMembership

/-- PR 2a's exit demonstration: a value from the selected Mem table's
`ProverData` is pulled on the c29-linked channel, balanced by the bus-103
static provider, and derives its 16-bit membership through Clean consistency. -/
theorem distanceBase0Demo_membership_from_balance :
    ZiskFv.AirsClean.RangeTables.rangeTable16.Spec distanceBase0DemoValue := by
  have h_guarantees := RawChannel.Consistent.consistent
    distanceBase0DemoInteractions distanceBase0DemoData
    distanceBase0DemoInteractions_balanced distanceBase0DemoInteractions_requirements
  have h_pull := h_guarantees
    (SpecifiedRangesSliceChannel.pulledValue distanceBase0DemoMessage) (by
      simp [distanceBase0DemoInteractions])
  simpa [Interaction.Guarantees, Channel.toRaw, distanceBase0DemoMessage,
    memDistanceMessage] using h_pull

end ZiskFv.AirsClean.Mem
