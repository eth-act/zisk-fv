import ZiskFv.AirsClean.MemAlign.Constraints
import ZiskFv.AirsClean.MemAlign.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# MemAlign Clean Component

Packages the MemAlign AIR per-row constraints, intrinsic D1/D3 source
transitions, and its unified memory/ROM/range interactions as a Clean
`Air.Flat.Component`.

The channel emissions are structural: their consumer guarantees are `True`.
Exact ROM and byte-range membership is supplied by their static providers and
finished-channel balance, not by the consumer or caller.

## Trust note

No axioms. Completeness is a constructibility claim for rows equal to
`memAlignRowOf ...`: a concrete phase, Boolean flags/selectors, registers, and
address fields with `value_0`, `value_1`, `preL1`, and `pc` computed by the
builder. Source predecessor/successor constraints are separately certified
by the component-owned D1/D3 accepted-trace predicates.
-/

namespace ZiskFv.AirsClean.MemAlign

open Goldilocks
open Air.Flat
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.MemAlignRom (MemAlignRomChannel)
open ZiskFv.Channels.MemAlignRanges (MemAlignRangeChannel)

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
    (addr offset width step delta_addr delta_pc pcVal : FGL) : MemAlignRow FGL :=
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
    delta_pc := delta_pc
    value_0 := memAlignValue0Of phase sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
      reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7
    value_1 := memAlignValue1Of phase sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
      reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7 }

/-- A concrete source-shaped padding/idle row.  All eight bytes are zero,
    `reset` is asserted, and the row is closed under both source transition
    families.  This is the non-vacuous base case for the strengthened
    component's honest-row construction; arbitrary real trace rows use the
    same `memAlignRowOf` builder with their source-provided adjacent values. -/
def memAlignIdleRow : MemAlignRow FGL :=
  memAlignRowOf .idle true false true
    false false false false false false false false
    0 0 0 0 0 0 0 0
    0 0 0 0 0 0 0

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4000000 in
def circuit : GeneralFormalCircuit FGL MemAlignRow unit where
    name := "MemAlignWithMemBusAndMemAlignRomAndRanges"
    main := mainWithMemBusAndMemAlignRomAndRanges
    channelsWithRequirements := [MemBusChannel.toRaw, MemAlignRomChannel.toRaw,
      MemAlignRangeChannel.toRaw]
    exposedChannels row _ :=
      expose MemBusChannel
        [MemBusChannel.emitted (row.sel_prove - selAssumeExpr row) (memBusMessageExpr row)] ++
      expose MemAlignRomChannel
        [MemAlignRomChannel.emitted (-1) (memAlignRomMessageExpr row)] ++
      expose MemAlignRangeChannel
        [ MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_0)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_1)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_2)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_3)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_4)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_5)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_6)
        , MemAlignRangeChannel.emitted (-1) (memAlignRangeMessageExpr row.reg_7) ]
    -- Three `expose` blocks appended, so `exposedChannelsLawful_expose` cannot
    -- fire on the whole list; split the membership first.
    exposedChannels_eq := by
      intro input offset exposed h_mem
      simp only [expose, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at h_mem
      rcases h_mem with rfl | rfl | rfl <;>
        simp [circuit_norm, mainWithMemBusAndMemAlignRomAndRanges, mainWithMemBus, main,
          selAssumeExpr, memBusMessageExpr, memAlignRomMessageExpr, memAlignRomFlagsExpr,
          memAlignRangeMessageExpr, MemBusChannel, MemAlignRomChannel, MemAlignRangeChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers rows built by `memAlignRowOf`: phase and Boolean
    -- columns are honest, while unconstrained address/register data remains free.
    ProverAssumptions := fun row _ _ =>
      ∃ phase isBoot wr reset sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
        reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7
        addr offset width step delta_addr delta_pc pcVal,
        row = memAlignRowOf phase isBoot wr reset
          sel_0 sel_1 sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
          reg_0 reg_1 reg_2 reg_3 reg_4 reg_5 reg_6 reg_7
          addr offset width step delta_addr delta_pc pcVal
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
        simp [MemBusChannel]
    completeness := by
      circuit_proof_start_core
      simp only [mainWithMemBusAndMemAlignRomAndRanges, mainWithMemBus, main, circuit_norm,
        selAssumeExpr, memBusMessageExpr, memAlignRomMessageExpr, memAlignRomFlagsExpr,
        memAlignRangeMessageExpr, MemBusChannel,
        ZiskFv.Channels.MemAlignRom.MemAlignRomChannel,
        ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel]
      obtain ⟨phase, isBoot, wr, reset, sel_0, sel_1, sel_2, sel_3,
        sel_4, sel_5, sel_6, sel_7, reg_0, reg_1, reg_2, reg_3,
        reg_4, reg_5, reg_6, reg_7, addr, offset, width, step,
        delta_addr, delta_pc, pcVal, hrow⟩ := h_assumptions
      rw [hrow] at h_input
      simp only [circuit_norm] at h_input
      injection h_input with h_addr h_offset h_width h_wr h_pc h_reset h_sel_up_to_down
        h_sel_down_to_up h_reg_0 h_reg_1 h_reg_2 h_reg_3 h_reg_4 h_reg_5
        h_reg_6 h_reg_7 h_sel_0 h_sel_1 h_step h_sel_2 h_sel_3 h_sel_4
        h_sel_5 h_sel_6 h_sel_7 h_sel_prove h_preL1 h_delta_addr h_delta_pc
        h_value_0 h_value_1
      cases isBoot <;> cases phase <;>
        simp [h_wr, h_pc, h_reset, h_sel_up_to_down, h_sel_down_to_up, h_reg_0,
          h_reg_1, h_reg_2, h_reg_3, h_reg_4, h_reg_5, h_reg_6, h_reg_7, h_sel_0,
          h_sel_1, h_sel_2, h_sel_3, h_sel_4, h_sel_5, h_sel_6, h_sel_7,
          h_sel_prove, h_preL1, h_value_0, h_value_1, memAlignValue0Of,
          memAlignValue1Of, memAlignLane] <;>
        ring_nf <;>
        simp

/-- The source's predecessor/current MemAlign constraints: c29's gated
    `delta_addr` relation and c1/c3/.../c15's register continuity.

    This is the exact `mem_align.pil:116-117,142` / extracted c1/c29 spelling.
    D1's saturated row zero is sound here only because the source's own
    `(1 - reset)` gate remains part of c29; no boundary condition is supplied
    by a caller. -/
def rowInputOfEnvironment (environment : Environment FGL) : MemAlignRow FGL :=
  valueFromOffset MemAlignRow 0 environment

def transitionRows (previous current : MemAlignRow FGL) : Prop :=
  current.delta_addr - (current.addr - previous.addr) * (1 - current.reset) = 0
  ∧ (previous.reg_0 - current.reg_0) * current.sel_0 * current.sel_down_to_up = 0
  ∧ (previous.reg_1 - current.reg_1) * current.sel_1 * current.sel_down_to_up = 0
  ∧ (previous.reg_2 - current.reg_2) * current.sel_2 * current.sel_down_to_up = 0
  ∧ (previous.reg_3 - current.reg_3) * current.sel_3 * current.sel_down_to_up = 0
  ∧ (previous.reg_4 - current.reg_4) * current.sel_4 * current.sel_down_to_up = 0
  ∧ (previous.reg_5 - current.reg_5) * current.sel_5 * current.sel_down_to_up = 0
  ∧ (previous.reg_6 - current.reg_6) * current.sel_6 * current.sel_down_to_up = 0
  ∧ (previous.reg_7 - current.reg_7) * current.sel_7 * current.sel_down_to_up = 0

def transition (_ : Nat) (previous current : Environment FGL) : Prop :=
  transitionRows (rowInputOfEnvironment previous) (rowInputOfEnvironment current)

/-- The exact source-linked successor/current MemAlign constraints: h998's
    `pc' - pc` relation and c0/c2/.../c14's register continuity.

    The generated terms are every-row expressions with no last-row mask
    (`Extraction/MemAlign.lean:51`); D3 therefore checks the final effective
    row against row zero, rather than omitting it or accepting a boundary
    promise. -/
def cyclicSuccessorTransitionRows (current successor : MemAlignRow FGL) : Prop :=
  current.delta_pc = successor.pc - current.pc
  ∧ (successor.reg_0 - current.reg_0) * current.sel_0 * current.sel_up_to_down = 0
  ∧ (successor.reg_1 - current.reg_1) * current.sel_1 * current.sel_up_to_down = 0
  ∧ (successor.reg_2 - current.reg_2) * current.sel_2 * current.sel_up_to_down = 0
  ∧ (successor.reg_3 - current.reg_3) * current.sel_3 * current.sel_up_to_down = 0
  ∧ (successor.reg_4 - current.reg_4) * current.sel_4 * current.sel_up_to_down = 0
  ∧ (successor.reg_5 - current.reg_5) * current.sel_5 * current.sel_up_to_down = 0
  ∧ (successor.reg_6 - current.reg_6) * current.sel_6 * current.sel_up_to_down = 0
  ∧ (successor.reg_7 - current.reg_7) * current.sel_7 * current.sel_up_to_down = 0

def cyclicSuccessorTransition (_ : Nat) (current successor : Environment FGL) : Prop :=
  cyclicSuccessorTransitionRows (rowInputOfEnvironment current)
    (rowInputOfEnvironment successor)

theorem transitionRows_memAlignIdleRow :
    transitionRows memAlignIdleRow memAlignIdleRow := by
  norm_num [transitionRows, memAlignIdleRow, memAlignRowOf, memAlignValue0Of,
    memAlignValue1Of, memAlignLane]

theorem cyclicSuccessorTransitionRows_memAlignIdleRow :
    cyclicSuccessorTransitionRows memAlignIdleRow memAlignIdleRow := by
  norm_num [cyclicSuccessorTransitionRows, memAlignIdleRow, memAlignRowOf,
    memAlignValue0Of, memAlignValue1Of, memAlignLane]

/-- ZisK instantiates both the MemAlign witness and fixed traces over this
    physical domain (`zisk/pil/src/pil_helpers/traces.rs:328-331`,
    `MemAlignFixed<F> = GenericTrace<MemAlignFixedRow<F>, 2097152, 0, 17>`). -/
def memAlignFixedCapacity : Nat := 2097152

/-- Map the 31 effective `MemAlignRow` slots to 30 raw witness slots plus the
    one physical fixed column `L1`. The flattened `ProvableStruct` order puts
    `preL1` at slot 26. -/
private def memAlignFixedLayout (slot : Fin 31) : Sum (Fin 30) (Fin 1) :=
  if h_preL1 : slot.val = 26 then
    .inr ⟨0, by omega⟩
  else
    .inl ⟨slot.val - (if 26 < slot.val then 1 else 0), by
      split <;> omega⟩

/-- MemAlign's one fixed column for the currently modeled segment: `L1` is
    `[1, 0, ...]` (`zisk/state-machines/mem/pil/mem_align.pil:120`). -/
private def memAlignFixedValues (_slot : Fin 1) (row : Fin memAlignFixedCapacity) : FGL :=
  if row.val = 0 then 1 else 0

/-- Component-owned MemAlign fixed schema. `IndexedFixedColumns.fixedAt`
    supplies physical-domain periodic access, while `Table.fixed_domain`
    bounds every materialized MemAlign prefix by this capacity. -/
def memAlignFixedColumns : IndexedFixedColumns FGL 30 where
  capacity := memAlignFixedCapacity
  capacity_pos := by decide
  effectiveWidth := 31
  fixedWidth := 1
  layout := memAlignFixedLayout
  values := memAlignFixedValues

/-- The 30 raw witness cells of a MemAlign row, omitting the component-owned
    `L1` fixed cell (`preL1`) at effective slot 26. -/
def memAlignRawRow (row : MemAlignRow FGL) : Array FGL :=
  #[row.addr, row.offset, row.width, row.wr, row.pc, row.reset,
    row.sel_up_to_down, row.sel_down_to_up,
    row.reg_0, row.reg_1, row.reg_2, row.reg_3, row.reg_4, row.reg_5, row.reg_6, row.reg_7,
    row.sel_0, row.sel_1, row.step, row.sel_2, row.sel_3, row.sel_4, row.sel_5, row.sel_6,
    row.sel_7, row.sel_prove, row.delta_addr, row.delta_pc, row.value_0, row.value_1]

@[simp] theorem memAlignRawRow_size (row : MemAlignRow FGL) : (memAlignRawRow row).size = 30 := by
  simp [memAlignRawRow]

/- Every materialized MemAlign row reads `L1` from the component-owned fixed
    schema. -/
set_option maxRecDepth 4000 in
theorem eval_memAlignFixedColumns_L1
    (index : Nat) (data : ProverData FGL) (raw : Array FGL) :
  (Eval.eval (Environment.fromArray (memAlignFixedColumns.materialize index raw) data)
      (varFromOffset (F := FGL) MemAlignRow 0)).preL1 =
      memAlignFixedColumns.fixedAt 0 index := by
  rw [ProvableStruct.eval_eq_eval, ProvableStruct.varFromOffset_eq_varFromOffset]
  unfold ProvableStruct.eval ProvableStruct.varFromOffset
  simp only [instProvableStructMemAlignRow, ProvableStruct.eval.go,
    ProvableStruct.varFromOffset.go]
  rw [ProvableType.eval_varFromOffset]
  simp only [explicit_provable_type, ProvableType.size,
    IndexedFixedColumns.materialize, Array.getElem?_ofFn]
  simp [IndexedFixedColumns.fixedAt, memAlignFixedColumns,
    memAlignFixedLayout, memAlignFixedValues]

/-- The component-owned `L1` fixed column marks the physical first MemAlign
    row as the boot row (`mem_align.pil:120`, `col fixed L1 = [1,0...]`). -/
theorem memAlignFixedColumns_L1_first : memAlignFixedColumns.fixedAt 0 0 = 1 := by
  simp [IndexedFixedColumns.fixedAt, memAlignFixedColumns, memAlignFixedValues]

/-- Away from the physical first row, `L1` is zero before the intrinsic
    fixed-domain bound permits a periodic wrap. -/
theorem memAlignFixedColumns_L1_nonfirst (index : Nat)
    (h_positive : 0 < index) (h_index : index < memAlignFixedCapacity) :
    memAlignFixedColumns.fixedAt 0 index = 0 := by
  have h_mod_ne : index % memAlignFixedCapacity ≠ 0 := by
    rw [Nat.mod_eq_of_lt h_index]
    exact Nat.ne_of_gt h_positive
  simp [IndexedFixedColumns.fixedAt, memAlignFixedColumns, memAlignFixedValues, h_mod_ne]

/-- No raw witness array can move the boot row's `preL1` away from `1`: the
    component-owned fixed schema supplies it independently of `raw`. This is
    the fact that closes eth-act/zisk-fv#332 -- a prover no longer controls
    `preL1` at the boot row, so `boot_pc_zero` (`Spec.lean`) genuinely forces
    `pc = 0` there. -/
theorem eval_memAlignFixedColumns_L1_boot
    (data : ProverData FGL) (raw : Array FGL) :
  (Eval.eval (Environment.fromArray (memAlignFixedColumns.materialize 0 raw) data)
      (varFromOffset (F := FGL) MemAlignRow 0)).preL1 = 1 := by
  rw [eval_memAlignFixedColumns_L1, memAlignFixedColumns_L1_first]

/-- Materializing `memAlignRawRow` reconstructs the original MemAlign row when
    its one fixed cell agrees with the component-owned fixed schema. -/
theorem eval_memAlignRawRow_materialize
    (index : Nat) (data : ProverData FGL) (row : MemAlignRow FGL)
    (h_preL1 : row.preL1 = memAlignFixedColumns.fixedAt 0 index) :
    Eval.eval
      (Environment.fromArray (memAlignFixedColumns.materialize index (memAlignRawRow row)) data)
      (varFromOffset (F := FGL) MemAlignRow 0) = row := by
  rw [ProvableStruct.eval_eq_eval, ProvableStruct.varFromOffset_eq_varFromOffset]
  unfold ProvableStruct.eval ProvableStruct.varFromOffset
  simp only [instProvableStructMemAlignRow, ProvableStruct.eval.go,
    ProvableStruct.varFromOffset.go, ProvableType.eval_field,
    ProvableType.varFromOffset_field, Expression.eval, Nat.zero_add]
  cases row with
  | mk addr offset width wr pc reset sel_up_to_down sel_down_to_up reg_0 reg_1 reg_2 reg_3
      reg_4 reg_5 reg_6 reg_7 sel_0 sel_1 step sel_2 sel_3 sel_4 sel_5 sel_6 sel_7
      sel_prove preL1 delta_addr delta_pc value_0 value_1 =>
    change preL1 = memAlignFixedColumns.fixedAt 0 index at h_preL1
    simp [IndexedFixedColumns.materialize, IndexedFixedColumns.fixedAt,
      memAlignFixedColumns, memAlignFixedLayout, memAlignFixedValues, memAlignRawRow,
      ProvableType.size]
    simpa [IndexedFixedColumns.fixedAt, memAlignFixedColumns, memAlignFixedValues] using
      h_preL1.symm

def component : Air.Flat.Component FGL :=
  { circuit := circuit
    rawWidth := 30
    fixedColumns := some memAlignFixedColumns
    transition := transition
    cyclicSuccessorTransition := cyclicSuccessorTransition }

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
  change ⟨MemBusChannel.toRaw,
      [((MemBusChannel.emitted
          (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
          (memBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    expose MemBusChannel
      [MemBusChannel.emitted
        (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
        (memBusMessageExpr component.rowInputVar)] ++
    expose ZiskFv.Channels.MemAlignRom.MemAlignRomChannel
      [ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.emitted (-1)
        (memAlignRomMessageExpr component.rowInputVar)] ++
    expose ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel
      [ ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_0)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_1)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_2)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_3)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_4)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_5)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_6)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_7)]
  simp [expose]

/-- MemAlign's h998 consumer emission is exactly one negative bus-133
    interaction per effective row. -/
theorem component_interactionsWith_memAlignRomChannel :
    component.operations.interactionsWith ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.toRaw =
      [((ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.emitted (-1)
          (memAlignRomMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.toRaw,
      [((ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.emitted (-1)
          (memAlignRomMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  change ⟨ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.toRaw,
      [((ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.emitted (-1)
          (memAlignRomMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    expose MemBusChannel
      [MemBusChannel.emitted
        (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
        (memBusMessageExpr component.rowInputVar)] ++
    expose ZiskFv.Channels.MemAlignRom.MemAlignRomChannel
      [ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.emitted (-1)
        (memAlignRomMessageExpr component.rowInputVar)] ++
    expose ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel
      [ ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_0)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_1)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_2)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_3)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_4)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_5)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_6)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_7)]
  simp [expose]

/-- MemAlign's eight source Range Check hints are exactly eight negative
    one-slot bus-107 consumer interactions, in `reg[0]` through `reg[7]`
    order (`mem_align.pil:113-118`; #982/#984/#986/#988/#990/#992/#994/#996). -/
theorem component_interactionsWith_memAlignRangeChannel :
    component.operations.interactionsWith
        ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw =
      [ ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_0)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_1)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_2)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_3)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_4)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_5)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_6)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_7)).toRaw) ] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.toRaw,
      [ ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_0)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_1)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_2)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_3)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_4)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_5)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_6)).toRaw)
      , ((ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
            (memAlignRangeMessageExpr component.rowInputVar.reg_7)).toRaw) ]⟩ ∈
    expose MemBusChannel
      [MemBusChannel.emitted
        (component.rowInputVar.sel_prove - selAssumeExpr component.rowInputVar)
        (memBusMessageExpr component.rowInputVar)] ++
    expose ZiskFv.Channels.MemAlignRom.MemAlignRomChannel
      [ZiskFv.Channels.MemAlignRom.MemAlignRomChannel.emitted (-1)
        (memAlignRomMessageExpr component.rowInputVar)] ++
    expose ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel
      [ ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_0)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_1)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_2)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_3)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_4)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_5)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_6)
      , ZiskFv.Channels.MemAlignRanges.MemAlignRangeChannel.emitted (-1)
          (memAlignRangeMessageExpr component.rowInputVar.reg_7)]
  simp [expose]

/-- Read `delta_pc` from the intrinsic cyclic successor view. -/
theorem delta_pc_eq_successor_pc_sub_pc
    {table : Table FGL} (h_component : table.component = component)
    (h_cyclic : table.CyclicSuccessorTransitionConstraints)
    (index : Fin table.length) :
    (rowInputOfEnvironment (table.environmentAt index)).delta_pc =
      (rowInputOfEnvironment (table.successorEnvironment index)).pc -
        (rowInputOfEnvironment (table.environmentAt index)).pc := by
  have h := h_cyclic index
  rw [h_component] at h
  change cyclicSuccessorTransition index.val (table.environmentAt index)
    (table.successorEnvironment index) at h
  exact h.1

theorem spec_via_component (row : MemAlignRow FGL)
    (_h_assumptions : Assumptions row)
    (h_constraints : Spec row) :
    Spec row := by
  exact h_constraints

end ZiskFv.AirsClean.MemAlign
