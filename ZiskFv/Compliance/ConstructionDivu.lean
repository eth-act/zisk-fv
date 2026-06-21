import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.EquivCore.Divu
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Bits.PackedBitVec.MulNoWrap

/-!
# Sound DIVU construction (`construction_divu_sound`)

Unsigned RV64M DIVU (`OP_DIVU = 184`), mirroring the MULW / MULHU
constructions.  The Arith provider witnesses (ArithTable membership, chunk
ranges, signed-carry ranges, c46, carry-chain) are **DERIVED FROM BALANCE**
via the SHARED ArithMul provider component's lookup-aware
`componentWithArithTable.Spec = FullSpec`, not carried as caller binders.

## Why the shared ArithMul provider (not ArithDiv)

`ArithDiv.component` carries NO operation-bus interactions in the full
ensemble (`arithDiv_table_interactionsWith_opBus_nil`): its
`circuit.channels = []`.  The DIVU Main op-bus emission is therefore balanced
by the SHARED ArithMul provider (`componentWithArithTable`), whose `FullSpec`
covers div rows too (the carry chain is mode-shared via the `div` flag).  The
muxed primary op-bus message, at the DIVU mode pins (`div = 1`,
`main_div = 1`, `main_mul = 0`), reduces to the div quotient-lane message
`opBus_row_ArithDiv`.

## The carry-range subtlety (vs MULW)

`EquivCore.Divu.equiv_DIVU` demands the *unsigned* carry bound
`cy_i.val < 131072 = 2^17`.  Balance supplies only `FullSpec`'s
`CarryRangeSpec` — the **signed disjunction** `< 983041 ∨ ≥ p - 983040`.  The
genuine Euclidean-chain carries (a 4×4 chunk multiply `quotient · divisor`)
reach `~3·2^16 > 2^17`, so the tight `< 131072` bound is NOT balance-
constructible.  This module therefore does NOT route through `equiv_DIVU`.
Instead it derives the looser balance-constructible bound `< 983041` (via
`unsigned_carry_step_nat`, reused from `ConstructionMulhu`) and reconstructs
the rd write value through the loose-bound DIVU write-value path
`h_rd_val_mdru_divu_loose`, replicating `equiv_DIVU`'s sail + `bus_effect`
tail otherwise.

## The remainder bound is RESIDUAL, not balance-derived

`EquivCore.Divu.equiv_DIVU` needs `ArithDivRemainderBoundWitness` — the
`|d| < b` LTU check from `arith.pil:274`.  This is the ArithDiv op-bus
*consumer* (`assumes_operation`) edge matched against a Binary LTU provider
row.  Because `ArithDiv.component` emits no op-bus in the ensemble, this
consume edge is a finished-channel SELF-EDGE that is **not composed into the
ensemble** — so it is NOT balance-derivable.  It is carried as the single
explicit residual binder `remainder_bound` (exactly as the canonical
`equiv_DIVU` already carries it), clearly documented here.

## Axioms

`construction_divu_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.  Its
closure carries `Lean.ofReduceBool` / `Lean.trustCompiler` (native_decide)
INHERITED from the canonical `equiv_DIVU` path (already has it; NOT new —
tracked by #75), plus the Sail-translation + kernel postulates.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ArithMul (componentWithArithTable primaryOpBusMessage rowAt)

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-! ## Phase 1 — row-native ArithDiv view + DIVU-mode op-bus bridge -/

/-- Row-native `Valid_ArithDiv` view of a concrete provider `ArithMulRow`.

    Same shape as `vOfMulwRow` but producing the `Valid_ArithDiv` interface.
    Every column is the constant function returning the corresponding field of
    `arow` (the carry fields `cy_i ← arow.carries.carry_i`), with
    `multiplicity` pinned to `1` (the active-row consume polarity).  Because
    `ArithMulRow` and `ArithDivRow` share field names and `arithTableRow`
    projections, `ArithDiv.rowAt (vOfDivuRow arow) 0` agrees with `arow` on
    every field that `ArithTableSpec` / `opBus_row_ArithDiv` dereference. -/
@[reducible]
def vOfDivuRow (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL) :
    ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL where
  cy_0 := fun _ => arow.carries.carry_0
  cy_1 := fun _ => arow.carries.carry_1
  cy_2 := fun _ => arow.carries.carry_2
  cy_3 := fun _ => arow.carries.carry_3
  cy_4 := fun _ => arow.carries.carry_4
  cy_5 := fun _ => arow.carries.carry_5
  cy_6 := fun _ => arow.carries.carry_6
  a_0 := fun _ => arow.chunks.a_0
  a_1 := fun _ => arow.chunks.a_1
  a_2 := fun _ => arow.chunks.a_2
  a_3 := fun _ => arow.chunks.a_3
  b_0 := fun _ => arow.chunks.b_0
  b_1 := fun _ => arow.chunks.b_1
  b_2 := fun _ => arow.chunks.b_2
  b_3 := fun _ => arow.chunks.b_3
  c_0 := fun _ => arow.chunks.c_0
  c_1 := fun _ => arow.chunks.c_1
  c_2 := fun _ => arow.chunks.c_2
  c_3 := fun _ => arow.chunks.c_3
  d_0 := fun _ => arow.chunks.d_0
  d_1 := fun _ => arow.chunks.d_1
  d_2 := fun _ => arow.chunks.d_2
  d_3 := fun _ => arow.chunks.d_3
  na := fun _ => arow.flags.na
  nb := fun _ => arow.flags.nb
  nr := fun _ => arow.flags.nr
  np := fun _ => arow.flags.np
  sext := fun _ => arow.flags.sext
  m32 := fun _ => arow.flags.m32
  div := fun _ => arow.flags.div
  fab := fun _ => arow.carries.fab
  na_fb := fun _ => arow.carries.na_fb
  nb_fa := fun _ => arow.carries.nb_fa
  main_div := fun _ => arow.flags.main_div
  main_mul := fun _ => arow.flags.main_mul
  signed := fun _ => arow.flags.signed
  div_by_zero := fun _ => arow.flags.div_by_zero
  div_overflow := fun _ => arow.flags.div_overflow
  op := fun _ => arow.flags.op
  bus_res1 := fun _ => arow.flags.bus_res1
  multiplicity := fun _ => 1
  range_ab := fun _ => arow.flags.range_ab
  range_cd := fun _ => arow.flags.range_cd

/-- The ArithDiv-view `FullSpec` of a provider `ArithMulRow`, derived from the
    SHARED-ArithMul-provider `FullSpec arow`.  The ArithDiv `Spec` is the same
    11-clause carry-chain algebra as the ArithMul `Spec` (reading the
    `vOfDivuRow` view's fields, which are `arow`'s fields), and the ArithDiv
    `ArithTableSpec` is the same 15-tuple ROM membership.  No new trust:
    this is a pure algebraic/defeq re-view of the same balance-derived facts. -/
theorem arithDiv_fullSpec_of_arithMul_fullSpec
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h : ZiskFv.AirsClean.ArithMul.FullSpec arow) :
    ZiskFv.AirsClean.ArithDiv.FullSpec
      (ZiskFv.AirsClean.ArithDiv.rowAt (vOfDivuRow arow) 0) := by
  obtain ⟨h_spec, h_table, _h_c46, _h_chunks, _h_carry⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨hc6, hc7, hc8, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38⟩ := h_spec
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination hc6
    · linear_combination hc7
    · linear_combination hc8
    · linear_combination hc31
    · linear_combination hc32
    · linear_combination hc33
    · linear_combination hc34
    · linear_combination hc35
    · linear_combination hc36
    · linear_combination hc37
    · linear_combination hc38
  · simpa [ZiskFv.AirsClean.ArithDiv.ArithTableSpec,
      ZiskFv.AirsClean.ArithDiv.arithTableRow,
      ZiskFv.AirsClean.ArithDiv.rowAt, vOfDivuRow,
      ZiskFv.AirsClean.ArithMul.ArithTableSpec,
      ZiskFv.AirsClean.ArithMul.arithTableRow] using h_table

/-- The ArithDiv-view `div_row_constraints_with_c46` of a provider `ArithMulRow`,
    derived from the SHARED-ArithMul-provider `FullSpec arow`.  The 11-clause
    `div_carry_chain_holds` is the same algebra as the ArithMul `Spec` (carry
    chain), and `bus_res1_eq_div` is the same C46 equation as the ArithMul
    `C46Spec`.  Pure algebraic re-view — no new trust. -/
theorem divu_row_constraints_of_arithMul_fullSpec
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h : ZiskFv.AirsClean.ArithMul.FullSpec arow) :
    ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 (vOfDivuRow arow) 0 := by
  obtain ⟨h_spec, _h_table, h_c46, _h_chunks, _h_carry⟩ := h
  obtain ⟨hc6, hc7, hc8, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38⟩ := h_spec
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [ZiskFv.Airs.ArithDiv.fab_eq_div, vOfDivuRow]; linear_combination hc6
  · simp only [ZiskFv.Airs.ArithDiv.na_fb_eq_div, vOfDivuRow]; linear_combination hc7
  · simp only [ZiskFv.Airs.ArithDiv.nb_fa_eq_div, vOfDivuRow]; linear_combination hc8
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_0_div, vOfDivuRow]; linear_combination hc31
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_1_div, vOfDivuRow]; linear_combination hc32
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_2_div, vOfDivuRow]; linear_combination hc33
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_3_div, vOfDivuRow]; linear_combination hc34
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_4_div, vOfDivuRow]; linear_combination hc35
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_5_div, vOfDivuRow]; linear_combination hc36
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_6_div, vOfDivuRow]; linear_combination hc37
  · simp only [ZiskFv.Airs.ArithDiv.carry_eq_7_div, vOfDivuRow]; linear_combination hc38
  · simp only [ZiskFv.Airs.ArithDiv.bus_res1_eq_div, vOfDivuRow,
      ZiskFv.AirsClean.ArithMul.C46Spec,
      ZiskFv.Airs.ArithMul.mul_constraint_46_named] at h_c46 ⊢
    linear_combination h_c46

/-- DIVU-mode op-bus bridge: the FAITHFUL muxed ArithMul primary message
    reduces to the div quotient-lane `opBus_row_ArithDiv` entry exactly at the
    DIVU mode pins (`div = 1`, `main_div = 1`, `main_mul = 0`).

    At these pins the muxed `a_lo`/`a_hi` lanes (`div·c + (1-div)·a`) collapse
    to the `c`-chunks (dividend), and the muxed `c_lo` lane
    (`(1-main_mul-main_div)·d + main_mul·c + main_div·a`) collapses to the
    `a`-chunks (quotient) — i.e. the muxed primary message at DIVU mode IS the
    div quotient-lane message.  The mode pins are discharged by the caller
    (the construction) from the provider row's `ArithTableSpec` + opcode pin. -/
theorem primaryOpBusMessage_toEntry_eq_opBus_row_ArithDiv
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_div : arow.flags.div = 1) (h_main_div : arow.flags.main_div = 1)
    (h_main_mul : arow.flags.main_mul = 0) :
    ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1 =
      ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv (vOfDivuRow arow) 0 := by
  simp only [ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
    ZiskFv.AirsClean.ArithMul.primaryOpBusMessage,
    ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv, vOfDivuRow,
    h_div, h_main_div, h_main_mul]
  ring

/-- The DIVU op-bus match transports along the ArithDiv row-native view: a
    match against the FAITHFUL muxed primary message of a concrete row carries
    over to `opBus_row_ArithDiv (vOfDivuRow arow) 0`, via the DIVU-mode bridge
    `primaryOpBusMessage_toEntry_eq_opBus_row_ArithDiv`. -/
theorem match_opBus_row_ArithDiv_vOfDivuRow
    {x : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_div : arow.flags.div = 1) (h_main_div : arow.flags.main_div = 1)
    (h_main_mul : arow.flags.main_mul = 0)
    (h :
      matches_entry x
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1)) :
    matches_entry x (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv (vOfDivuRow arow) 0) := by
  rw [← primaryOpBusMessage_toEntry_eq_opBus_row_ArithDiv arow h_div h_main_div h_main_mul]
  exact h

/-! ## Phase 2 — balance-derived div-Euclidean chunk equations + loose carry bounds -/

open ZiskFv.Airs.ArithMul in


/-! ## Phase 3 — balance-selected DIVU provider row + transports -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a DIVU
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the DIVU
    keep-arithMul balance wrapper
    `exists_arithMul_provider_row_matches_primary_of_divu_from_binding`.
    Mirrors `mulwArow`. -/
noncomputable def divuArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := exists_arithMul_provider_row_matches_primary_of_divu_from_binding
    trace binding i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected DIVU provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem divuArow_fullSpec_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU) :
    ZiskFv.AirsClean.ArithMul.FullSpec (divuArow trace binding i h_main_active h_main_op) := by
  unfold divuArow
  set H := exists_arithMul_provider_row_matches_primary_of_divu_from_binding
    trace binding i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- The op-bus match of the balance-selected DIVU provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form (cheap: free
    `ArithMulRow`, no view whnf). -/
theorem divuArow_match_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (divuArow trace binding i h_main_active h_main_op)) 1) := by
  unfold divuArow
  set H := exists_arithMul_provider_row_matches_primary_of_divu_from_binding
    trace binding i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- DIVU mode pins on the balance-selected provider row, DERIVED from its
    `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 184`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `divu_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem divuArow_mode_pins
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU) :
    (divuArow trace binding i h_main_active h_main_op).flags.na = 0
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.nb = 0
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.np = 0
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.nr = 0
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.sext = 0
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.m32 = 0
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.div = 1
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.main_div = 1
      ∧ (divuArow trace binding i h_main_active h_main_op).flags.main_mul = 0 := by
  have h_table := (divuArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (divuArow trace binding i h_main_active h_main_op).flags.op = 184 := by
    have h_match := divuArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val).op
          = (mainOfTable trace.program binding.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_DIVU] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.divu_mode_pins_of_row
    (divuArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected DIVU provider row view against the
    Main row's emission, in `opBus_row_ArithDiv` form.  The DIVU mode pins
    needed to reduce the faithful mux are DERIVED via `divuArow_mode_pins`. -/
theorem divuArow_match
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv
        (vOfDivuRow (divuArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨_, _, _, _, _, _, h_div, h_main_div, h_main_mul⟩ :=
    divuArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithDiv_vOfDivuRow h_div h_main_div h_main_mul
    (divuArow_match_row trace binding i h_main_active h_main_op)

/-! ## Phase 4 — F4 `FullSpec` discharge bridge for DIVU -/

open ZiskFv.Airs.ArithDiv in
open ZiskFv.EquivCore.Promises in

/-! ## Phase 5 — sound DIVU construction -/


end ZiskFv.Compliance
