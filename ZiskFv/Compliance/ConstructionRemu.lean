import ZiskFv.Compliance.OpBusProviderMatch
import ZiskFv.Compliance.SailTrace
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.EquivCore.Remu
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Bits.PackedBitVec.MulNoWrap

/-!
# Sound REMU construction (`construction_remu_sound`)

Unsigned RV64M **REMU** (`OP_REMU = 185`), the remainder sibling of DIVU.
The Arith provider witnesses (ArithTable membership, chunk ranges,
signed-carry ranges, c46, carry-chain) are **DERIVED FROM BALANCE** via the
SHARED ArithMul provider component's lookup-aware
`componentWithArithTable.Spec = FullSpec`, not carried as caller binders.

## Why the shared ArithMul provider (not ArithDiv)

`ArithDiv.component` carries NO operation-bus interactions in the full
ensemble (`arithDiv_table_interactionsWith_opBus_nil`): its
`circuit.channels = []`.  The REMU Main op-bus emission is therefore balanced
by the SHARED ArithMul provider (`componentWithArithTable`), whose `FullSpec`
covers div rows too (the carry chain is mode-shared via the `div` flag).

## The REMU SECONDARY lane (delta from DIVU)

REMU's result is the **remainder** in `d[]`, not the quotient in `a[]`.  REMU
consumes the **secondary** Arith lane: `main_div = 0`, `main_mul = 0` (so
`secondary = 1`).  At these mode pins the muxed primary op-bus message's `c_lo`
lane `(1 - main_mul - main_div)·(d_0 + d_1·2^16) + …` collapses to
`d_0 + d_1·2^16` (the remainder low half), so the muxed message reduces to the
div **remainder**-lane message `opBus_row_ArithDivSecondary`, NOT the
quotient-lane `opBus_row_ArithDiv` that DIVU uses.  The REMU-mode op-bus bridge
below therefore differs from DIVU's: it pins `main_div = 0` (vs DIVU's
`main_div = 1`) and targets `opBus_row_ArithDivSecondary`.  The high half comes
from `bus_res1 = d_2 + d_3·2^16` (constraint 46 at the secondary pins, via
`rem_bus_res1_eq_d_hi`).

## The carry-range subtlety (vs MULW)

`EquivCore.Remu.equiv_REMU` consumes carry witnesses through
`div_unsigned_chain_witnesses_of_carry_ranges`; this bridge instead derives the
looser balance-constructible bound `< 983041` (via `divu_carry_bounds`, reused
from `ConstructionDivu`) and reconstructs the rd write value through the
loose-bound REMU write-value path `h_rd_val_mdru_remu_loose`, replicating
`equiv_REMU`'s sail + `bus_effect` tail otherwise.

## The remainder bound is RESIDUAL, not balance-derived

`equiv_REMU` needs `ArithDivRemainderBoundWitness` — the `|d| < b` LTU check
from `arith.pil:274`.  This is the ArithDiv op-bus *consumer*
(`assumes_operation`) edge matched against a Binary LTU provider row.  Because
`ArithDiv.component` emits no op-bus in the ensemble, this consume edge is a
finished-channel SELF-EDGE that is **not composed into the ensemble** — so it is
NOT balance-derivable.  It is carried as the single explicit residual binder
`remainder_bound` (exactly as the canonical `equiv_REMU` already carries it).

## Axioms

`construction_remu_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.  Its
closure carries `Lean.ofReduceBool` / `Lean.trustCompiler` (native_decide)
INHERITED from the canonical `equiv_REMU` path (already has it; NOT new —
tracked by #75), plus `Classical.choice` / `Quot.sound`, the Sail-translation
postulates, and the Lean-kernel postulates.
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

/-! ## Phase 1 — REMU-mode op-bus bridge (secondary remainder lane) -/

/-- REMU-mode op-bus bridge: the FAITHFUL muxed ArithMul primary message
    reduces to the div remainder-lane `opBus_row_ArithDivSecondary` entry
    exactly at the REMU mode pins (`div = 1`, `main_div = 0`, `main_mul = 0`).

    At these pins the muxed `a_lo`/`a_hi` lanes (`div·c + (1-div)·a`) collapse
    to the `c`-chunks (dividend), and the muxed `c_lo` lane
    `(1-main_mul-main_div)·d + main_mul·c + main_div·a` collapses to the
    `d`-chunks (remainder) — i.e. the muxed primary message at REMU mode IS the
    div remainder-lane message.  Differs from DIVU's bridge in pinning
    `main_div = 0` (vs DIVU's `main_div = 1`) and targeting the secondary row. -/
theorem primaryOpBusMessage_toEntry_eq_opBus_row_ArithDivSecondary
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_div : arow.flags.div = 1) (h_main_div : arow.flags.main_div = 0)
    (h_main_mul : arow.flags.main_mul = 0) :
    ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1 =
      ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary (vOfDivuRow arow) 0 := by
  simp only [ZiskFv.Channels.OperationBus.OpBusMessage.toEntry,
    ZiskFv.AirsClean.ArithMul.primaryOpBusMessage,
    ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary, vOfDivuRow,
    h_div, h_main_div, h_main_mul]
  ring

/-- The REMU op-bus match transports along the ArithDiv secondary row-native
    view: a match against the FAITHFUL muxed primary message of a concrete row
    carries over to `opBus_row_ArithDivSecondary (vOfDivuRow arow) 0`, via the
    REMU-mode bridge. -/
theorem match_opBus_row_ArithDivSecondary_vOfDivuRow
    {x : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_div : arow.flags.div = 1) (h_main_div : arow.flags.main_div = 0)
    (h_main_mul : arow.flags.main_mul = 0)
    (h :
      matches_entry x
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1)) :
    matches_entry x
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary (vOfDivuRow arow) 0) := by
  rw [← primaryOpBusMessage_toEntry_eq_opBus_row_ArithDivSecondary
        arow h_div h_main_div h_main_mul]
  exact h

/-! ## Phase 3 — balance-selected REMU provider row + transports -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a REMU
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the REMU
    keep-arithMul balance wrapper
    `main_request_remu_provided`.
    Mirrors `divuArow`. -/
noncomputable def remuArow
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := main_request_remu_provided
    trace i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected REMU provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem remuArow_fullSpec_row
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (remuArow trace binding i h_main_active h_main_op) := by
  unfold remuArow
  set H := main_request_remu_provided
    trace i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- The op-bus match of the balance-selected REMU provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form. -/
theorem remuArow_match_row
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (remuArow trace binding i h_main_active h_main_op)) 1) := by
  unfold remuArow
  set H := main_request_remu_provided
    trace i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- REMU mode pins on the balance-selected provider row, DERIVED from its
    `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 185`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `remu_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem remuArow_mode_pins
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    (remuArow trace binding i h_main_active h_main_op).flags.na = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.nb = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.np = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.nr = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.sext = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.m32 = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.div = 1
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.main_div = 0
      ∧ (remuArow trace binding i h_main_active h_main_op).flags.main_mul = 0 := by
  have h_table := (remuArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (remuArow trace binding i h_main_active h_main_op).flags.op = 185 := by
    have h_match := remuArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val).op
          = (mainOfTable trace.program trace.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_REMU] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.remu_mode_pins_of_row
    (remuArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected REMU provider row view against the
    Main row's emission, in `opBus_row_ArithDivSecondary` form.  The REMU mode
    pins needed to reduce the faithful mux are DERIVED via `remuArow_mode_pins`. -/
theorem remuArow_match
    (trace : AcceptedZiskTrace) (binding : SailTrace trace.numInstructions) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary
        (vOfDivuRow (remuArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨_, _, _, _, _, _, h_div, h_main_div, h_main_mul⟩ :=
    remuArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithDivSecondary_vOfDivuRow h_div h_main_div h_main_mul
    (remuArow_match_row trace binding i h_main_active h_main_op)

/-! ## Phase 2 — balance-derived div-Euclidean chunk equations + loose carry bounds

The REMU Euclidean chunk identity is the SAME as DIVU's: the carry-chain
constraints 31–38 do not reference `main_div` / `main_mul` (they share the `div`
flag).  We re-derive them here over `vOfDivuRow` (reused from `ConstructionDivu`)
at the unsigned mode pins `na = nb = np = nr = m32 = 0`, `div = 1` — identical
to `divu_chain_eqs` / `divu_carry_bounds`, but those are `private` to
`ConstructionDivu`, so (as DIVUW does) we keep local copies here. -/

open ZiskFv.Airs.ArithMul in
/-- **Mode-pinned REMU Euclidean chunk equations.** Identical to DIVU's
    `divu_chain_eqs` — the carry-chain constraints 31–38 are
    `main_div`/`main_mul`-independent, so the REMU secondary-lane chain is the
    same low Euclidean form. -/
private lemma remu_chain_eqs_claimed_dead
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_chain : mul_carry_chain_holds (vOfMulwRow arow) 0)
    (h_na : arow.flags.na = 0) (h_nb : arow.flags.nb = 0)
    (h_np : arow.flags.np = 0) (h_nr : arow.flags.nr = 0)
    (h_m32 : arow.flags.m32 = 0) (h_div : arow.flags.div = 1) :
    (arow.chunks.a_0 * arow.chunks.b_0 + arow.chunks.d_0
        = arow.chunks.c_0 + arow.carries.carry_0 * 65536)
    ∧ (arow.chunks.a_1 * arow.chunks.b_0 + arow.chunks.a_0 * arow.chunks.b_1
        + arow.chunks.d_1 + arow.carries.carry_0
        = arow.chunks.c_1 + arow.carries.carry_1 * 65536)
    ∧ (arow.chunks.a_2 * arow.chunks.b_0 + arow.chunks.a_1 * arow.chunks.b_1
        + arow.chunks.a_0 * arow.chunks.b_2 + arow.chunks.d_2 + arow.carries.carry_1
        = arow.chunks.c_2 + arow.carries.carry_2 * 65536)
    ∧ (arow.chunks.a_3 * arow.chunks.b_0 + arow.chunks.a_2 * arow.chunks.b_1
        + arow.chunks.a_1 * arow.chunks.b_2 + arow.chunks.a_0 * arow.chunks.b_3
        + arow.chunks.d_3 + arow.carries.carry_2
        = arow.chunks.c_3 + arow.carries.carry_3 * 65536)
    ∧ (arow.chunks.a_3 * arow.chunks.b_1 + arow.chunks.a_2 * arow.chunks.b_2
        + arow.chunks.a_1 * arow.chunks.b_3 + arow.carries.carry_3
        = arow.carries.carry_4 * 65536)
    ∧ (arow.chunks.a_3 * arow.chunks.b_2 + arow.chunks.a_2 * arow.chunks.b_3
        + arow.carries.carry_4 = arow.carries.carry_5 * 65536)
    ∧ (arow.chunks.a_3 * arow.chunks.b_3 + arow.carries.carry_5
        = arow.carries.carry_6 * 65536)
    ∧ (arow.carries.carry_6 = 0) := by
  obtain ⟨h6, h7, h8, h31, h32, h33, h34, h35, h36, h37, h38⟩ := h_chain
  simp only [mul_constraint_6_named, mul_constraint_7_named, mul_constraint_8_named,
             vOfMulwRow, h_na, h_nb, mul_zero, zero_mul, add_zero, sub_zero] at h6 h7 h8
  have h_fab : arow.carries.fab = (1 : FGL) := by linear_combination h6
  have h_nafb : arow.carries.na_fb = (0 : FGL) := by linear_combination h7
  have h_nbfa : arow.carries.nb_fa = (0 : FGL) := by linear_combination h8
  simp only [mul_constraint_31_named, mul_constraint_32_named,
             mul_constraint_33_named, mul_constraint_34_named,
             mul_constraint_35_named, mul_constraint_36_named,
             mul_constraint_37_named, mul_constraint_38_named,
             vOfMulwRow, h_na, h_nb, h_np, h_nr, h_m32, h_div, h_fab, h_nafb, h_nbfa,
             mul_zero, zero_mul, add_zero, sub_zero, mul_one, one_mul]
    at h31 h32 h33 h34 h35 h36 h37 h38
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h31
  · linear_combination h32
  · linear_combination h33
  · linear_combination h34
  · linear_combination h35
  · linear_combination h36
  · linear_combination h37
  · linear_combination h38

/-- **Balance-constructible REMU unsigned carry bounds.** Identical to DIVU's
    `divu_carry_bounds`: derive the looser unsigned-side carry bounds
    `cy_i.val < 983041` via `unsigned_carry_step_nat` (reused from
    `ConstructionMulhu`). -/
private lemma remu_carry_bounds_claimed_dead
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_chunks : ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt (vOfDivuRow arow) 0)
    (h_csgn : ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedCarryRangesAt (vOfDivuRow arow) 0)
    (heqs :
      (arow.chunks.a_0 * arow.chunks.b_0 + arow.chunks.d_0
          = arow.chunks.c_0 + arow.carries.carry_0 * 65536)
      ∧ (arow.chunks.a_1 * arow.chunks.b_0 + arow.chunks.a_0 * arow.chunks.b_1
          + arow.chunks.d_1 + arow.carries.carry_0
          = arow.chunks.c_1 + arow.carries.carry_1 * 65536)
      ∧ (arow.chunks.a_2 * arow.chunks.b_0 + arow.chunks.a_1 * arow.chunks.b_1
          + arow.chunks.a_0 * arow.chunks.b_2 + arow.chunks.d_2 + arow.carries.carry_1
          = arow.chunks.c_2 + arow.carries.carry_2 * 65536)
      ∧ (arow.chunks.a_3 * arow.chunks.b_0 + arow.chunks.a_2 * arow.chunks.b_1
          + arow.chunks.a_1 * arow.chunks.b_2 + arow.chunks.a_0 * arow.chunks.b_3
          + arow.chunks.d_3 + arow.carries.carry_2
          = arow.chunks.c_3 + arow.carries.carry_3 * 65536)
      ∧ (arow.chunks.a_3 * arow.chunks.b_1 + arow.chunks.a_2 * arow.chunks.b_2
          + arow.chunks.a_1 * arow.chunks.b_3 + arow.carries.carry_3
          = arow.carries.carry_4 * 65536)
      ∧ (arow.chunks.a_3 * arow.chunks.b_2 + arow.chunks.a_2 * arow.chunks.b_3
          + arow.carries.carry_4 = arow.carries.carry_5 * 65536)
      ∧ (arow.chunks.a_3 * arow.chunks.b_3 + arow.carries.carry_5
          = arow.carries.carry_6 * 65536)
      ∧ (arow.carries.carry_6 = 0)) :
    (arow.carries.carry_0).val < 983041 ∧ (arow.carries.carry_1).val < 983041
    ∧ (arow.carries.carry_2).val < 983041 ∧ (arow.carries.carry_3).val < 983041
    ∧ (arow.carries.carry_4).val < 983041 ∧ (arow.carries.carry_5).val < 983041
    ∧ (arow.carries.carry_6).val < 983041 := by
  obtain ⟨ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3,
          hc0, hc1, hc2, hc3, hd0, hd1, hd2, hd3⟩ := h_chunks
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6⟩ := h_csgn
  obtain ⟨hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ := heqs
  simp only [vOfDivuRow] at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hc0 hc1 hc2 hc3 hd0 hd1 hd2 hd3
  simp only [vOfDivuRow] at hs0 hs1 hs2 hs3 hs4 hs5 hs6
  have b0 : (arow.carries.carry_0).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_0).val * (arow.chunks.b_0).val + (arow.chunks.d_0).val)
      _ _ ?_ hc0 ?_ hs0
    · push_cast; linear_combination hC31
    · have : (arow.chunks.a_0).val * (arow.chunks.b_0).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have b1 : (arow.carries.carry_1).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_1).val * (arow.chunks.b_0).val
        + (arow.chunks.a_0).val * (arow.chunks.b_1).val
        + (arow.chunks.d_1).val + (arow.carries.carry_0).val) _ _ ?_ hc1 ?_ hs1
    · push_cast; linear_combination hC32
    · have h1 : (arow.chunks.a_1).val * (arow.chunks.b_0).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (arow.chunks.a_0).val * (arow.chunks.b_1).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have b2 : (arow.carries.carry_2).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_2).val * (arow.chunks.b_0).val
        + (arow.chunks.a_1).val * (arow.chunks.b_1).val
        + (arow.chunks.a_0).val * (arow.chunks.b_2).val
        + (arow.chunks.d_2).val + (arow.carries.carry_1).val) _ _ ?_ hc2 ?_ hs2
    · push_cast; linear_combination hC33
    · have h1 : (arow.chunks.a_2).val * (arow.chunks.b_0).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (arow.chunks.a_1).val * (arow.chunks.b_1).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (arow.chunks.a_0).val * (arow.chunks.b_2).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have b3 : (arow.carries.carry_3).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_3).val * (arow.chunks.b_0).val
        + (arow.chunks.a_2).val * (arow.chunks.b_1).val
        + (arow.chunks.a_1).val * (arow.chunks.b_2).val
        + (arow.chunks.a_0).val * (arow.chunks.b_3).val
        + (arow.chunks.d_3).val + (arow.carries.carry_2).val) _ _ ?_ hc3 ?_ hs3
    · push_cast; linear_combination hC34
    · have h1 : (arow.chunks.a_3).val * (arow.chunks.b_0).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (arow.chunks.a_2).val * (arow.chunks.b_1).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (arow.chunks.a_1).val * (arow.chunks.b_2).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h4 : (arow.chunks.a_0).val * (arow.chunks.b_3).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have b4 : (arow.carries.carry_4).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_3).val * (arow.chunks.b_1).val
        + (arow.chunks.a_2).val * (arow.chunks.b_2).val
        + (arow.chunks.a_1).val * (arow.chunks.b_3).val
        + (arow.carries.carry_3).val) 0 _ ?_ (by omega) ?_ hs4
    · push_cast; linear_combination hC35
    · have h1 : (arow.chunks.a_3).val * (arow.chunks.b_1).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (arow.chunks.a_2).val * (arow.chunks.b_2).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : (arow.chunks.a_1).val * (arow.chunks.b_3).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have b5 : (arow.carries.carry_5).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_3).val * (arow.chunks.b_2).val
        + (arow.chunks.a_2).val * (arow.chunks.b_3).val
        + (arow.carries.carry_4).val) 0 _ ?_ (by omega) ?_ hs5
    · push_cast; linear_combination hC36
    · have h1 : (arow.chunks.a_3).val * (arow.chunks.b_2).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      have h2 : (arow.chunks.a_2).val * (arow.chunks.b_3).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  have b6 : (arow.carries.carry_6).val < 983041 := by
    refine unsigned_carry_step_nat_claimed_dead
      ((arow.chunks.a_3).val * (arow.chunks.b_3).val + (arow.carries.carry_5).val)
      0 _ ?_ (by omega) ?_ hs6
    · push_cast; linear_combination hC37
    · have h1 : (arow.chunks.a_3).val * (arow.chunks.b_3).val ≤ 65535 * 65535 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  exact ⟨b0, b1, b2, b3, b4, b5, b6⟩

/-! ## Phase 4 — F4 `FullSpec` discharge bridge for REMU -/

open ZiskFv.Airs.ArithDiv in
open ZiskFv.EquivCore.Promises in
/-- **F4 extraction bridge for `equiv_REMU`.**  Mirror of
    `equiv_DIVU_of_fullSpec` for the remainder (secondary) lane.  The four
    lookup-aware Arith witness records are replaced by the single `FullSpec arow`
    hypothesis (the SHARED ArithMul provider's `componentWithArithTable.Spec`),
    with the ArithDiv-view facts read off the same row through `vOfDivuRow arow`.

    Like DIVU, this derives the looser balance bound `< 983041` (via
    `divu_carry_bounds`) and reconstructs the rd write value through the loose
    write-value path `h_rd_val_mdru_remu_loose`, replicating `equiv_REMU`'s
    sail + `bus_effect` tail.

    The remainder bound `remainder_bound : ArithDivRemainderBoundWitness` is the
    ONE explicit residual binder (NOT balance-derived): the ArithDiv op-bus
    consumer `assumes_operation` edge is a finished-channel self-edge absent
    from the full ensemble (see module header). -/
lemma equiv_REMU_of_fullSpec_claimed_dead
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary (vOfDivuRow arow) 0))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_full_spec : ZiskFv.AirsClean.ArithMul.FullSpec arow)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness (vOfDivuRow arow) 0)
    (h_rs1_value : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.c_0).val (arow.chunks.c_1).val
          (arow.chunks.c_2).val (arow.chunks.c_3).val)
    (h_rs2_value : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.b_0).val (arow.chunks.b_1).val
          (arow.chunks.b_2).val (arow.chunks.b_3).val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  -- Unpack FullSpec into its five conjuncts (ArithMul view of `arow`).
  obtain ⟨h_spec, h_arith_table, h_c46, h_chunk_ranges_spec, h_carry_ranges_spec⟩ :=
    h_full_spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨_h_main_active, h_main_op_remu⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_div_secondary_op_eq h_match_primary
  have h_op_arith_remu : (vOfDivuRow arow).op 0 = 185 := by
    rw [h_op_eq, h_main_op_remu]; simp [OP_REMU]
  -- ============ REMU mode pins, DERIVED from the bare-row ArithTableSpec ======
  have h_op_arow : arow.flags.op = 185 := h_op_arith_remu
  obtain ⟨h_na_arow, h_nb_arow, h_np_arow, h_nr_arow, h_sext_arow, h_m32_arow,
          h_div_arow, h_main_div_arow, h_main_mul_arow⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.remu_mode_pins_of_row arow h_arith_table h_op_arow
  -- ArithDiv-view mode pins (defeq to the bare-row flags).
  have h_na : (vOfDivuRow arow).na 0 = 0 := h_na_arow
  have h_nb : (vOfDivuRow arow).nb 0 = 0 := h_nb_arow
  have h_nr : (vOfDivuRow arow).nr 0 = 0 := h_nr_arow
  have h_sext : (vOfDivuRow arow).sext 0 = 0 := h_sext_arow
  have h_m32 : (vOfDivuRow arow).m32 0 = 0 := h_m32_arow
  have h_div : (vOfDivuRow arow).div 0 = 1 := h_div_arow
  -- ============ Chunk / carry ranges (ArithDiv view, from FullSpec) ==========
  have h_chunk_ranges :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivChunkRangesAt (vOfDivuRow arow) 0 :=
    h_chunk_ranges_spec
  have h_carry_ranges_signed :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivSignedCarryRangesAt (vOfDivuRow arow) 0 :=
    h_carry_ranges_spec
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt,
          h_b0_lt, h_b1_lt, h_b2_lt, h_b3_lt,
          h_c0_lt, h_c1_lt, h_c2_lt, h_c3_lt,
          h_d0_lt, h_d1_lt, h_d2_lt, h_d3_lt⟩ := h_chunk_ranges
  -- ============ Mode-pinned div-Euclidean chunk equations ============
  have heqs := remu_chain_eqs_claimed_dead arow h_spec h_na_arow h_nb_arow h_np_arow h_nr_arow
    h_m32_arow h_div_arow
  -- ============ Balance-constructible LOOSE unsigned carry bounds ============
  obtain ⟨hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6⟩ :=
    remu_carry_bounds_claimed_dead arow h_chunk_ranges_spec h_carry_ranges_signed heqs
  obtain ⟨hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ := heqs
  -- ============ Remainder bound (RESIDUAL): d < b in chunk form ============
  have h_d_lt_b_arith :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_remainder_bound_unsigned
      remainder_bound h_chunk_ranges_spec h_nr h_nb
  have h_d_lt_b :
      ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.d_0).val (arow.chunks.d_1).val
          (arow.chunks.d_2).val (arow.chunks.d_3).val
        < remu_input.r2_val.toNat := by
    simpa [h_rs2_value] using h_d_lt_b_arith
  have h_op2_ne : remu_input.r2_val.toNat ≠ 0 := by
    intro h_zero
    have : ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.d_0).val (arow.chunks.d_1).val
          (arow.chunks.d_2).val (arow.chunks.d_3).val < 0 := by
      simpa [h_zero] using h_d_lt_b
    omega
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (remainder d-lanes) ==========
  obtain ⟨_h_a_lo_eq_FGL, _h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, h_c1_eq_FGL⟩ :=
    arith_div_secondary_projections h_match_primary
  have h_bundle := arith_mem.c_lane_vals
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [arith_h_pair_lift _ _ h_d0_lt h_d1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_bus_res1_eq : (vOfDivuRow arow).bus_res1 0
      = (vOfDivuRow arow).d_2 0 + (vOfDivuRow arow).d_3 0 * 65536 :=
    ZiskFv.Airs.ArithBusRes1.rem_bus_res1_eq_d_hi (vOfDivuRow arow) 0
      (by
        -- c46 (ArithDiv form) from the ArithMul-view C46Spec on the same row.
        simp only [ZiskFv.AirsClean.ArithMul.C46Spec,
          ZiskFv.Airs.ArithMul.mul_constraint_46_named] at h_c46
        simp only [ZiskFv.Airs.ArithDiv.bus_res1_eq_div, vOfDivuRow]
        linear_combination h_c46)
      h_sext h_m32 h_main_mul_arow h_main_div_arow
  have h_byte_hi_to_c1 : (byteAt e2 4).val + (byteAt e2 5).val * 256
      + (byteAt e2 6).val * 65536 + (byteAt e2 7).val * 16777216
      = (m.c_1 r_main).val := by
    have h_e2_hi_bound : e2.value_1.val < 4294967296 := by
      rw [← h_bundle.2, h_c1_eq_FGL, h_bus_res1_eq]
      rw [arith_h_pair_lift _ _ h_d2_lt h_d3_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_hi_val_sum_eq e2 h_e2_hi_bound, h_bundle.2]
  have h_byte_lo :=
    arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
  have h_c1_eq_FGL' : m.c_1 r_main = (vOfDivuRow arow).d_2 0 + (vOfDivuRow arow).d_3 0 * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]
  have h_byte_hi :=
    arith_byte_lane_eq_of_match h_byte_hi_to_c1 h_c1_eq_FGL' h_d2_lt h_d3_lt
  -- ============ DISCHARGE rd-write value via the LOOSE write-value path ======
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_remu_loose
      remu_input.r1_val remu_input.r2_val e2
      (arow.chunks.a_0) (arow.chunks.a_1) (arow.chunks.a_2) (arow.chunks.a_3)
      (arow.chunks.b_0) (arow.chunks.b_1) (arow.chunks.b_2) (arow.chunks.b_3)
      (arow.chunks.c_0) (arow.chunks.c_1) (arow.chunks.c_2) (arow.chunks.c_3)
      (arow.chunks.d_0) (arow.chunks.d_1) (arow.chunks.d_2) (arow.chunks.d_3)
      (arow.carries.carry_0) (arow.carries.carry_1) (arow.carries.carry_2)
      (arow.carries.carry_3) (arow.carries.carry_4) (arow.carries.carry_5)
      (arow.carries.carry_6)
      h0 h1 h2 h3 h4 h5 h6 h7
      h_a0_lt h_a1_lt h_a2_lt h_a3_lt h_b0_lt h_b1_lt h_b2_lt h_b3_lt
      h_c0_lt h_c1_lt h_c2_lt h_c3_lt h_d0_lt h_d1_lt h_d2_lt h_d3_lt
      hcy0 hcy1 hcy2 hcy3 hcy4 hcy5 hcy6
      hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
      h_byte_lo h_byte_hi h_rs1_value h_rs2_value h_op2_ne h_d_lt_b
  -- ============ Replicate `equiv_REMU`'s sail + bus_effect tail ==============
  rw [ZiskFv.EquivCore.Remu.equiv_REMU_sail state remu_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remu_pure, h_rd_idx]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · rw [h_rd_val]

/-! ## Phase 5 — sound REMU construction -/

/-- **Sound REMU construction:** from the accepted trace + honest residual
    binders, conclude the canonical
    `execute (REM (r2, r1, rd, true)) = (bus_effect …).2`.

    The Arith provider witnesses (ArithTable membership, chunk ranges, signed
    carry ranges, c46, carry-chain) are DERIVED inside the body from
    `trace.channels_balanced` / `trace.spec_holds` via the SHARED ArithMul provider's
    lookup-aware `componentWithArithTable.Spec = FullSpec`, NOT supplied as
    binders.

    The ONE non-balance-derived residual is `remainder_bound`
    (`ArithDivRemainderBoundWitness`): the `|d| < b` LTU consumer edge from
    `arith.pil:274` is a finished-channel self-edge absent from the full
    ensemble (`ArithDiv.component` emits no op-bus —
    `arithDiv_table_interactionsWith_opBus_nil`), so it is carried explicitly,
    exactly as the canonical `equiv_REMU` carries it. -/
theorem construction_remu_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (remu_input : PureSpec.RemuInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_REMU)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_store_pc :
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok remu_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok remu_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some remu_input.PC)
    (h_input_rd : remu_input.rd = regidx_to_fin rd)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC)
    (h_rd_idx :
      remu_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr)
    -- (c) byte range bounds on the rd-write entry
    (bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2)
    -- (b) RESIDUAL: remainder-bound witness (the ONE non-balance-derived
    -- binder — the ArithDiv `assumes_operation` LTU consumer edge is a
    -- finished-channel self-edge absent from the ensemble).
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
        (vOfDivuRow (remuArow trace binding i h_main_active h_main_op)) 0)
    -- (b) operand bridges (Sail↔chunk binding of the unsigned 64-bit operands;
    -- genuinely residual, phrased over the balance-selected provider row).
    (h_rs1_value : remu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((remuArow trace binding i h_main_active h_main_op).chunks.c_0).val
          ((remuArow trace binding i h_main_active h_main_op).chunks.c_1).val
          ((remuArow trace binding i h_main_active h_main_op).chunks.c_2).val
          ((remuArow trace binding i h_main_active h_main_op).chunks.c_3).val)
    (h_rs2_value : remu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((remuArow trace binding i h_main_active h_main_op).chunks.b_0).val
          ((remuArow trace binding i h_main_active h_main_op).chunks.b_1).val
          ((remuArow trace binding i h_main_active h_main_op).chunks.b_2).val
          ((remuArow trace binding i h_main_active h_main_op).chunks.b_3).val) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REM (r2, r1, rd, true))) (binding i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding i)).2 := by
  -- (a) Arith witnesses derived from balance: FullSpec.
  have h_full :
      ZiskFv.AirsClean.ArithMul.FullSpec
        (remuArow trace binding i h_main_active h_main_op) :=
    remuArow_fullSpec_row trace binding i h_main_active h_main_op
  -- (a) primary op-bus match against `opBus_row_ArithDivSecondary (vOfDivuRow …) 0`.
  have h_match_primary :
      matches_entry (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary
          (vOfDivuRow (remuArow trace binding i h_main_active h_main_op)) 0) :=
    remuArow_match trace binding i h_main_active h_main_op
  -- decode pins bundle
  let pins :
      ZiskFv.Compliance.MainRowPins
        (mainOfTable trace.program trace.mainTable) i.val 1 OP_REMU :=
    ⟨h_main_active, h_main_op⟩
  -- (a) Main rd-write memory witness, from `store_pc = 0`.
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt (mainOfTable trace.program trace.mainTable) i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness
        (mainOfTable trace.program trace.mainTable) i.val
        (busSub trace binding i execRow).e2 :=
    { row := mainRowWithRomSub trace binding i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  -- promises bundle: Sail reads + exec artifacts as binders; MemBus shape by rfl.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) remu_input.r1_val remu_input.r2_val remu_input.rd remu_input.PC
      (PureSpec.execute_DIVREM_remu_pure remu_input).nextPC
      r1 r2 rd (busSub trace binding i execRow).exec_row (busSub trace binding i execRow).e0
      (busSub trace binding i execRow).e1 (busSub trace binding i execRow).e2 :=
    { input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_rd_eq := h_input_rd
      input_pc_eq := h_input_pc
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      m0_mult := by rfl
      m0_as := by rfl
      m1_mult := by rfl
      m1_as := by rfl
      m2_mult := by rfl
      m2_as := by rfl
      rd_idx := h_rd_idx }
  -- Delegate to the F4 fullSpec bridge.
  exact equiv_REMU_of_fullSpec_claimed_dead
    (binding i) remu_input r1 r2 rd (busSub trace binding i execRow)
    (mainOfTable trace.program trace.mainTable) i.val
    (remuArow trace binding i h_main_active h_main_op)
    pins h_match_primary promises arith_mem bounds
    h_full remainder_bound h_rs1_value h_rs2_value

end ZiskFv.Compliance
