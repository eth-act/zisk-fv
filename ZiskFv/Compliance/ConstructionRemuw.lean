import ZiskFv.Compliance.ProgramBinding.Wrappers
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.Compliance.ConstructionRemu
import ZiskFv.EquivCore.Remuw
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Bits.PackedBitVec.MulNoWrap

/-!
# Sound REMUW construction (`construction_remuw_sound`)

Unsigned RV64M **REMUW** (`OP_REMU_W = 189`, W-mode `m32 = 1`), the W-mode
sibling of REMU — exactly as DIVUW relates to DIVU.  REMUW consumes the
**secondary** remainder lane (`main_div = 0`, `main_mul = 0`, like REMU) at the
W width (`m32 = 1`, like DIVUW).  The Arith provider witnesses (ArithTable
membership, chunk ranges, signed-carry ranges, c46, carry-chain) are **DERIVED
FROM BALANCE** via the SHARED ArithMul provider component's lookup-aware
`componentWithArithTable.Spec = FullSpec`, not carried as caller binders.

## Why the shared ArithMul provider (not ArithDiv)

`ArithDiv.component` carries NO operation-bus interactions in the full ensemble
(`arithDiv_table_interactionsWith_opBus_nil`): its `circuit.channels = []`.  The
REMUW Main op-bus emission is therefore balanced by the SHARED ArithMul provider
(`componentWithArithTable`), whose `FullSpec` covers div rows too.  At the REMUW
mode pins (`div = 1`, `main_div = 0`, `main_mul = 0`; `m32 = 1` plays no role in
the mux) the muxed primary op-bus message's `c_lo` lane collapses to the
remainder low half `d_0 + d_1·2^16`, so the muxed message reduces to the div
remainder-lane message `opBus_row_ArithDivSecondary` (the SAME REMU secondary
bridge `match_opBus_row_ArithDivSecondary_vOfDivuRow`, reused verbatim — `m32` is
not a mux selector).

## The carry-range subtlety (vs MULW)

`EquivCore.Remuw.equiv_REMUW` demands the *unsigned* carry bound
`cy_i.val < 131072 = 2^17`.  Balance supplies only `FullSpec`'s `CarryRangeSpec`
— the **signed disjunction** `< 983041 ∨ ≥ p - 983040`.  The genuine Euclidean
carries (`quotient · divisor`) reach `~3·2^16 > 2^17`, so the tight `< 131072`
bound is NOT balance-constructible (same as DIVU / DIVUW / MULHU).  This module
therefore does NOT route through `equiv_REMUW`.  Instead it derives the looser
balance-constructible bound `< 983041` (via `unsigned_carry_step_nat`, reused
from `ConstructionMulhu`) and reconstructs the rd write value through the
loose-bound REMUW W-mode write-value path `h_rd_val_mdru_remuw_loose`,
replicating `equiv_REMUW`'s sail + `bus_effect` tail otherwise.

## The W-mode deltas (vs REMU)

REMUW is `m32 = 1`; the result is the *sign-extended low-32-bit remainder*.  The
high half of the bus result comes from the sign-extension byte pattern (bytes
4..7 are `0x00` or `0xFF`), tied to the remainder top bit — NOT the
`d_2 + d_3·2^16` chunk pack that REMU (the non-W remainder lane) uses.

* `h_b23` (`b_2 = b_3 = 0`) and `h_c23` (`c_2 = c_3 = 0`) are residual binders,
  mirroring the canonical `equiv_REMUW`'s `h_b23` / `h_c23` (the divisor and
  dividend high chunks are zero in W-mode; `m32` is not an op-bus field, so these
  are not balance-derivable here).
* `h_byte_lo` (bytes 0..3 pack `d_0 + d_1·65536`, the W remainder low half) is
  DERIVED from the op-bus secondary c-lane match — NOT a binder.
* `h_d23` (`d_2 = d_3 = 0`) is DERIVED inside the body from the W-mode remainder
  bound (`arith_div_remainder_bound_unsigned_w`).
* `h_sext_choice` (the SEXT_00 / SEXT_FF disjunction on bytes 4..7, tied to the
  remainder top bit) is the ONE W-mode bus-encoding residual, exactly as the
  canonical `equiv_REMUW` and `Wrappers/Remuw` carry it (class #4, bus encoding —
  the same trust class as MULW / ADDW / DIVUW).

## The remainder bound is RESIDUAL, not balance-derived

`equiv_REMUW` needs `ArithDivRemainderBoundWitness` — the `|d| < b` LTU check
from `arith.pil:274`.  This is the ArithDiv op-bus *consumer*
(`assumes_operation`) edge matched against a Binary LTU provider row.  Because
`ArithDiv.component` emits no op-bus in the ensemble, this consume edge is a
finished-channel SELF-EDGE that is **not composed into the ensemble** — so it is
NOT balance-derivable.  It is carried as the single explicit residual binder
`remainder_bound`, exactly as REMU / DIVUW.

## Axioms

`construction_remuw_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.  Its
closure carries `Lean.ofReduceBool` / `Lean.trustCompiler` (native_decide)
INHERITED from the canonical `equiv_REMUW` path (already has it; NOT new —
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

/-! ## Phase 2 — balance-derived W-mode div-Euclidean chunk equations + loose carry bounds

The REMUW W-mode chain (op 189, `m32 = 1`) Euclidean chunk identity is the SAME
as DIVU's / REMU's: the carry-chain constraints 31–38 do not reference `m32`,
`main_div`, or `main_mul` (they share the `div` flag).  We re-derive them here
over `vOfDivuRow` (reused from `ConstructionDivu`) at the unsigned mode pins
`na = nb = np = nr = 0`, `div = 1` (hence `fab = 1`, `na_fb = nb_fa = 0`) — the
`ConstructionRemu` versions are `private`, so (as DIVUW does) we keep local
copies here. -/

open ZiskFv.Airs.ArithMul in
/-- **Mode-pinned REMUW Euclidean chunk equations.** Identical to DIVU's
    `divu_chain_eqs` — the carry-chain constraints 31–38 are
    `m32`/`main_div`/`main_mul`-independent, so the W-mode secondary-lane chain
    is the same low Euclidean form. -/
private lemma remuw_chain_eqs_claimed_dead
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (h_chain : mul_carry_chain_holds (vOfMulwRow arow) 0)
    (h_na : arow.flags.na = 0) (h_nb : arow.flags.nb = 0)
    (h_np : arow.flags.np = 0) (h_nr : arow.flags.nr = 0)
    (h_div : arow.flags.div = 1) :
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
             vOfMulwRow, h_na, h_nb, h_np, h_nr, h_div, h_fab, h_nafb, h_nbfa,
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

/-- **Balance-constructible REMUW unsigned carry bounds.** Identical to DIVU's
    `divu_carry_bounds`: derive the looser unsigned-side carry bounds
    `cy_i.val < 983041` via `unsigned_carry_step_nat` (reused from
    `ConstructionMulhu`). -/
private lemma remuw_carry_bounds_claimed_dead
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

/-! ## Phase 3 — balance-selected REMUW provider row + transports -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a REMUW
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the REMUW
    keep-arithMul balance wrapper
    `exists_arithMul_provider_row_matches_primary_of_remuw_from_binding`.
    Mirrors `remuArow` / `divuwArow`. -/
noncomputable def remuwArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := exists_arithMul_provider_row_matches_primary_of_remuw_from_binding
    trace binding i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected REMUW provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem remuwArow_fullSpec_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (remuwArow trace binding i h_main_active h_main_op) := by
  unfold remuwArow
  set H := exists_arithMul_provider_row_matches_primary_of_remuw_from_binding
    trace binding i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- The op-bus match of the balance-selected REMUW provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form. -/
theorem remuwArow_match_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (remuwArow trace binding i h_main_active h_main_op)) 1) := by
  unfold remuwArow
  set H := exists_arithMul_provider_row_matches_primary_of_remuw_from_binding
    trace binding i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- REMUW mode pins on the balance-selected provider row, DERIVED from its
    `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 189`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `remuw_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem remuwArow_mode_pins
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W) :
    (remuwArow trace binding i h_main_active h_main_op).flags.na = 0
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.nb = 0
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.np = 0
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.nr = 0
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.m32 = 1
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.div = 1
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.main_div = 0
      ∧ (remuwArow trace binding i h_main_active h_main_op).flags.main_mul = 0 := by
  have h_table := (remuwArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (remuwArow trace binding i h_main_active h_main_op).flags.op = 189 := by
    have h_match := remuwArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val).op
          = (mainOfTable trace.program binding.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_REMU_W] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.remuw_mode_pins_of_row
    (remuwArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected REMUW provider row view against the
    Main row's emission, in `opBus_row_ArithDivSecondary` form.  The REMU-mode
    mux selectors (`div = 1`, `main_div = 0`, `main_mul = 0`) needed to reduce
    the faithful mux are DERIVED via `remuwArow_mode_pins` (they are
    `m32`-agnostic, so the REMU secondary bridge
    `match_opBus_row_ArithDivSecondary_vOfDivuRow` applies verbatim). -/
theorem remuwArow_match
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary
        (vOfDivuRow (remuwArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨_, _, _, _, _, h_div, h_main_div, h_main_mul⟩ :=
    remuwArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithDivSecondary_vOfDivuRow h_div h_main_div h_main_mul
    (remuwArow_match_row trace binding i h_main_active h_main_op)

/-! ## Phase 4 — F4 `FullSpec` discharge bridge for REMUW -/

open ZiskFv.Airs.ArithDiv in
open ZiskFv.EquivCore.Promises in
/-- **F4 extraction bridge for `equiv_REMUW`.**  Mirror of `equiv_REMU_of_fullSpec`
    for the W-mode (`m32 = 1`) sibling.  The four lookup-aware Arith witness
    records are replaced by the single `FullSpec arow` hypothesis (the SHARED
    ArithMul provider's `componentWithArithTable.Spec`), with the ArithDiv-view
    facts read off the same row through `vOfDivuRow arow`.

    Like REMU / DIVUW, this derives the looser balance bound `< 983041` (via
    `remuw_carry_bounds`) and reconstructs the rd write value through the loose
    W-mode write-value path `h_rd_val_mdru_remuw_loose`, replicating
    `equiv_REMUW`'s sail + `bus_effect` tail.

    The low-remainder byte match `h_byte_lo` is DERIVED inside the body from the
    op-bus secondary c-lane projection.  The W-mode high-lane zeros `h_b23` /
    `h_c23`, the `remainder_bound`, and `h_sext_choice` are the explicit residual
    binders — exactly the W-mode route/provenance obligations the canonical
    `equiv_REMUW` carries (the `m32` flag is not an op-bus field, so the
    high-lane zeros are not balance-derivable here). -/
lemma equiv_REMUW_of_fullSpec_claimed_dead
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (remuw_input : PureSpec.RemuwInput)
    (r1 r2 rd : regidx)
    (bus : ZiskFv.Compliance.BusRows)
    (m : Valid_Main FGL FGL) (r_main : ℕ)
    (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL)
    (pins : ZiskFv.Compliance.MainRowPins m r_main 1 OP_REMU_W)
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary (vOfDivuRow arow) 0))
    (promises : ZiskFv.EquivCore.Promises.RTypePromises
        state remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        r1 r2 rd bus.exec_row bus.e0 bus.e1 bus.e2)
    (arith_mem : ZiskFv.Compliance.ExternalArithMemoryWitness m r_main bus.e2)
    (bounds : ZiskFv.Compliance.ByteBounds bus.e2)
    (h_full_spec : ZiskFv.AirsClean.ArithMul.FullSpec arow)
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness (vOfDivuRow arow) 0)
    -- W-mode high-lane zeros (CIRCUIT-CONSTRAINT / bus W-pin): the divisor and
    -- dividend high chunks are zero in W-mode.  Residual, mirroring the
    -- canonical `equiv_REMUW`'s `h_b23` / `h_c23`.
    (h_b23 : (arow.chunks.b_2).val = 0 ∧ (arow.chunks.b_3).val = 0)
    (h_c23 : (arow.chunks.c_2).val = 0 ∧ (arow.chunks.c_3).val = 0)
    -- The W-mode bus-encoding residual (class #4): SEXT_00 / SEXT_FF on
    -- bytes 4..7, tied to the remainder top bit.  Phrased over `arow.chunks.d`.
    (h_sext_choice :
      (((byteAt bus.e2 4).val = 0 ∧ (byteAt bus.e2 5).val = 0
          ∧ (byteAt bus.e2 6).val = 0 ∧ (byteAt bus.e2 7).val = 0)
        ∧ (arow.chunks.d_0).val + (arow.chunks.d_1).val * 65536 < 2147483648)
      ∨ (((byteAt bus.e2 4).val = 255 ∧ (byteAt bus.e2 5).val = 255
          ∧ (byteAt bus.e2 6).val = 255 ∧ (byteAt bus.e2 7).val = 255)
        ∧ (arow.chunks.d_0).val + (arow.chunks.d_1).val * 65536 ≥ 2147483648))
    -- Operand bridges (W form: low 32 bits; genuinely residual).
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
      = (arow.chunks.c_0).val + (arow.chunks.c_1).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
      = (arow.chunks.b_0).val + (arow.chunks.b_1).val * 65536) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) state
      = (bus_effect bus.exec_row [bus.e0, bus.e1, bus.e2] state).2 := by
  obtain ⟨h_spec, h_arith_table, h_c46, h_chunk_ranges_spec, h_carry_ranges_spec⟩ :=
    h_full_spec
  obtain ⟨exec_row, e0, e1, e2⟩ := bus
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bounds
  obtain ⟨_h_main_active, h_main_op_remuw⟩ := pins
  obtain ⟨h_input_r1, h_input_r2, h_input_rd, h_input_pc,
          h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches,
          h_m0_mult, h_m0_as, h_m1_mult, h_m1_as, h_m2_mult, h_m2_as,
          h_rd_idx⟩ := promises
  -- ============ DERIVE arith-side opcode literal ============
  have h_op_eq := arith_div_secondary_op_eq h_match_primary
  have h_op_arith_remuw : (vOfDivuRow arow).op 0 = 189 := by
    rw [h_op_eq, h_main_op_remuw]; simp [OP_REMU_W]
  have h_op_arow : arow.flags.op = 189 := h_op_arith_remuw
  -- ============ REMUW mode pins, DERIVED from the bare-row ArithTableSpec =====
  obtain ⟨h_na_arow, h_nb_arow, h_np_arow, h_nr_arow, h_m32_arow,
          h_div_arow, h_main_div_arow, h_main_mul_arow⟩ :=
    ZiskFv.AirsClean.ArithTableProjections.Mul.remuw_mode_pins_of_row arow h_arith_table h_op_arow
  have h_nb : (vOfDivuRow arow).nb 0 = 0 := h_nb_arow
  have h_nr : (vOfDivuRow arow).nr 0 = 0 := h_nr_arow
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
  -- ============ Op-bus secondary c-lane projection (for the byte-lo match) ====
  obtain ⟨_h_a_lo_eq_FGL, _h_a_hi_eq_FGL, _h_b_lo_eq_FGL, _h_b_hi_eq_FGL,
          h_c0_eq_FGL, _h_c1_eq_FGL⟩ :=
    arith_div_secondary_projections h_match_primary
  -- ============ Mode-pinned div-Euclidean chunk equations (W-mode) ===========
  have heqs := remuw_chain_eqs_claimed_dead arow h_spec h_na_arow h_nb_arow h_np_arow h_nr_arow
    h_div_arow
  obtain ⟨hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩ := heqs
  -- ============ Balance-constructible LOOSE unsigned carry bounds ============
  obtain ⟨hcy0, hcy1, hcy2, hcy3, hcy4, hcy5, hcy6⟩ :=
    remuw_carry_bounds_claimed_dead arow h_chunk_ranges_spec h_carry_ranges_signed
      ⟨hC31, hC32, hC33, hC34, hC35, hC36, hC37, hC38⟩
  -- ============ Remainder bound (RESIDUAL): d < b in low-32 chunk form =======
  obtain ⟨h_d23, h_d_lt_b_arith⟩ :=
    ZiskFv.EquivCore.Bridge.Arith.arith_div_remainder_bound_unsigned_w
      remainder_bound h_chunk_ranges_spec h_nr h_nb h_b23
  have h_d23' : (arow.chunks.d_2).val = 0 ∧ (arow.chunks.d_3).val = 0 := h_d23
  have h_d_lt_b :
      (arow.chunks.d_0).val + (arow.chunks.d_1).val * 65536
        < (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat := by
    rw [h_rs2_value]
    exact h_d_lt_b_arith
  have h_op2_ne : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat ≠ 0 := by
    intro h_zero
    have hlt := h_d_lt_b
    rw [h_zero] at hlt
    omega
  -- ============ DISCHARGE h_byte_lo (remainder low d-lanes) ===================
  have h_bundle := arith_mem.c_lane_vals
  have h_byte_lo_to_c0 : (byteAt e2 0).val + (byteAt e2 1).val * 256
      + (byteAt e2 2).val * 65536 + (byteAt e2 3).val * 16777216
      = (m.c_0 r_main).val := by
    have h_e2_lo_bound : e2.value_0.val < 4294967296 := by
      rw [← h_bundle.1, h_c0_eq_FGL]
      rw [arith_h_pair_lift _ _ h_d0_lt h_d1_lt]
      omega
    rw [ZiskFv.Channels.MemoryBusBytes.byteAt_lo_val_sum_eq e2 h_e2_lo_bound, h_bundle.1]
  have h_byte_lo :
      (byteAt e2 0).val + (byteAt e2 1).val * 256 + (byteAt e2 2).val * 65536
        + (byteAt e2 3).val * 16777216
      = (arow.chunks.d_0).val + (arow.chunks.d_1).val * 65536 := by
    have := arith_byte_lane_eq_of_match h_byte_lo_to_c0 h_c0_eq_FGL h_d0_lt h_d1_lt
    simpa [vOfDivuRow] using this
  -- ============ DISCHARGE rd-write value via the LOOSE W-mode write-value path
  have h_rd_val :=
    ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.h_rd_val_mdru_remuw_loose
      remuw_input.r1_val remuw_input.r2_val e2
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
      (by
        -- h_a23 : a_2 = a_3 = 0.  In W-mode the quotient is the low-32 value;
        -- the high chunks are forced zero by the Euclidean identity collapse
        -- (b_2=b_3=c_2=c_3=d_2=d_3=0).
        have h_packed_nat :
            ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.a_0).val
                (arow.chunks.a_1).val (arow.chunks.a_2).val (arow.chunks.a_3).val
              * ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.b_0).val
                  (arow.chunks.b_1).val (arow.chunks.b_2).val (arow.chunks.b_3).val
              + ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.d_0).val
                  (arow.chunks.d_1).val (arow.chunks.d_2).val (arow.chunks.d_3).val
            = ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.c_0).val
                (arow.chunks.c_1).val (arow.chunks.c_2).val (arow.chunks.c_3).val :=
          ZiskFv.EquivCore.WriteValueProofs.MulDivRemUnsigned.fgl_div_unsigned_chunks_to_nat_identity_loose
            (arow.chunks.a_0) (arow.chunks.a_1) (arow.chunks.a_2) (arow.chunks.a_3)
            (arow.chunks.b_0) (arow.chunks.b_1) (arow.chunks.b_2) (arow.chunks.b_3)
            (arow.chunks.c_0) (arow.chunks.c_1) (arow.chunks.c_2) (arow.chunks.c_3)
            (arow.chunks.d_0) (arow.chunks.d_1) (arow.chunks.d_2) (arow.chunks.d_3)
            (arow.carries.carry_0) (arow.carries.carry_1) (arow.carries.carry_2)
            (arow.carries.carry_3) (arow.carries.carry_4) (arow.carries.carry_5)
            (arow.carries.carry_6)
            h_a0_lt h_a1_lt h_a2_lt h_a3_lt h_b0_lt h_b1_lt h_b2_lt h_b3_lt
            h_c0_lt h_c1_lt h_c2_lt h_c3_lt h_d0_lt h_d1_lt h_d2_lt h_d3_lt
            hcy0 hcy1 hcy2 hcy3 hcy4 hcy5 hcy6
            hC31 hC32 hC33 hC34 hC35 hC36 hC37 hC38
        obtain ⟨hb2, hb3⟩ := h_b23
        obtain ⟨hc2, hc3⟩ := h_c23
        obtain ⟨hd2, hd3⟩ := h_d23'
        have h_c32_lt : (arow.chunks.c_0).val + (arow.chunks.c_1).val * 65536 < 4294967296 := by
          have : (arow.chunks.c_1).val * 65536 ≤ 65535 * 65536 :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have h_b32_pos : 0 < (arow.chunks.b_0).val + (arow.chunks.b_1).val * 65536 := by
          have h_ne : (arow.chunks.b_0).val + (arow.chunks.b_1).val * 65536 ≠ 0 := by
            intro h_zero
            apply h_op2_ne
            rw [h_rs2_value, h_zero]
          omega
        have h_a_packed_lt :
            ZiskFv.PackedBitVec.MulNoWrap.packed4 (arow.chunks.a_0).val
              (arow.chunks.a_1).val (arow.chunks.a_2).val (arow.chunks.a_3).val < 4294967296 := by
          unfold ZiskFv.PackedBitVec.MulNoWrap.packed4 at h_packed_nat
          rw [hb2, hb3, hc2, hc3, hd2, hd3] at h_packed_nat
          nlinarith
        unfold ZiskFv.PackedBitVec.MulNoWrap.packed4 at h_a_packed_lt
        constructor <;> omega)
      h_b23 h_d23' h_c23 h_byte_lo h_sext_choice h_rs1_value h_rs2_value h_op2_ne h_d_lt_b
  -- ============ Replicate `equiv_REMUW`'s sail + bus_effect tail =============
  rw [ZiskFv.EquivCore.Remuw.equiv_REMUW_sail state remuw_input r1 r2 rd
        h_input_r1 h_input_r2 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.Bus.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  simp only [PureSpec.execute_DIVREM_remuw_pure, h_rd_idx]
  rw [← h_rd_val]
  split_ifs with h_rd_zero
  · simp only [bind, pure, EStateM.bind, EStateM.pure]
  · simp only [bind, pure, EStateM.bind, EStateM.pure]

/-! ## Phase 5 — sound REMUW construction -/

/-- **Sound REMUW construction:** from the accepted trace + honest residual
    binders, conclude the canonical
    `execute (REMW (r2, r1, rd, true)) = (bus_effect …).2`.

    The Arith provider witnesses (ArithTable membership, chunk ranges, signed
    carry ranges, c46, carry-chain) are DERIVED inside the body from
    `trace.channels_balanced` / `trace.spec_holds` via the SHARED ArithMul provider's
    lookup-aware `componentWithArithTable.Spec = FullSpec`, NOT supplied as
    binders.  The low-remainder byte match is also DERIVED.

    The THREE non-balance-derived residuals are `remainder_bound`
    (`ArithDivRemainderBoundWitness`: the `|d| < b` LTU consumer self-edge from
    `arith.pil:274`, absent from the ensemble), `h_b23` / `h_c23` (the W-mode
    high-lane zeros), and `h_sext_choice` (the W-mode SEXT_00/SEXT_FF bus
    encoding on bytes 4..7, class #4 — the same residuals the canonical
    `equiv_REMUW` carries). -/
theorem construction_remuw_sound_claimed_dead
    (trace : AcceptedTrace)
    (binding : ProgramBinding trace)
    (i : Fin trace.numInstructions)
    (remuw_input : PureSpec.RemuwInput)
    (r1 r2 rd : regidx)
    -- (b) decode pins
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU_W)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_store_pc :
      (mainOfTable trace.program binding.mainTable).store_pc i.val = 0)
    -- (b) Sail reads + operands
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding.stateAt i)
        = EStateM.Result.ok remuw_input.r1_val (binding.stateAt i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding.stateAt i)
        = EStateM.Result.ok remuw_input.r2_val (binding.stateAt i))
    (h_input_pc : (binding.stateAt i).regs.get? Register.PC = .some remuw_input.PC)
    (h_input_rd : remuw_input.rd = regidx_to_fin rd)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace binding i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace binding i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace binding i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace binding i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC)
    (h_rd_idx :
      remuw_input.rd =
        Transpiler.wrap_to_regidx (busSub trace binding i execRow).e2.ptr)
    -- (c) byte range bounds on the rd-write entry
    (bounds : ZiskFv.Compliance.ByteBounds (busSub trace binding i execRow).e2)
    -- (b) RESIDUAL: remainder-bound witness (the ArithDiv `assumes_operation`
    -- LTU consumer edge is a finished-channel self-edge absent from the
    -- ensemble).
    (remainder_bound :
      ZiskFv.EquivCore.Bridge.Arith.ArithDivRemainderBoundWitness
        (vOfDivuRow (remuwArow trace binding i h_main_active h_main_op)) 0)
    -- (b) W-mode RESIDUAL high-lane zeros (CIRCUIT-CONSTRAINT / bus W-pin),
    -- mirroring the canonical `equiv_REMUW`'s `h_b23` / `h_c23`.
    (h_b23 :
      ((remuwArow trace binding i h_main_active h_main_op).chunks.b_2).val = 0
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.b_3).val = 0)
    (h_c23 :
      ((remuwArow trace binding i h_main_active h_main_op).chunks.c_2).val = 0
        ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.c_3).val = 0)
    -- (b) W-mode RESIDUAL: SEXT_00/SEXT_FF bus encoding on bytes 4..7 (class #4,
    -- same trust class as the canonical `equiv_REMUW` / MULW / ADDW).
    (h_sext_choice :
      ((((byteAt (busSub trace binding i execRow).e2 4).val = 0
            ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 0
            ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 0
            ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 0)
          ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
              + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
                < 2147483648)
        ∨ (((byteAt (busSub trace binding i execRow).e2 4).val = 255
            ∧ (byteAt (busSub trace binding i execRow).e2 5).val = 255
            ∧ (byteAt (busSub trace binding i execRow).e2 6).val = 255
            ∧ (byteAt (busSub trace binding i execRow).e2 7).val = 255)
          ∧ ((remuwArow trace binding i h_main_active h_main_op).chunks.d_0).val
              + ((remuwArow trace binding i h_main_active h_main_op).chunks.d_1).val * 65536
                ≥ 2147483648)))
    -- (b) operand bridges (Sail↔chunk binding of the W-form low-32 operands;
    -- genuinely residual, phrased over the balance-selected provider row).
    (h_rs1_value : (Sail.BitVec.extractLsb remuw_input.r1_val 31 0).toNat
      = ((remuwArow trace binding i h_main_active h_main_op).chunks.c_0).val
          + ((remuwArow trace binding i h_main_active h_main_op).chunks.c_1).val * 65536)
    (h_rs2_value : (Sail.BitVec.extractLsb remuw_input.r2_val 31 0).toNat
      = ((remuwArow trace binding i h_main_active h_main_op).chunks.b_0).val
          + ((remuwArow trace binding i h_main_active h_main_op).chunks.b_1).val * 65536) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.REMW (r2, r1, rd, true))) (binding.stateAt i)
      = (bus_effect (busSub trace binding i execRow).exec_row
          [ (busSub trace binding i execRow).e0
          , (busSub trace binding i execRow).e1
          , (busSub trace binding i execRow).e2 ] (binding.stateAt i)).2 := by
  -- (a) Arith witnesses derived from balance: FullSpec.
  have h_full :
      ZiskFv.AirsClean.ArithMul.FullSpec
        (remuwArow trace binding i h_main_active h_main_op) :=
    remuwArow_fullSpec_row trace binding i h_main_active h_main_op
  -- (a) primary op-bus match against `opBus_row_ArithDivSecondary (vOfDivuRow …) 0`.
  have h_match_primary :
      matches_entry (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
        (ZiskFv.Airs.ArithDiv.opBus_row_ArithDivSecondary
          (vOfDivuRow (remuwArow trace binding i h_main_active h_main_op)) 0) :=
    remuwArow_match trace binding i h_main_active h_main_op
  -- decode pins bundle
  let pins :
      ZiskFv.Compliance.MainRowPins
        (mainOfTable trace.program binding.mainTable) i.val 1 OP_REMU_W :=
    ⟨h_main_active, h_main_op⟩
  -- (a) Main rd-write memory witness, from `store_pc = 0`.
  have h_core_store_pc :
      (mainRowWithRomSub trace binding i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace binding i).core =
          ZiskFv.AirsClean.Main.rowAt (mainOfTable trace.program binding.mainTable) i.val := by
      have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
      simpa [mainRowWithRomSub,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness
        (mainOfTable trace.program binding.mainTable) i.val
        (busSub trace binding i execRow).e2 :=
    { row := mainRowWithRomSub trace binding i
      row_eq := by
        have := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program binding.mainTable ⟨i.val, binding.mainTable_index i⟩
        simpa [mainRowWithRomSub,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get] using this.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  -- promises bundle: Sail reads + exec artifacts as binders; MemBus shape by rfl.
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding.stateAt i) remuw_input.r1_val remuw_input.r2_val remuw_input.rd remuw_input.PC
      (PureSpec.execute_DIVREM_remuw_pure remuw_input).nextPC
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
  exact equiv_REMUW_of_fullSpec_claimed_dead
    (binding.stateAt i) remuw_input r1 r2 rd (busSub trace binding i execRow)
    (mainOfTable trace.program binding.mainTable) i.val
    (remuwArow trace binding i h_main_active h_main_op)
    pins h_match_primary promises arith_mem bounds
    h_full remainder_bound h_b23 h_c23 h_sext_choice h_rs1_value h_rs2_value

end ZiskFv.Compliance
