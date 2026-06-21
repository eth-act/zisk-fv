import ZiskFv.Compliance.AcceptedTrace
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


/-! ## Phase 3 — balance-selected REMUW provider row + transports -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a REMUW
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the REMUW
    keep-arithMul balance wrapper
    `exists_arithMul_provider_row_matches_primary_of_remuw_from_binding`.
    Mirrors `remuArow` / `divuwArow`. -/
noncomputable def remuwArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
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
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
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
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
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
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
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
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
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

/-! ## Phase 5 — sound REMUW construction -/


end ZiskFv.Compliance
