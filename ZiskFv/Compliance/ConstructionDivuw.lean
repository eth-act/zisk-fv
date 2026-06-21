import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.ConstructionDivu
import ZiskFv.EquivCore.Divuw
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithDiv.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.Div
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Bits.PackedBitVec.MulNoWrap

/-!
# Sound DIVUW construction (`construction_divuw_sound`)

Unsigned RV64M **DIVUW** (`OP_DIVU_W = 188`, W-mode `m32 = 1`), the W-mode
sibling of DIVU — exactly as MULW relates to a 64-bit multiply.  The Arith
provider witnesses (ArithTable membership, chunk ranges, signed-carry ranges,
c46, carry-chain) are **DERIVED FROM BALANCE** via the SHARED ArithMul provider
component's lookup-aware `componentWithArithTable.Spec = FullSpec`, not carried
as caller binders.

## Why the shared ArithMul provider (not ArithDiv)

`ArithDiv.component` carries NO operation-bus interactions in the full ensemble
(`arithDiv_table_interactionsWith_opBus_nil`): its `circuit.channels = []`.  The
DIVUW Main op-bus emission is therefore balanced by the SHARED ArithMul provider
(`componentWithArithTable`), whose `FullSpec` covers div rows too.  The muxed
primary op-bus message, at the DIVUW mode pins (`div = 1`, `main_div = 1`,
`main_mul = 0` — all uniform for op 188), reduces to the div quotient-lane
message `opBus_row_ArithDiv`.  These three mux selectors are the SAME as DIVU's,
so the DIVU-mode op-bus bridge `match_opBus_row_ArithDiv_vOfDivuRow` (reused
from `ConstructionDivu`) applies verbatim — `m32` plays no role in the mux.

## The carry-range subtlety (vs MULW)

`EquivCore.Divuw.equiv_DIVUW` demands the *unsigned* carry bound
`cy_i.val < 131072 = 2^17`.  Balance supplies only `FullSpec`'s `CarryRangeSpec`
— the **signed disjunction** `< 983041 ∨ ≥ p - 983040`.  The genuine Euclidean
carries (`quotient · divisor`) reach `~3·2^16 > 2^17`, so the tight `< 131072`
bound is NOT balance-constructible (same as DIVU / MULHU).  This module
therefore does NOT route through `equiv_DIVUW`.  Instead it derives the looser
balance-constructible bound `< 983041` (via `unsigned_carry_step_nat`, reused
from `ConstructionMulhu`) and reconstructs the rd write value through the
loose-bound DIVUW W-mode write-value path `h_rd_val_mdru_divuw_loose`,
replicating `equiv_DIVUW`'s sail + `bus_effect` tail otherwise.

## The W-mode deltas (vs DIVU)

DIVUW is `m32 = 1`; the result is the *sign-extended low-32-bit quotient*.  The
high half of the bus result comes from `bus_res1 = sext · 0xFFFF_FFFF` (PIL
constraint 46 at `m32 = 1`), i.e. bytes 4..7 are `0x00` or `0xFF`.

* `h_b23` (`b_2 = b_3 = 0`) and `h_c23` (`c_2 = c_3 = 0`) are DERIVED inside the
  body from the W-mode op-bus hi-lane projection `(1 - m32) · m.* = …`
  collapsing to `0 = …` at `m32 = 1` (via `arith_chunk_pair_eq_zero_of_m32_one`)
  — NOT residual binders.
* `h_byte_lo` (bytes 0..3 pack `a_0 + a_1·65536`, the W quotient low half) is
  DERIVED from the op-bus c-lane match — NOT a binder.
* `h_sext_choice` (the SEXT_00 / SEXT_FF disjunction on bytes 4..7, tied to the
  quotient top bit) is the ONE W-mode bus-encoding residual, exactly as the
  canonical `equiv_DIVUW` and `Wrappers/Divuw` carry it (class #4, bus
  encoding — the same trust class as MULW / ADDW).  The arith table does not
  uniformly pin `sext` across the op-188 rows, so this cannot be derived from
  `ArithTableSpec`.

## The remainder bound is RESIDUAL, not balance-derived

`equiv_DIVUW` needs `ArithDivRemainderBoundWitness` — the `|d| < b` LTU check
from `arith.pil:274`.  This is the ArithDiv op-bus *consumer*
(`assumes_operation`) edge matched against a Binary LTU provider row.  Because
`ArithDiv.component` emits no op-bus in the ensemble, this consume edge is a
finished-channel SELF-EDGE that is **not composed into the ensemble** — so it is
NOT balance-derivable.  It is carried as the single explicit residual binder
`remainder_bound`, exactly as DIVU.

## Residual binder shape

`construction_divuw_sound` carries exactly DIVU's residual shape — decode pins +
Sail reads + operand bridges (W-form, `extractLsb 31 0`) + exec artifacts +
`execRow` + nextPC + the single `remainder_bound` — PLUS the ONE W-mode
bus-encoding residual `h_sext_choice` (irreducible; same trust class as the
canonical `equiv_DIVUW`).  NO arith-witness binders.

## Axioms

`construction_divuw_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**.  Its
closure carries `Lean.ofReduceBool` / `Lean.trustCompiler` (native_decide)
INHERITED from the canonical `equiv_DIVUW` path (already has it; NOT new —
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

The W-mode chain (op 188, `m32 = 1`) Euclidean chunk identity is the SAME as
DIVU's: the carry-chain constraints 31–38 do not reference `m32`.  We re-derive
them here over `vOfDivuRow` (reused from `ConstructionDivu`) at the unsigned mode
pins `na = nb = np = nr = 0`, `div = 1` (hence `fab = 1`, `na_fb = nb_fa = 0`). -/

open ZiskFv.Airs.ArithMul in


/-! ## Phase 3 — balance-selected DIVUW provider row + transports -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a DIVUW
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the DIVUW
    keep-arithMul balance wrapper
    `exists_arithMul_provider_row_matches_primary_of_divuw_from_binding`.
    Mirrors `divuArow`. -/
noncomputable def divuwArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := exists_arithMul_provider_row_matches_primary_of_divuw_from_binding
    trace binding i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected DIVUW provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem divuwArow_fullSpec_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (divuwArow trace binding i h_main_active h_main_op) := by
  unfold divuwArow
  set H := exists_arithMul_provider_row_matches_primary_of_divuw_from_binding
    trace binding i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- The op-bus match of the balance-selected DIVUW provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form. -/
theorem divuwArow_match_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (divuwArow trace binding i h_main_active h_main_op)) 1) := by
  unfold divuwArow
  set H := exists_arithMul_provider_row_matches_primary_of_divuw_from_binding
    trace binding i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- DIVUW mode pins on the balance-selected provider row, DERIVED from its
    `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 188`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `divuw_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem divuwArow_mode_pins
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W) :
    (divuwArow trace binding i h_main_active h_main_op).flags.na = 0
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.nb = 0
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.np = 0
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.nr = 0
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.m32 = 1
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.div = 1
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.main_div = 1
      ∧ (divuwArow trace binding i h_main_active h_main_op).flags.main_mul = 0 := by
  have h_table := (divuwArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (divuwArow trace binding i h_main_active h_main_op).flags.op = 188 := by
    have h_match := divuwArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val).op
          = (mainOfTable trace.program binding.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_DIVU_W] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.divuw_mode_pins_of_row
    (divuwArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected DIVUW provider row view against the
    Main row's emission, in `opBus_row_ArithDiv` form.  The DIVU-mode mux
    selectors (`div = 1`, `main_div = 1`, `main_mul = 0`) needed to reduce the
    faithful mux are DERIVED via `divuwArow_mode_pins` (they are `m32`-agnostic,
    so the DIVU-mode bridge `match_opBus_row_ArithDiv_vOfDivuRow` applies). -/
theorem divuwArow_match
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_DIVU_W) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv
        (vOfDivuRow (divuwArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨_, _, _, _, _, h_div, h_main_div, h_main_mul⟩ :=
    divuwArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithDiv_vOfDivuRow h_div h_main_div h_main_mul
    (divuwArow_match_row trace binding i h_main_active h_main_op)

/-! ## Phase 4 — F4 `FullSpec` discharge bridge for DIVUW -/

open ZiskFv.Airs.ArithDiv in
open ZiskFv.EquivCore.Promises in

/-! ## Phase 5 — sound DIVUW construction -/


end ZiskFv.Compliance
