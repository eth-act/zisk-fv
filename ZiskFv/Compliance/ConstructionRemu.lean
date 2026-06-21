import ZiskFv.Compliance.AcceptedTrace
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
    `exists_arithMul_provider_row_matches_primary_of_remu_from_binding`.
    Mirrors `divuArow`. -/
noncomputable def remuArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := exists_arithMul_provider_row_matches_primary_of_remu_from_binding
    trace binding i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected REMU provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem remuArow_fullSpec_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (remuArow trace binding i h_main_active h_main_op) := by
  unfold remuArow
  set H := exists_arithMul_provider_row_matches_primary_of_remu_from_binding
    trace binding i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- The op-bus match of the balance-selected REMU provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form. -/
theorem remuArow_match_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (remuArow trace binding i h_main_active h_main_op)) 1) := by
  unfold remuArow
  set H := exists_arithMul_provider_row_matches_primary_of_remu_from_binding
    trace binding i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- REMU mode pins on the balance-selected provider row, DERIVED from its
    `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 185`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `remu_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem remuArow_mode_pins
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
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
        show (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val).op
          = (mainOfTable trace.program binding.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_REMU] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.remu_mode_pins_of_row
    (remuArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected REMU provider row view against the
    Main row's emission, in `opBus_row_ArithDivSecondary` form.  The REMU mode
    pins needed to reduce the faithful mux are DERIVED via `remuArow_mode_pins`. -/
theorem remuArow_match
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_REMU) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
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


/-! ## Phase 4 — F4 `FullSpec` discharge bridge for REMU -/

open ZiskFv.Airs.ArithDiv in
open ZiskFv.EquivCore.Promises in

/-! ## Phase 5 — sound REMU construction -/


end ZiskFv.Compliance
