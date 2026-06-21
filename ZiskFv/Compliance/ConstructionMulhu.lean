import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.ConstructionMulw
import ZiskFv.EquivCore.MulHU
import ZiskFv.EquivCore.Promises.ArithHelpers
import ZiskFv.EquivCore.Bridge.Arith
import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.Airs.Arith.BusRes1
import ZiskFv.Bits.PackedBitVec.MulNoWrap
import ZiskFv.Bits.PackedBitVec.Extensions

/-!
# Sound MULHU construction (`construction_mulhu_sound`)

Unsigned high-half RV64M MULHU (`OP_MULUH = 177`), mirroring the MULW
construction (`ConstructionMulw.lean`).  The Arith provider witnesses
(ArithTable membership, chunk ranges, signed-carry ranges, c46, carry-chain)
are **DERIVED FROM BALANCE** via the provider component's lookup-aware
`componentWithArithTable.Spec = FullSpec`, not carried as caller binders.

## The carry-range subtlety (vs MULW)

`EquivCore.MulHU.equiv_MULHU` demands the *unsigned* carry-range bound
`cy_i.val < 131072 = 2^17`.  Balance supplies only `FullSpec`'s
`CarryRangeSpec` — the **signed disjunction** `cy_i.val < 983041 ∨
GL_prime - 983040 ≤ cy_i.val` (because `mainWithArithTable` ranges every
carry through `signedCarryRangeTable`).  The genuine 4×4 unsigned-multiply
carries can reach `~3·2^16 > 2^17`, so the tight `< 131072` bound is NOT
satisfiable from real balance data.

This module therefore does NOT route through `equiv_MULHU`.  Instead it
derives the looser, balance-constructible bound `cy_i.val < 983041` (via
`unsigned_carry_step` below) — which is fully sufficient for the no-wrap
chunk → ℕ → high-half product reconstruction — and reconstructs the rd
write value through a loose-bound copy of the unsigned write-value path
(`mulhu_h_rd_val_of_loose`), mirroring `equiv_MULHU`'s body otherwise.

No new trust: the carry chain, ROM membership, `bus_res1` mux, and the
range bounds all come from the provider component's proven soundness via
`FullSpec`, not from fresh per-opcode promises.  `construction_mulhu_sound`
introduces **0 PROJECT (`ZiskFv.*`) axioms**.
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

/-! ## Phase 1 — balance-constructible unsigned carry bound + loose write-value path -/


/-! ### Loose-bound FGL → ℕ chunk lifts (carry bound `< 983041`)

Copies of `ZiskFv.PackedBitVec.MulNoWrap.fgl_chunk_lift_*` with the carry
bound relaxed from `< 131072` to the balance-constructible `< 983041`.  The
no-wrap argument is unchanged: every chunk equation's two sides stay below
`GL_prime` (LHS ≤ `4·(2^16-1)^2 + 983040 < 2^35`; RHS `≤ 2^16 + 983040·2^16 <
2^36`).  Each lift discharges via the additive `NoWrap.fgl_eq_to_nat_eq`. -/


open ZiskFv.Airs.ArithMul in

open ZiskFv.Airs.ArithMul in

open ZiskFv.PackedBitVec.Extensions in

/-! ## Phase 2 — F4 `FullSpec` discharge bridge for MULHU -/

open ZiskFv.Airs.ArithMul in
open ZiskFv.EquivCore.Promises in

/-! ## Phase 3 — sound MULHU construction -/

/-- The balance-selected Arith-Mul provider row at trace index `i` for a MULHU
    operation, as a concrete `ArithMulRow`.  It is the
    `componentWithArithTable.rowInput` of the provider row chosen by the MULHU
    keep-arithMul balance wrapper
    `exists_arithMul_provider_row_matches_secondary_of_mulhu_from_binding`.
    Mirrors `mulwArow`. -/
noncomputable def mulhuArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := exists_arithMul_provider_row_matches_secondary_of_mulhu_from_binding
    trace binding i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` of the balance-selected MULHU provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`). -/
theorem mulhuArow_fullSpec_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    ZiskFv.AirsClean.ArithMul.FullSpec (mulhuArow trace binding i h_main_active h_main_op) := by
  unfold mulhuArow
  set H := exists_arithMul_provider_row_matches_secondary_of_mulhu_from_binding
    trace binding i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- `FullSpec` of the balance-selected MULHU provider row view. -/
theorem mulhuArow_fullSpec
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (rowAt (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0) :=
  fullSpec_rowAt_vOfMulwRow
    (mulhuArow_fullSpec_row trace binding i h_main_active h_main_op)

/-- The op-bus match transports along the row-native view at the MULHU secondary
    mode pins (`div = 0`, `main_mul = 0`, `main_div = 0`): a match against the
    FAITHFUL muxed primary message of a concrete row carries over to
    `opBus_row_ArithMulSecondary (vOfMulwRow arow) 0`, via the MULHU-mode bridge
    `primaryOpBusMessage_toEntry_rowAt_eq_opBus_row_secondary`. -/
theorem match_opBus_row_ArithMulSecondary_vOfMulwRow
    {x : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_div : arow.flags.div = 0)
    (h_main_mul : arow.flags.main_mul = 0)
    (h_main_div : arow.flags.main_div = 0)
    (h :
      matches_entry x
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1)) :
    matches_entry x (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary (vOfMulwRow arow) 0) := by
  rw [← ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_rowAt_eq_opBus_row_secondary
        (vOfMulwRow arow) 0 h_div h_main_mul h_main_div]
  exact h

/-- The op-bus match of the balance-selected MULHU provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form (cheap: free
    `ArithMulRow`, no `vOfMulwRow`/`opBus_row_*` whnf). -/
theorem mulhuArow_match_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (mulhuArow trace binding i h_main_active h_main_op)) 1) := by
  unfold mulhuArow
  set H := exists_arithMul_provider_row_matches_secondary_of_mulhu_from_binding
    trace binding i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

/-- MULHU secondary mode pins on the balance-selected provider row, DERIVED from
    its `ArithTableSpec` (part of `FullSpec`) plus the opcode pin
    `arow.flags.op = 177`.  These are not caller binders.  Reads the mode flags
    off the BARE provider `ArithMulRow` via `mulhu_mode_pins_of_row`, never
    forcing the heavy `Classical.choose` row's whnf. -/
theorem mulhuArow_mode_pins
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    (mulhuArow trace binding i h_main_active h_main_op).flags.div = 0
      ∧ (mulhuArow trace binding i h_main_active h_main_op).flags.main_mul = 0
      ∧ (mulhuArow trace binding i h_main_active h_main_op).flags.main_div = 0 := by
  have h_table := (mulhuArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (mulhuArow trace binding i h_main_active h_main_op).flags.op = 177 := by
    have h_match := mulhuArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val).op
          = (mainOfTable trace.program binding.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_MULUH] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.mulhu_mode_pins_of_row
    (mulhuArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected MULHU provider row view against the
    Main row's emission, in `opBus_row_ArithMulSecondary` form.  The MULHU mode
    pins needed to reduce the faithful mux are DERIVED via `mulhuArow_mode_pins`. -/
theorem mulhuArow_match
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MULUH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
        (vOfMulwRow (mulhuArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨h_div, h_main_mul, h_main_div⟩ :=
    mulhuArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithMulSecondary_vOfMulwRow h_div h_main_mul h_main_div
    (mulhuArow_match_row trace binding i h_main_active h_main_op)


end ZiskFv.Compliance
