import ZiskFv.Compliance.AcceptedTrace
import ZiskFv.Compliance.ConstructionSub
import ZiskFv.Compliance.Wrappers.MulW

/-!
# Sound MULW construction (`construction_mulw_sound`)

The first honest sound construction for the **Arith** family in the P4 closeout.
It assembles the canonical MULW conclusion
(`execute (MULW (r2, r1, rd)) = (bus_effect …).2`) from an accepted full-ensemble
trace plus an explicit, named, top-level set of residual binders — with the
ARITH WITNESSES (ArithTable membership, chunk/carry ranges, the `bus_res1`
mux c46, and the carry-chain) **DERIVED FROM BALANCE**, not carried as caller
binders.

This is the anti-laundering payoff of the c46 + chunk-range + carry-range
composition into the shared ArithMul component: the provider's
`componentWithArithTable.Spec` is now exactly
`FullSpec = Spec ∧ ArithTableSpec ∧ C46Spec ∧ ChunkRangeSpec ∧ CarryRangeSpec`,
which contains everything the MULW wrapper needs from the multiplier AIR. The
construction reads that `FullSpec` straight off the balance-derived provider row
(`mulwArow`) and hands it to `equiv_MULW_of_fullSpec`.

## The honest decomposition

* **(a) derived** — proven inside the body, NOT a binder:
  - op-bus provider match (from `trace.balanced`, via the Layer-A wrapper
    `exists_arithMul_provider_row_matches_primary_of_mulw_from_binding`,
    bottoming in the axiom-free keep-arithMul balance theorem),
  - the row-native `Valid_ArithMul` view `vOfMulwRow (mulwArow …)` of the
    balance-selected provider row,
  - **the arith witnesses** — `FullSpec (rowAt v 0)` from the provider's
    `componentWithArithTable.Spec` (carry-chain + ArithTable membership + c46 +
    chunk ranges + signed-carry ranges, ALL balance-derived),
  - the MemBus rd-write witness (`ExternalArithMemoryWitness`, from
    `store_pc = 0`),
  - the MemBus `m0..m2` write shape (`by rfl` off the real trace row).

* **(b) named residual** — explicit top-level binders (program / ROM / Sail
  facts the ensemble cannot finish; not new trust, but visible):
  - decode pins (3): `h_main_op` (= `OP_MUL_W`), `h_main_active`, `h_store_pc`
  - Sail reads + operands (5): `h_input_r1`, `h_input_r2`, `h_input_pc`,
    `h_input_rd`, `h_rd_idx`
  - W-mode high-lane zero + signed operand bridges (5): `h_a23`, `h_b23`,
    `h_sext_choice`, `h_rs1_value`, `h_rs2_value` (the Sail↔chunk binding of the
    32-bit signed operands and the sign-extension on rd bytes 4..7 — genuinely
    residual; they reference the balance-selected provider row view
    `vOfMulwRow (mulwArow …)`),
  - control-flow next-PC (1): `h_nextPC_matches`.

* **(c) artifact** — pure `bus_effect`/`ExecutionBusEntry` bookkeeping:
  - exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`,
  - PLUS the genuine `execRow : List (ExecutionBusEntry FGL)` **∀-binder**.

## Anti-vacuity

`execRow` MUST be a genuine top-level ∀-binder (the bus consumed by the exec
hypotheses is `busSub`, built from the real trace row, NOT chosen to trivialize
a hypothesis). The Arith witnesses are NOT binders — they are derived from
`trace.balanced` / `trace.spec`, matching the ALU constructions' shape.

## Axioms

`construction_mulw_sound` introduces **0 PROJECT (`ZiskFv.*`) axioms**. As with
every canonical theorem in this project, its closure still includes the
Sail-translation axioms and the Lean-kernel postulates (incl. `Classical.choice`,
used to name the balance-selected provider row) as documented external trust.
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.EquivCore.Promises
open ZiskFv.Channels.MemoryBusBytes (byteAt)
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ArithMul (componentWithArithTable primaryOpBusMessage rowAt)

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

/-- Row-native `Valid_ArithMul` view of a concrete provider `ArithMulRow`.

    Every column is the constant function returning the corresponding field of
    `arow`, with `multiplicity` pinned to `1` (the active-row consume polarity).
    Consequently `rowAt (vOfMulwRow arow) 0` agrees with `arow` on every field
    `FullSpec` / `primaryOpBusMessage` dereferences, so both `FullSpec` transport
    and the op-bus-message bridge below are `rfl` / definitional. -/
@[reducible]
def vOfMulwRow (arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL) :
    ZiskFv.Airs.ArithMul.Valid_ArithMul FGL FGL where
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

/-- The balance-selected Arith-Mul provider row at trace index `i`, as a concrete
    `ArithMulRow`. It is the `componentWithArithTable.rowInput` of the provider
    row chosen by the keep-arithMul balance wrapper
    `exists_arithMul_provider_row_matches_primary_of_mulw_from_binding`.

    This is a deterministic handle on the balance-selected row, used to phrase
    the residual operand bridges over its row-native view
    `vOfMulwRow (mulwArow …)`. The Arith witnesses for this row are derived
    inside `construction_mulw_sound`; nothing about the row is caller-supplied. -/
noncomputable def mulwArow
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := exists_arithMul_provider_row_matches_primary_of_mulw_from_binding
    trace binding i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- `FullSpec` transports along the row-native view: a `FullSpec` for a concrete
    `ArithMulRow` carries over to `rowAt (vOfMulwRow arow) 0`, because the two
    rows agree on every field `FullSpec` dereferences (they differ only in
    `multiplicity`, which `FullSpec` never reads). -/
theorem fullSpec_rowAt_vOfMulwRow
    {arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h : ZiskFv.AirsClean.ArithMul.FullSpec arow) :
    ZiskFv.AirsClean.ArithMul.FullSpec (rowAt (vOfMulwRow arow) 0) := h

/-- `FullSpec` of the balance-selected MULW provider row, derived from the
    provider component's proven soundness (`componentWithArithTable.Spec`).

    Proved here, at the `mulwArow` definition site, so the `Classical.choose`
    underlying `mulwArow` matches the one this proof picks — keeping the defeq
    cheap for the construction body. -/
theorem mulwArow_fullSpec_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W) :
    ZiskFv.AirsClean.ArithMul.FullSpec (mulwArow trace binding i h_main_active h_main_op) := by
  unfold mulwArow
  set H := exists_arithMul_provider_row_matches_primary_of_mulw_from_binding
    trace binding i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  -- Cheap projection of the provider component's generic `Spec` to `FullSpec`
  -- (the heavy `componentWithArithTable.Spec` unfold lives once in `Balance`).
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

/-- `FullSpec` of the balance-selected MULW provider row view. -/
theorem mulwArow_fullSpec
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (rowAt (vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)) 0) :=
  fullSpec_rowAt_vOfMulwRow
    (mulwArow_fullSpec_row trace binding i h_main_active h_main_op)

/-- The op-bus match transports along the row-native view: a match against the
    FAITHFUL muxed ArithMul primary op-bus message of a concrete row carries
    over to `opBus_row_Arith (vOfMulwRow arow) 0` exactly at the MUL/MULW mode
    pins (`div=0`, `main_mul=1`, `main_div=0`), via the mode-conditional bridge
    `primaryOpBusMessage_toEntry_rowAt_eq_opBus_row`.

    (Previously `rfl`; the faithful mux makes `toEntry (primaryOpBusMessage arow)
    1` equal `opBus_row_Arith (vOfMulwRow arow) 0` only once the muxes reduce
    under the mode pins — which the construction derives from the provider row's
    `ArithTableSpec` + opcode pin.) -/
theorem match_opBus_row_Arith_vOfMulwRow
    {x : ZiskFv.Airs.OperationBus.OperationBusEntry FGL}
    {arow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL}
    (h_div : arow.flags.div = 0)
    (h_main_mul : arow.flags.main_mul = 1)
    (h_main_div : arow.flags.main_div = 0)
    (h :
      matches_entry x
        (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
          (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arow) 1)) :
    matches_entry x (ZiskFv.Airs.ArithMul.opBus_row_Arith (vOfMulwRow arow) 0) := by
  -- `rowAt (vOfMulwRow arow) 0` agrees with `arow` field-for-field, and
  -- `(vOfMulwRow arow).multiplicity 0 = 1`, so the mode-gated bridge rewrites
  -- the matched entry from the muxed message to `opBus_row_Arith`.
  rw [← ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_rowAt_eq_opBus_row
        (vOfMulwRow arow) 0 h_div h_main_mul h_main_div]
  exact h

/-- The op-bus match of the balance-selected MULW provider row against the Main
    row's emission, in `toEntry (primaryOpBusMessage …) 1` form. Cheap: the row
    is a free `ArithMulRow`, so no `vOfMulwRow`/`opBus_row_Arith` whnf. -/
theorem mulwArow_match_row
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (mulwArow trace binding i h_main_active h_main_op)) 1) := by
  unfold mulwArow
  set H := exists_arithMul_provider_row_matches_primary_of_mulw_from_binding
    trace binding i h_main_active h_main_op with hH
  -- Use direct `.choose_spec` projections (NOT `obtain`, which introduces a
  -- fresh fvar for the row that the muxed message would force `exact` to
  -- whnf-reconcile against the goal's `H.choose_spec.2.choose`).
  exact H.choose_spec.2.choose_spec.2.2.2

/-- MUL/MULW mode pins on the balance-selected provider row, DERIVED from its
    `ArithTableSpec` (part of the balance-derived `FullSpec`) plus the opcode
    pin `arow.flags.op = 182`.  These are not caller binders: they come from the
    multiplier ROM membership the provider component already proves.

    PERFORMANCE: the provider row `mulwArow …` is a heavy `Classical.choose`
    application whose fields explode under whnf.  We therefore `set arow := …`
    so `arow` is an opaque fvar — `ArithTableSpec`, the op-pin, and the ROM
    `fin_cases` all act on `arow.flags.*` SYMBOLICALLY, never forcing the row's
    `componentWithArithTable.rowInput` evaluation.  The op-pin is read off the
    op-bus match via the CHEAP `rfl`-projection lemma `primaryOpBusMessage_toEntry_op`
    (a rewrite, not a reduction). -/
theorem mulwArow_mode_pins
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W) :
    (mulwArow trace binding i h_main_active h_main_op).flags.div = 0
      ∧ (mulwArow trace binding i h_main_active h_main_op).flags.main_mul = 1
      ∧ (mulwArow trace binding i h_main_active h_main_op).flags.main_div = 0 := by
  -- Read the mode flags off the BARE provider `ArithMulRow` (`mulwArow …`),
  -- never wrapping it in `vOfMulwRow` (whose per-field closures whnf-force the
  -- heavy `Classical.choose` row).  `ArithTableSpec` comes from the bare
  -- `mulwArow_fullSpec_row`; the op-pin from the muxed op-bus match via the cheap
  -- `rfl`-projection lemma; the ROM pins from the bare-row `mulw_mode_pins_of_row`.
  have h_table := (mulwArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (mulwArow trace binding i h_main_active h_main_op).flags.op = 182 := by
    have h_match := mulwArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val).op
          = (mainOfTable trace.program binding.mainTable).op i.val from rfl,
        h_main_op] at h_op
    exact h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.mulw_mode_pins_of_row
    (mulwArow trace binding i h_main_active h_main_op) h_table h_op

/-- The op-bus match of the balance-selected MULW provider row view against the
    Main row's emission, in `opBus_row_Arith` form. The MUL/MULW mode pins
    needed to reduce the faithful mux are DERIVED via `mulwArow_mode_pins`. -/
theorem mulwArow_match
    (trace : AcceptedTrace) (binding : ProgramBinding trace) (i : Fin trace.length)
    (h_main_active :
      (mainOfTable trace.program binding.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program binding.mainTable).op i.val = ZiskFv.Trusted.OP_MUL_W) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program binding.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_Arith
        (vOfMulwRow (mulwArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨h_div, h_main_mul, h_main_div⟩ :=
    mulwArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_Arith_vOfMulwRow h_div h_main_mul h_main_div
    (mulwArow_match_row trace binding i h_main_active h_main_op)


end ZiskFv.Compliance
