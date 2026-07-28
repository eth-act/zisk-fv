import ZiskFv.AirsClean.ArithMul.Bridge
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.Bits.Execution
import ZiskFv.Compliance.Defects
import ZiskFv.Compliance.Instantiation.ConcreteRowReductions

/-!
# Ordinary signed-DIV completed-component counterexample

This module pins an opcode-186 row accepted by the live completed Arith component.
It represents dividend `1`, divisor `-1`, quotient `+1`, and remainder `0`.
The physical remainder-bound consumer is balanced by an explicit static Binary
`LT_ABS_PN` provider.  The row is outside the existing equal-magnitude
`DivRemForge` boundary, but its quotient differs from Sail/RISC-V signed division.
-/

namespace ZiskFv.Regression.SignedDivOrdinaryCounterexample

open Goldilocks
open Air.Flat
open ZiskFv.Compliance.Instantiation

def arithRow : ZiskFv.AirsClean.ArithMul.ArithMulRow FGL where
  chunks := {
    a_0 := 1, a_1 := 0, a_2 := 0, a_3 := 0
    b_0 := 65535, b_1 := 65535, b_2 := 65535, b_3 := 65535
    c_0 := 1, c_1 := 0, c_2 := 0, c_3 := 0
    d_0 := 0, d_1 := 0, d_2 := 0, d_3 := 0
  }
  flags := {
    na := 0, nb := 1, nr := 0, np := 0
    sext := 0, m32 := 0, div := 1
    div_by_zero := 0, div_overflow := 0
    main_div := 1, main_mul := 0, signed := 1
    range_ab := 5, range_cd := 4, op := 186
    bus_res1 := 0, multiplicity := 1
  }
  carries := {
    carry_0 := -1, carry_1 := -1, carry_2 := -1, carry_3 := -1
    carry_4 := 0, carry_5 := 0, carry_6 := 0
    fab := -1, na_fb := 0, nb_fa := 1
    inv_sum_all_bs := (4 * (65535 : FGL))⁻¹
  }

private def indexedRangeIndex (block remainder : ℕ)
    (hBlock : block < 68) (hRemainder : remainder < 32768) :
    Fin ZiskFv.AirsClean.RangeTables.arithRangeTableLength :=
  ⟨block * 32768 + remainder, by
    simp [ZiskFv.AirsClean.RangeTables.arithRangeTableLength]
    omega⟩

def a1Index := indexedRangeIndex 38 0 (by decide) (by decide)
def b1Index := indexedRangeIndex 17 32767 (by decide) (by decide)
def c1Index := indexedRangeIndex 36 0 (by decide) (by decide)
def d1Index := indexedRangeIndex 14 0 (by decide) (by decide)
def a3Index := indexedRangeIndex 52 0 (by decide) (by decide)
def b3Index := indexedRangeIndex 63 32767 (by decide) (by decide)
def c3Index := indexedRangeIndex 51 0 (by decide) (by decide)
def d3Index := indexedRangeIndex 54 0 (by decide) (by decide)

theorem arithTableSpec : ZiskFv.AirsClean.ArithMul.ArithTableSpec arithRow := by
  refine ⟨⟨24, by decide⟩, ?_⟩
  norm_num [arithRow, ZiskFv.AirsClean.ArithMul.arithTableRow,
    ZiskFv.AirsClean.ArithTable.arithTable, ZiskFv.AirsClean.ArithTable.rows]

private theorem indexedSpec (block remainder rangeId value : ℕ)
    (hBlock : block < 68) (hRemainder : remainder < 32768)
    (hId : ZiskFv.AirsClean.RangeTables.arithRangeHalfBlockId block = rangeId)
    (hValue :
      ZiskFv.AirsClean.RangeTables.arithRangeChunkValue block remainder = value) :
    ZiskFv.AirsClean.RangeTables.arithRangeTable.Spec
      #v[(rangeId : FGL), (value : FGL)] := by
  have hChunk : block * 32768 + remainder < 2228224 := by omega
  have hDiv : (block * 32768 + remainder) / 32768 = block := by omega
  have hMod : (block * 32768 + remainder) % 32768 = remainder := by omega
  refine ⟨indexedRangeIndex block remainder hBlock hRemainder, ?_⟩
  simp [indexedRangeIndex, ZiskFv.AirsClean.RangeTables.arithRangeTableRow,
    ZiskFv.AirsClean.RangeTables.arithRangeChunkRows,
    ZiskFv.AirsClean.RangeTables.arithRangeHalfBlockSize, hChunk, hDiv, hMod,
    hId, hValue]

theorem indexedRangeSpec : ZiskFv.AirsClean.ArithMul.IndexedRangeSpec arithRow := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact indexedSpec 38 0 31 0 (by decide) (by decide) (by decide) (by decide)
  · exact indexedSpec 17 32767 14 65535 (by decide) (by decide) (by decide) (by decide)
  · exact indexedSpec 36 0 30 0 (by decide) (by decide) (by decide) (by decide)
  · exact indexedSpec 14 0 13 0 (by decide) (by decide) (by decide) (by decide)
  · simpa [arithRow] using
      indexedSpec 52 0 5 0 (by decide) (by decide) (by decide) (by decide)
  · exact indexedSpec 63 32767 22 65535 (by decide) (by decide) (by decide) (by decide)
  · simpa [arithRow] using
      indexedSpec 51 0 4 0 (by decide) (by decide) (by decide) (by decide)
  · exact indexedSpec 54 0 21 0 (by decide) (by decide) (by decide) (by decide)

theorem fullSpec : ZiskFv.AirsClean.ArithMul.FullSpec arithRow := by
  refine ⟨?_, arithTableSpec, ?_, ?_, ?_, indexedRangeSpec⟩
  · norm_num [ZiskFv.AirsClean.ArithMul.Spec, arithRow]
  · norm_num [ZiskFv.AirsClean.ArithMul.C46Spec, arithRow]
  · norm_num [ZiskFv.AirsClean.ArithMul.ChunkRangeSpec, arithRow]
  · norm_num [ZiskFv.AirsClean.ArithMul.CarryRangeSpec, arithRow]

theorem sharedDivBlockSpec :
    ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec arithRow := by
  have hDenominator : (262140 : FGL) ≠ 0 := by decide
  norm_num [ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec,
    ZiskFv.AirsClean.ArithMul.DivModeSpec,
    ZiskFv.AirsClean.ArithMul.DivBoundarySpec,
    ZiskFv.AirsClean.ArithMul.DivInverseSumSpec,
    ZiskFv.AirsClean.ArithMul.DivScopeSpec,
    ZiskFv.AirsClean.ArithMul.DivWModeSpec, arithRow]
  rw [inv_mul_cancel₀ hDenominator]
  ring

def arithEnv : Environment FGL :=
  Environment.fromInput arithRow (fun _ _ => #[])

theorem componentRowInput :
    ZiskFv.AirsClean.ArithMul.componentComplete.rowInput arithEnv = arithRow := by
  simp [arithEnv, Air.Flat.Component.rowInput,
    ProvableType.valueFromOffset_zero_fromInput_eq]

private theorem evalRowInput :
    Eval.eval arithEnv ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar =
      arithRow := by
  simpa only [Air.Flat.Component.rowInput, eval_varFromOffset_valueFromOffset] using
    componentRowInput

private theorem evalArithRow (env : Environment FGL)
    (row : ZiskFv.AirsClean.ArithMul.ArithMulRow (Expression FGL)) :
    Eval.eval env row = {
      chunks := Eval.eval env row.chunks
      flags := Eval.eval env row.flags
      carries := Eval.eval env row.carries
    } := by
  cases row
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go]

private theorem evalChunks (env : Environment FGL)
    (chunks : ZiskFv.AirsClean.ArithMul.ArithMulChunks (Expression FGL)) :
    Eval.eval env chunks = {
      a_0 := chunks.a_0.eval env, a_1 := chunks.a_1.eval env
      a_2 := chunks.a_2.eval env, a_3 := chunks.a_3.eval env
      b_0 := chunks.b_0.eval env, b_1 := chunks.b_1.eval env
      b_2 := chunks.b_2.eval env, b_3 := chunks.b_3.eval env
      c_0 := chunks.c_0.eval env, c_1 := chunks.c_1.eval env
      c_2 := chunks.c_2.eval env, c_3 := chunks.c_3.eval env
      d_0 := chunks.d_0.eval env, d_1 := chunks.d_1.eval env
      d_2 := chunks.d_2.eval env, d_3 := chunks.d_3.eval env
    } := by
  cases chunks
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

private theorem evalFlags (env : Environment FGL)
    (flags : ZiskFv.AirsClean.ArithMul.ArithMulFlags (Expression FGL)) :
    Eval.eval env flags = {
      na := flags.na.eval env, nb := flags.nb.eval env
      nr := flags.nr.eval env, np := flags.np.eval env
      sext := flags.sext.eval env, m32 := flags.m32.eval env
      div := flags.div.eval env, div_by_zero := flags.div_by_zero.eval env
      div_overflow := flags.div_overflow.eval env
      main_div := flags.main_div.eval env, main_mul := flags.main_mul.eval env
      signed := flags.signed.eval env, range_ab := flags.range_ab.eval env
      range_cd := flags.range_cd.eval env, op := flags.op.eval env
      bus_res1 := flags.bus_res1.eval env, multiplicity := flags.multiplicity.eval env
    } := by
  cases flags
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

private theorem evalCarries (env : Environment FGL)
    (carries : ZiskFv.AirsClean.ArithMul.ArithMulCarries (Expression FGL)) :
    Eval.eval env carries = {
      carry_0 := carries.carry_0.eval env, carry_1 := carries.carry_1.eval env
      carry_2 := carries.carry_2.eval env, carry_3 := carries.carry_3.eval env
      carry_4 := carries.carry_4.eval env, carry_5 := carries.carry_5.eval env
      carry_6 := carries.carry_6.eval env, fab := carries.fab.eval env
      na_fb := carries.na_fb.eval env, nb_fa := carries.nb_fa.eval env
      inv_sum_all_bs := carries.inv_sum_all_bs.eval env
    } := by
  cases carries
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

private theorem evalRowInputParts :
    Eval.eval arithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.chunks =
        arithRow.chunks ∧
    Eval.eval arithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.flags =
        arithRow.flags ∧
    Eval.eval arithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar.carries =
        arithRow.carries := by
  have h := evalRowInput
  rw [evalArithRow] at h
  injection h with hChunks hFlags hCarries
  exact ⟨hChunks, hFlags, hCarries⟩

theorem componentFullSpec :
    ZiskFv.AirsClean.ArithMul.componentComplete.Spec arithEnv := by
  rw [ZiskFv.AirsClean.ArithMul.componentComplete_spec]
  rw [componentRowInput]
  exact fullSpec

private theorem constraintsHold_append (left right : Operations FGL) :
    Operations.ConstraintsHold arithEnv (left ++ right) ↔
      Operations.ConstraintsHold arithEnv left ∧
        Operations.ConstraintsHold arithEnv right := by
  simp only [Operations.ConstraintsHold, Operations.constraints_append,
    Operations.lookups_append, List.mem_append, or_imp, forall_and]
  tauto

private theorem constraintsHold_bind {α β : Type} (first : Circuit FGL α)
    (next : α → Circuit FGL β) (offset : ℕ)
    (hFirst : Operations.ConstraintsHold arithEnv (first.operations offset))
    (hNext : Operations.ConstraintsHold arithEnv
      ((next (first.output offset)).operations (offset + first.localLength offset))) :
    Operations.ConstraintsHold arithEnv ((first >>= next).operations offset) := by
  rw [Circuit.bind_operations_eq, constraintsHold_append]
  exact ⟨hFirst, hNext⟩

private theorem constraintsHold_assertZero (expression : Expression FGL) (offset : ℕ)
    (h : expression.eval arithEnv = 0) :
    Operations.ConstraintsHold arithEnv ((assertZero expression).operations offset) := by
  simpa [Operations.ConstraintsHold, circuit_norm] using h

private theorem constraintsHold_interaction (interaction : Circuit FGL Unit) (offset : ℕ)
    (hNoConstraints : (interaction.operations offset).constraints = [])
    (hNoLookups : (interaction.operations offset).lookups = []) :
    Operations.ConstraintsHold arithEnv (interaction.operations offset) := by
  simp [Operations.ConstraintsHold, hNoConstraints, hNoLookups]

private theorem constraintsHold_staticLookup {Row : TypeMap} [ProvableType Row]
    (table : StaticTable FGL Row) (entry : Row (Expression FGL)) (offset : ℕ)
    (h : table.Spec (Eval.eval arithEnv entry)) :
    Operations.ConstraintsHold arithEnv
      ((lookup (Table.fromStatic table) entry).operations offset) := by
  have hContains : ∃ i, Eval.eval arithEnv entry = table.row i :=
    (table.contains_iff _).mpr h
  simpa [Operations.ConstraintsHold, circuit_norm, Lookup.Contains,
    Table.fromStatic, StaticTable.toTable, Table.toRaw] using hContains

private theorem expressionEvalConst (env : Environment FGL) (value : FGL) :
    Expression.eval env (Expression.const value) = value := rfl

private theorem mainConstraints (offset : ℕ) :
    Operations.ConstraintsHold arithEnv
      ((ZiskFv.AirsClean.ArithMul.main
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations offset) := by
  rcases evalRowInputParts with ⟨hChunks, hFlags, hCarries⟩
  rw [evalChunks] at hChunks
  rw [evalFlags] at hFlags
  rw [evalCarries] at hCarries
  injection hChunks with h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
    h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  injection hFlags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div0
    h_overflow h_mainDiv h_mainMul h_signed h_rangeAB h_rangeCD h_op h_busRes h_mult
  injection hCarries with h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6 h_fab
    h_nafb h_nbfa h_inv
  unfold ZiskFv.AirsClean.ArithMul.main
  repeat' apply constraintsHold_bind
  all_goals first
    | apply constraintsHold_assertZero
      simp only [Expression.eval, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
        h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np,
        h_sext, h_m32, h_div, h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed,
        h_rangeAB, h_rangeCD, h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3,
        h_cy4, h_cy5, h_cy6, h_fab, h_nafb, h_nbfa, h_inv]
      norm_num [arithRow]
    | apply constraintsHold_interaction <;> rfl

set_option maxRecDepth 2000 in
private theorem mainWithArithTableConstraints (offset : ℕ) :
    Operations.ConstraintsHold arithEnv
      ((ZiskFv.AirsClean.ArithMul.mainWithArithTable
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations offset) := by
  have hMain := mainConstraints offset
  have hRom := arithTableSpec
  rcases indexedRangeSpec with
    ⟨hIdxA1, hIdxB1, hIdxC1, hIdxD1, hIdxA3, hIdxB3, hIdxC3, hIdxD3⟩
  simp only [ZiskFv.AirsClean.ArithMul.ArithTableSpec,
    ZiskFv.AirsClean.ArithMul.arithTableRow, arithRow] at hRom
  simp only [arithRow] at hIdxA1 hIdxB1 hIdxC1 hIdxD1
  simp only [arithRow] at hIdxA3 hIdxB3 hIdxC3 hIdxD3
  norm_num at hIdxA1 hIdxB1 hIdxC1 hIdxD1 hIdxB3 hIdxD3
  rcases fullSpec.2.2.2.2.1 with
    ⟨hRangeCy0, hRangeCy1, hRangeCy2, hRangeCy3, hRangeCy4, hRangeCy5, hRangeCy6⟩
  rcases evalRowInputParts with ⟨hChunks, hFlags, hCarries⟩
  rw [evalChunks] at hChunks
  rw [evalFlags] at hFlags
  rw [evalCarries] at hCarries
  injection hChunks with h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
    h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  injection hFlags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div0
    h_overflow h_mainDiv h_mainMul h_signed h_rangeAB h_rangeCD h_op h_busRes h_mult
  injection hCarries with h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6 h_fab
    h_nafb h_nbfa h_inv
  unfold ZiskFv.AirsClean.ArithMul.mainWithArithTable
  apply constraintsHold_bind
  · exact hMain
  repeat' apply constraintsHold_bind
  next =>
    apply constraintsHold_assertZero
    simp only [Expression.eval, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
      h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np,
      h_sext, h_m32, h_div, h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed,
      h_rangeAB, h_rangeCD, h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3,
      h_cy4, h_cy5, h_cy6, h_fab, h_nafb, h_nbfa, h_inv]
    norm_num [arithRow]
  all_goals
    apply constraintsHold_staticLookup
    simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field,
      ProvableType.eval_fields, CircuitType.eval_expr, CircuitType.eval_var_field,
      Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      eval_add, expressionEvalConst,
      h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
      h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np, h_sext, h_m32, h_div,
      h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed, h_rangeAB, h_rangeCD,
      h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3, h_cy4, h_cy5, h_cy6,
      h_fab, h_nafb, h_nbfa, h_inv]
  next => exact hRom
  next => norm_num; exact hIdxA1
  next => norm_num; exact hIdxB1
  next => norm_num; exact hIdxC1
  next => norm_num; exact hIdxD1
  next => exact hIdxA3
  next => norm_num; exact hIdxB3
  next => exact hIdxC3
  next => norm_num; exact hIdxD3
  all_goals
    norm_num [ZiskFv.AirsClean.RangeTables.rangeTable16,
      ZiskFv.AirsClean.RangeTables.rangeStaticTable,
      ZiskFv.AirsClean.RangeTables.signedCarryRangeTable]

private theorem sharedMainConstraints (offset : ℕ) :
    Operations.ConstraintsHold arithEnv
      ((ZiskFv.AirsClean.ArithMul.sharedMainComplete
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations offset) := by
  have hMainWithArithTable := mainWithArithTableConstraints offset
  rcases evalRowInputParts with ⟨hChunks, hFlags, hCarries⟩
  rw [evalChunks] at hChunks
  rw [evalFlags] at hFlags
  rw [evalCarries] at hCarries
  injection hChunks with h_a0 h_a1 h_a2 h_a3 h_b0 h_b1 h_b2 h_b3
    h_c0 h_c1 h_c2 h_c3 h_d0 h_d1 h_d2 h_d3
  injection hFlags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div0
    h_overflow h_mainDiv h_mainMul h_signed h_rangeAB h_rangeCD h_op h_busRes h_mult
  injection hCarries with h_cy0 h_cy1 h_cy2 h_cy3 h_cy4 h_cy5 h_cy6 h_fab
    h_nafb h_nbfa h_inv
  unfold ZiskFv.AirsClean.ArithMul.sharedMainComplete
  apply constraintsHold_bind
  · exact hMainWithArithTable
  repeat' apply constraintsHold_bind
  all_goals first
    | apply constraintsHold_assertZero
      simp only [Expression.eval, h_a0, h_a1, h_a2, h_a3, h_b0, h_b1, h_b2, h_b3,
        h_c0, h_c1, h_c2, h_c3, h_d0, h_d1, h_d2, h_d3, h_na, h_nb, h_nr, h_np,
        h_sext, h_m32, h_div, h_div0, h_overflow, h_mainDiv, h_mainMul, h_signed,
        h_rangeAB, h_rangeCD, h_op, h_busRes, h_mult, h_cy0, h_cy1, h_cy2, h_cy3,
        h_cy4, h_cy5, h_cy6, h_fab, h_nafb, h_nbfa, h_inv]
      norm_num [arithRow]
  all_goals
    have hDenominator : (262140 : FGL) ≠ 0 := by decide
    rw [inv_mul_cancel₀ hDenominator]
    ring

theorem componentConstraints :
    ZiskFv.AirsClean.ArithMul.componentComplete.operations.ConstraintsHold arithEnv := by
  rw [Air.Flat.Component.constraintsHold_iff]
  change Operations.ConstraintsHold arithEnv
    ((ZiskFv.AirsClean.ArithMul.sharedMainCompleteWithRemainderBound
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations
        ZiskFv.AirsClean.ArithMul.componentComplete.rowOffset)
  unfold ZiskFv.AirsClean.ArithMul.sharedMainCompleteWithRemainderBound
  apply constraintsHold_bind
  · exact sharedMainConstraints _
  · apply constraintsHold_interaction <;> rfl

set_option maxHeartbeats 800000 in
theorem completedBlockFromLiveConstraints :
    ZiskFv.AirsClean.ArithMul.SharedDivBlockSpec arithRow := by
  have hRows :=
    (Air.Flat.Component.constraintsHold_iff
      (component := ZiskFv.AirsClean.ArithMul.componentComplete) arithEnv).mp
      componentConstraints
  have hComplete :
      Operations.ConstraintsHold arithEnv
        ((ZiskFv.AirsClean.ArithMul.sharedMainComplete
          ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations
            ZiskFv.AirsClean.ArithMul.componentComplete.rowOffset) := by
    change Operations.ConstraintsHold arithEnv
      ((ZiskFv.AirsClean.ArithMul.sharedMainCompleteWithRemainderBound
        ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar).operations
          ZiskFv.AirsClean.ArithMul.componentComplete.rowOffset) at hRows
    simpa [ZiskFv.AirsClean.ArithMul.sharedMainCompleteWithRemainderBound,
      Operations.ConstraintsHold] using hRows
  have hBlock :=
    ZiskFv.AirsClean.ArithMul.sharedDivBlockSpec_of_constraints
      ZiskFv.AirsClean.ArithMul.componentComplete.rowOffset arithEnv
      ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar hComplete
  have hEval :
      eval arithEnv ZiskFv.AirsClean.ArithMul.componentComplete.rowInputVar = arithRow := by
    exact ProvableType.eval_fromInput_varFromOffset_zero arithRow (fun _ _ => #[])
  rw [hEval] at hBlock
  exact hBlock

theorem primaryMessage :
    ZiskFv.AirsClean.ArithMul.primaryOpBusMessage arithRow = {
      op := 186
      a_lo := 1
      a_hi := 0
      b_lo := 4294967295
      b_hi := 4294967295
      c_lo := 1
      c_hi := 0
      flag := 0
      main_step := 0
      extended_arg := 0
      extra_args_0 := 0
    } := by
  norm_num [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage, arithRow]

def legacyRow : ZiskFv.Airs.ArithDiv.Valid_ArithDiv FGL FGL where
  cy_0 := fun _ => arithRow.carries.carry_0
  cy_1 := fun _ => arithRow.carries.carry_1
  cy_2 := fun _ => arithRow.carries.carry_2
  cy_3 := fun _ => arithRow.carries.carry_3
  cy_4 := fun _ => arithRow.carries.carry_4
  cy_5 := fun _ => arithRow.carries.carry_5
  cy_6 := fun _ => arithRow.carries.carry_6
  a_0 := fun _ => arithRow.chunks.a_0
  a_1 := fun _ => arithRow.chunks.a_1
  a_2 := fun _ => arithRow.chunks.a_2
  a_3 := fun _ => arithRow.chunks.a_3
  b_0 := fun _ => arithRow.chunks.b_0
  b_1 := fun _ => arithRow.chunks.b_1
  b_2 := fun _ => arithRow.chunks.b_2
  b_3 := fun _ => arithRow.chunks.b_3
  c_0 := fun _ => arithRow.chunks.c_0
  c_1 := fun _ => arithRow.chunks.c_1
  c_2 := fun _ => arithRow.chunks.c_2
  c_3 := fun _ => arithRow.chunks.c_3
  d_0 := fun _ => arithRow.chunks.d_0
  d_1 := fun _ => arithRow.chunks.d_1
  d_2 := fun _ => arithRow.chunks.d_2
  d_3 := fun _ => arithRow.chunks.d_3
  na := fun _ => arithRow.flags.na
  nb := fun _ => arithRow.flags.nb
  nr := fun _ => arithRow.flags.nr
  np := fun _ => arithRow.flags.np
  sext := fun _ => arithRow.flags.sext
  m32 := fun _ => arithRow.flags.m32
  div := fun _ => arithRow.flags.div
  fab := fun _ => arithRow.carries.fab
  na_fb := fun _ => arithRow.carries.na_fb
  nb_fa := fun _ => arithRow.carries.nb_fa
  main_div := fun _ => arithRow.flags.main_div
  main_mul := fun _ => arithRow.flags.main_mul
  signed := fun _ => arithRow.flags.signed
  div_by_zero := fun _ => arithRow.flags.div_by_zero
  div_overflow := fun _ => arithRow.flags.div_overflow
  inv_sum_all_bs := fun _ => arithRow.carries.inv_sum_all_bs
  op := fun _ => arithRow.flags.op
  bus_res1 := fun _ => arithRow.flags.bus_res1
  multiplicity := fun _ => arithRow.flags.multiplicity
  range_ab := fun _ => arithRow.flags.range_ab
  range_cd := fun _ => arithRow.flags.range_cd

def divisor : BitVec 64 := BitVec.ofInt 64 (-1)

theorem outsideDivRemForge :
    ¬ ZiskFv.Compliance.Defects.DivRemForge divisor legacyRow 0 := by
  simp [ZiskFv.Compliance.Defects.DivRemForge,
    ZiskFv.Compliance.Defects.signedRemainderInt,
    ZiskFv.PackedBitVec.MulNoWrap.packed4, divisor, legacyRow, arithRow]

private def firstProviderIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block5 + 196352, by
    norm_num [ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.block5,
      ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3,
      ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize]⟩

private def middleProviderIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block5 + 327424, by
    norm_num [ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.block5,
      ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3,
      ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize]⟩

private def lastProviderIndex : ZiskFv.AirsClean.Binary.BinaryTableIndex :=
  ⟨ZiskFv.AirsClean.BinaryTable.block5 + 392960, by
    norm_num [ZiskFv.AirsClean.BinaryTable.tableSize,
      ZiskFv.AirsClean.BinaryTable.block5,
      ZiskFv.AirsClean.BinaryTable.block4,
      ZiskFv.AirsClean.BinaryTable.block3,
      ZiskFv.AirsClean.BinaryTable.block2,
      ZiskFv.AirsClean.BinaryTable.block1,
      ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
      ZiskFv.AirsClean.BinaryTable.absBlockSize]⟩

def providerRow : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  ZiskFv.AirsClean.Binary.binaryStaticRowOf false false true false true
    firstProviderIndex
    middleProviderIndex middleProviderIndex middleProviderIndex
    middleProviderIndex middleProviderIndex middleProviderIndex
    lastProviderIndex

theorem providerProverAssumptions :
    ZiskFv.AirsClean.Binary.staticLookupComponent.circuit.ProverAssumptions
      providerRow emptyData (ProverHint.empty FGL) := by
  refine ⟨false, false, true, false, true,
    firstProviderIndex,
    middleProviderIndex, middleProviderIndex, middleProviderIndex,
    middleProviderIndex, middleProviderIndex, middleProviderIndex,
    lastProviderIndex, ?_⟩
  norm_num [providerRow, firstProviderIndex, middleProviderIndex, lastProviderIndex,
    ZiskFv.AirsClean.Binary.binaryStaticRowOf,
    ZiskFv.AirsClean.Binary.binaryRowOf,
    ZiskFv.AirsClean.Binary.binaryBOpOrSextOf,
    ZiskFv.AirsClean.Binary.binaryMode32AndCIsSignedOf,
    ZiskFv.AirsClean.Binary.binaryTableRow,
    ZiskFv.AirsClean.BinaryTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfBlock,
    ZiskFv.AirsClean.BinaryTable.OP_LT_ABS_PN,
    ZiskFv.AirsClean.BinaryTable.blockOfIndex,
    ZiskFv.AirsClean.BinaryTable.startOfBlock,
    ZiskFv.AirsClean.BinaryTable.relativeIndex,
    ZiskFv.AirsClean.BinaryTable.posIndOfIndex,
    ZiskFv.AirsClean.BinaryTable.cinOfIndex,
    ZiskFv.AirsClean.BinaryTable.coutOfIndex,
    ZiskFv.AirsClean.BinaryTable.resultIsAOfIndex,
    ZiskFv.AirsClean.BinaryTable.useFirstByteOfIndex,
    ZiskFv.AirsClean.BinaryTable.cIsSignedOfIndex,
    ZiskFv.AirsClean.BinaryTable.flagsOfIndex,
    ZiskFv.AirsClean.BinaryTable.cOfIndex,
    ZiskFv.AirsClean.BinaryTable.lowByte,
    ZiskFv.AirsClean.BinaryTable.highByte,
    ZiskFv.AirsClean.BinaryTable.coutLt,
    ZiskFv.AirsClean.BinaryTable.block6,
    ZiskFv.AirsClean.BinaryTable.block5,
    ZiskFv.AirsClean.BinaryTable.block4,
    ZiskFv.AirsClean.BinaryTable.block3,
    ZiskFv.AirsClean.BinaryTable.block2,
    ZiskFv.AirsClean.BinaryTable.block1,
    ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
    ZiskFv.AirsClean.BinaryTable.absBlockSize]

def providerTable : Table FGL := binarySingleRowTable providerRow

theorem providerTableConstraints : providerTable.Constraints :=
  binarySingleRowTable_constraints_of_proverAssumptions providerRow providerProverAssumptions

theorem providerMessage :
    ZiskFv.AirsClean.Binary.opBusMessage providerRow =
      ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage arithRow := by
  norm_num [providerRow, firstProviderIndex, middleProviderIndex, lastProviderIndex,
    ZiskFv.AirsClean.Binary.opBusMessage,
    ZiskFv.AirsClean.Binary.aLoValue,
    ZiskFv.AirsClean.Binary.aHiValue,
    ZiskFv.AirsClean.Binary.bLoValue,
    ZiskFv.AirsClean.Binary.bHiValue,
    ZiskFv.AirsClean.Binary.cLoValue,
    ZiskFv.AirsClean.Binary.cHiValue,
    ZiskFv.AirsClean.Binary.binaryStaticRowOf,
    ZiskFv.AirsClean.Binary.binaryRowOf,
    ZiskFv.AirsClean.Binary.binaryBOpOrSextOf,
    ZiskFv.AirsClean.Binary.binaryMode32AndCIsSignedOf,
    ZiskFv.AirsClean.Binary.binaryTableRow,
    ZiskFv.AirsClean.BinaryTable.rowOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfIndex,
    ZiskFv.AirsClean.BinaryTable.opOfBlock,
    ZiskFv.AirsClean.BinaryTable.OP_LT_ABS_PN,
    ZiskFv.AirsClean.BinaryTable.blockOfIndex,
    ZiskFv.AirsClean.BinaryTable.startOfBlock,
    ZiskFv.AirsClean.BinaryTable.relativeIndex,
    ZiskFv.AirsClean.BinaryTable.posIndOfIndex,
    ZiskFv.AirsClean.BinaryTable.cinOfIndex,
    ZiskFv.AirsClean.BinaryTable.coutOfIndex,
    ZiskFv.AirsClean.BinaryTable.resultIsAOfIndex,
    ZiskFv.AirsClean.BinaryTable.useFirstByteOfIndex,
    ZiskFv.AirsClean.BinaryTable.cIsSignedOfIndex,
    ZiskFv.AirsClean.BinaryTable.flagsOfIndex,
    ZiskFv.AirsClean.BinaryTable.cOfIndex,
    ZiskFv.AirsClean.BinaryTable.lowByte,
    ZiskFv.AirsClean.BinaryTable.highByte,
    ZiskFv.AirsClean.BinaryTable.coutLt,
    ZiskFv.AirsClean.BinaryTable.block6,
    ZiskFv.AirsClean.BinaryTable.block5,
    ZiskFv.AirsClean.BinaryTable.block4,
    ZiskFv.AirsClean.BinaryTable.block3,
    ZiskFv.AirsClean.BinaryTable.block2,
    ZiskFv.AirsClean.BinaryTable.block1,
    ZiskFv.AirsClean.BinaryTable.minMaxBlockSize,
    ZiskFv.AirsClean.BinaryTable.absBlockSize,
    ZiskFv.AirsClean.ArithMul.remainderBoundOpBusMessage, arithRow]

theorem remainderConsumerMultiplicity :
    -(arithRow.flags.div * (1 - arithRow.flags.div_by_zero)) = (-1 : FGL) := by
  norm_num [arithRow]

def physicalQuotient : BitVec 64 :=
  BitVec.ofNat 64
    (ZiskFv.PackedBitVec.MulNoWrap.packed4
      arithRow.chunks.a_0.val arithRow.chunks.a_1.val
      arithRow.chunks.a_2.val arithRow.chunks.a_3.val)

theorem physicalQuotient_is_one : physicalQuotient = 1#64 := by
  decide

theorem sailQuotient_is_neg_one :
    (execute_DIV_REM_pure (1#64) divisor .DRS).1 = divisor := by
  decide

theorem physicalQuotient_ne_sail :
    physicalQuotient ≠ (execute_DIV_REM_pure (1#64) divisor .DRS).1 := by
  rw [physicalQuotient_is_one, sailQuotient_is_neg_one]
  decide

end ZiskFv.Regression.SignedDivOrdinaryCounterexample
