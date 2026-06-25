import ZiskFv.AirsClean.FullEnsemble
import ZiskFv.AirsClean.ArithTableProjections
import ZiskFv.AirsClean.Binary.Bridge
import ZiskFv.AirsClean.BinaryAdd.Bridge
import ZiskFv.AirsClean.BinaryExtension.Bridge
import ZiskFv.AirsClean.Mem.Bridge
import ZiskFv.AirsClean.Mem.TraceSpec
import ZiskFv.AirsClean.FullEnsemble.Balance.Classification
import ZiskFv.AirsClean.FullEnsemble.Balance.CounterpartClassification
import ZiskFv.AirsClean.FullEnsemble.Balance.RowExtraction
import ZiskFv.AirsClean.FullEnsemble.Balance.OpBusRowBridges
import ZiskFv.AirsClean.FullEnsemble.Balance.MemRowReplayProjections

namespace ZiskFv.AirsClean.FullEnsemble

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.AirsClean.ZiskInstructionRom (Program)
open ZiskFv.AirsClean.BinaryExtension (shiftStaticLookupComponent)

/-- Zero row for totalizing concrete Main table projections. -/
def zeroMainRowWithRom : ZiskFv.AirsClean.Main.MainRowWithRom FGL where
  core := {
    a_0 := 0
    a_1 := 0
    b_0 := 0
    b_1 := 0
    c_0 := 0
    c_1 := 0
    flag := 0
    pc := 0
    is_external_op := 0
    op := 0
    m32 := 0
    ind_width := 0
    set_pc := 0
    jmp_offset1 := 0
    jmp_offset2 := 0
    store_pc := 0
    im_high_degree_2 := 0
    segment_l1 := 0 }
  rom := {
    a_offset_imm0 := 0
    a_imm1 := 0
    b_offset_imm0 := 0
    b_imm1 := 0
    store_offset := 0
    a_src_imm := 0
    a_src_mem := 0
    is_precompiled := 0
    b_src_imm := 0
    b_src_mem := 0
    store_mem := 0
    store_ind := 0
    b_src_ind := 0
    a_src_reg := 0
    b_src_reg := 0
    store_reg := 0
    addr0 := 0
    addr1 := 0
    addr2 := 0
    main_step := 0 }

/-- Project row `row` of a concrete Clean Main table to its unified Main+ROM
    row input. Out-of-range rows use `zeroMainRowWithRom` only to keep the
    named-column view total. -/
@[reducible]
def mainTableRowAtOrZero
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar
  else
    zeroMainRowWithRom

/-- Named-column Main view obtained from the concrete Clean unified Main table.

    **Semireducible (not `@[reducible]`).** Marking it reducible used to make
    elaboration whnf-expand this 16-field `Valid_Main` structure instance over
    the heavy noncomputable `mainTable`, which tips into a non-terminating
    `whnf` once `AcceptedZiskTrace` is parameterized by `numInstructions`
    (issue #144). Consumers rewrite via the `@[simp]` projection lemmas below
    (`mainOfTable_op`, `mainOfTable_is_external_op`, …) instead of unfolding the
    instance directly. -/
def mainOfTable
    {length : ℕ}
    (program : Program length)
    (table : Table FGL) :
    ZiskFv.Airs.Main.Valid_Main FGL FGL where
  a_0 := fun row => (mainTableRowAtOrZero program table row).core.a_0
  a_1 := fun row => (mainTableRowAtOrZero program table row).core.a_1
  b_0 := fun row => (mainTableRowAtOrZero program table row).core.b_0
  b_1 := fun row => (mainTableRowAtOrZero program table row).core.b_1
  c_0 := fun row => (mainTableRowAtOrZero program table row).core.c_0
  c_1 := fun row => (mainTableRowAtOrZero program table row).core.c_1
  flag := fun row => (mainTableRowAtOrZero program table row).core.flag
  pc := fun row => (mainTableRowAtOrZero program table row).core.pc
  is_external_op := fun row => (mainTableRowAtOrZero program table row).core.is_external_op
  op := fun row => (mainTableRowAtOrZero program table row).core.op
  b_src_imm := fun row => (mainTableRowAtOrZero program table row).rom.b_src_imm
  b_src_mem := fun row => (mainTableRowAtOrZero program table row).rom.b_src_mem
  b_src_ind := fun row => (mainTableRowAtOrZero program table row).rom.b_src_ind
  b_src_reg := fun row => (mainTableRowAtOrZero program table row).rom.b_src_reg
  m32 := fun row => (mainTableRowAtOrZero program table row).core.m32
  ind_width := fun row => (mainTableRowAtOrZero program table row).core.ind_width
  set_pc := fun row => (mainTableRowAtOrZero program table row).core.set_pc
  jmp_offset1 := fun row => (mainTableRowAtOrZero program table row).core.jmp_offset1
  jmp_offset2 := fun row => (mainTableRowAtOrZero program table row).core.jmp_offset2
  store_pc := fun row => (mainTableRowAtOrZero program table row).core.store_pc
  im_high_degree_2 := fun row => (mainTableRowAtOrZero program table row).core.im_high_degree_2
  segment_l1 := fun row => (mainTableRowAtOrZero program table row).core.segment_l1

section MainOfTableProjections

variable {length : ℕ} (program : Program length) (table : Table FGL)

/-! ### `mainOfTable` field projections

Since `mainOfTable` is no longer `@[reducible]`, every `Valid_Main` field
access on it goes through these `@[simp]` lemmas instead of whnf-unfolding the
16-field structure instance. Each is a definitional `rfl`. -/

@[simp] theorem mainOfTable_a_0 :
    (mainOfTable program table).a_0 =
      fun row => (mainTableRowAtOrZero program table row).core.a_0 := rfl
@[simp] theorem mainOfTable_a_1 :
    (mainOfTable program table).a_1 =
      fun row => (mainTableRowAtOrZero program table row).core.a_1 := rfl
@[simp] theorem mainOfTable_b_0 :
    (mainOfTable program table).b_0 =
      fun row => (mainTableRowAtOrZero program table row).core.b_0 := rfl
@[simp] theorem mainOfTable_b_1 :
    (mainOfTable program table).b_1 =
      fun row => (mainTableRowAtOrZero program table row).core.b_1 := rfl
@[simp] theorem mainOfTable_c_0 :
    (mainOfTable program table).c_0 =
      fun row => (mainTableRowAtOrZero program table row).core.c_0 := rfl
@[simp] theorem mainOfTable_c_1 :
    (mainOfTable program table).c_1 =
      fun row => (mainTableRowAtOrZero program table row).core.c_1 := rfl
@[simp] theorem mainOfTable_flag :
    (mainOfTable program table).flag =
      fun row => (mainTableRowAtOrZero program table row).core.flag := rfl
@[simp] theorem mainOfTable_pc :
    (mainOfTable program table).pc =
      fun row => (mainTableRowAtOrZero program table row).core.pc := rfl
@[simp] theorem mainOfTable_is_external_op :
    (mainOfTable program table).is_external_op =
      fun row => (mainTableRowAtOrZero program table row).core.is_external_op := rfl
@[simp] theorem mainOfTable_op :
    (mainOfTable program table).op =
      fun row => (mainTableRowAtOrZero program table row).core.op := rfl
@[simp] theorem mainOfTable_b_src_imm :
    (mainOfTable program table).b_src_imm =
      fun row => (mainTableRowAtOrZero program table row).rom.b_src_imm := rfl
@[simp] theorem mainOfTable_b_src_mem :
    (mainOfTable program table).b_src_mem =
      fun row => (mainTableRowAtOrZero program table row).rom.b_src_mem := rfl
@[simp] theorem mainOfTable_b_src_ind :
    (mainOfTable program table).b_src_ind =
      fun row => (mainTableRowAtOrZero program table row).rom.b_src_ind := rfl
@[simp] theorem mainOfTable_b_src_reg :
    (mainOfTable program table).b_src_reg =
      fun row => (mainTableRowAtOrZero program table row).rom.b_src_reg := rfl
@[simp] theorem mainOfTable_m32 :
    (mainOfTable program table).m32 =
      fun row => (mainTableRowAtOrZero program table row).core.m32 := rfl
@[simp] theorem mainOfTable_ind_width :
    (mainOfTable program table).ind_width =
      fun row => (mainTableRowAtOrZero program table row).core.ind_width := rfl
@[simp] theorem mainOfTable_set_pc :
    (mainOfTable program table).set_pc =
      fun row => (mainTableRowAtOrZero program table row).core.set_pc := rfl
@[simp] theorem mainOfTable_jmp_offset1 :
    (mainOfTable program table).jmp_offset1 =
      fun row => (mainTableRowAtOrZero program table row).core.jmp_offset1 := rfl
@[simp] theorem mainOfTable_jmp_offset2 :
    (mainOfTable program table).jmp_offset2 =
      fun row => (mainTableRowAtOrZero program table row).core.jmp_offset2 := rfl
@[simp] theorem mainOfTable_store_pc :
    (mainOfTable program table).store_pc =
      fun row => (mainTableRowAtOrZero program table row).core.store_pc := rfl
@[simp] theorem mainOfTable_im_high_degree_2 :
    (mainOfTable program table).im_high_degree_2 =
      fun row => (mainTableRowAtOrZero program table row).core.im_high_degree_2 := rfl
@[simp] theorem mainOfTable_segment_l1 :
    (mainOfTable program table).segment_l1 =
      fun row => (mainTableRowAtOrZero program table row).core.segment_l1 := rfl

end MainOfTableProjections

/-- In-range concrete table projection agrees with `List.get`. -/
theorem mainTableRowAtOrZero_get
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    mainTableRowAtOrZero program table idx.val =
      eval (table.environment (table.table.get idx))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar := by
  unfold mainTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete unified Main table has the
    expected core `rowAt` view at every in-range index. -/
theorem rowAt_mainOfTable
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Main.rowAt (mainOfTable program table) idx.val =
      (eval (table.environment (table.table.get idx))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar).core := by
  simp [ZiskFv.AirsClean.Main.rowAt, mainTableRowAtOrZero_get program table idx]

/-- Evaluating the `core` projection of the combined Main+ROM row variable
    agrees with projecting `core` after evaluating the combined row. -/
theorem mainRowWithRom_eval_core
    (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL) :
    eval env row.core = (eval env row).core := by
  cases row
  simp [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go]

/-- Evaluating the `is_external_op` projection directly agrees with projecting
    it after evaluating the Main core row. -/
theorem mainRow_eval_is_external_op
    (env : Environment FGL)
    (row : Var ZiskFv.AirsClean.Main.MainRow FGL) :
    Expression.eval env row.is_external_op = (eval env row).is_external_op := by
  cases row with
  | mk a_0 a_1 b_0 b_1 c_0 c_1 flag pc is_external_op op m32 ind_width
      set_pc jmp_offset1 jmp_offset2 store_pc im_high_degree_2 segment_l1 =>
    simpa [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
      ProvableStruct.fromComponents, ProvableStruct.components,
      ProvableStruct.toComponents, ProvableStruct.eval.go] using
      (CircuitType.eval_expr env is_external_op).symm

/-- The concrete unified Main operation-bus interaction has multiplicity `-1`
    when the evaluated Main core row is active. -/
theorem main_op_row_eval_mult_neg_one_of_active
    {length : ℕ} {program : Program length}
    (env : Environment FGL)
    (h_active :
      (eval env
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core).is_external_op = 1) :
    (((OpBusChannel.emitted
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core.is_external_op)
      (ZiskFv.AirsClean.Main.opBusMessageExpr
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core)).toRaw).eval env).mult = -1 := by
  have h_field :=
    mainRow_eval_is_external_op env
      (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
        length program).rowInputVar.core
  change
    Expression.eval env
      (-(ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
          length program).rowInputVar.core.is_external_op) = -1
  simp [Expression.eval, h_field, h_active]

/-- Field-projection form of `rowAt_mainOfTable`, matching callers that already
    evaluate the Main core row input directly. -/
theorem rowAt_mainOfTable_core
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    eval (table.environment (table.table.get idx))
        (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program).rowInputVar.core =
      ZiskFv.AirsClean.Main.rowAt (mainOfTable program table) idx.val := by
  rw [rowAt_mainOfTable program table idx]
  exact mainRowWithRom_eval_core _ _

/-- The component `Spec` for a concrete unified Main table row projects to the
    named-column `Spec` for the corresponding `mainOfTable` row. -/
theorem mainSpec_rowAt_mainOfTable_of_component_spec
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length)
    (h_component :
      table.component =
        ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program)
    (h_component_spec :
      table.component.Spec (table.environment (table.table.get idx))) :
    ZiskFv.AirsClean.Main.Spec
      (ZiskFv.AirsClean.Main.rowAt (mainOfTable program table) idx.val) := by
  let component :=
    ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus length program
  let env := table.environment (table.table.get idx)
  have h_unified_spec :
      component.Spec env := by
    simpa [component, env, h_component] using h_component_spec
  have h_input_eq :
      eval env component.rowInputVar = component.rowInput env := by
    simpa only [component, Air.Flat.Component.rowInput,
      Air.Flat.Component.rowInputVar] using
        (eval_varFromOffset_valueFromOffset component.Input 0 env)
  have h_core_eq :
      (component.rowInput env).core = eval env component.rowInputVar.core := by
    rw [← h_input_eq]
    exact (mainRowWithRom_eval_core env component.rowInputVar).symm
  have h_row_spec :
      ZiskFv.AirsClean.Main.Spec (eval env component.rowInputVar.core) := by
    have h_row_input_spec :
        ZiskFv.AirsClean.Main.Spec ((component.rowInput env).core) := by
      simpa [component, ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus_spec]
        using h_unified_spec
    simpa [h_core_eq] using h_row_input_spec
  rw [← rowAt_mainOfTable_core program table idx]
  exact h_row_spec

/-- The legacy `opBus_row_Main` view of `mainOfTable` is the Clean Main
    operation-bus message evaluated on the same concrete row. -/
theorem opBus_row_Main_mainOfTable
    {length : ℕ}
    (program : Program length)
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.OperationBus.opBus_row_Main (mainOfTable program table) idx.val =
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Main.opBusMessage
          (eval (table.environment (table.table.get idx))
            (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
              length program).rowInputVar).core)
        (eval (table.environment (table.table.get idx))
          (ZiskFv.AirsClean.Main.componentWithRomMemAndOpBus
            length program).rowInputVar).core.is_external_op := by
  rw [← ZiskFv.AirsClean.Main.opBusMessage_toEntry_rowAt_eq_opBus_row]
  rw [rowAt_mainOfTable program table idx]
  simp [mainTableRowAtOrZero_get program table idx]

/-- Zero fallback for out-of-range projections from a concrete Binary table.
    In-range rows are the only rows consumed by the table bridge below. -/
@[reducible]
def zeroBinaryRow : ZiskFv.AirsClean.Binary.BinaryRow FGL where
  aBytes := {
    free_in_a_0 := 0
    free_in_a_1 := 0
    free_in_a_2 := 0
    free_in_a_3 := 0
    free_in_a_4 := 0
    free_in_a_5 := 0
    free_in_a_6 := 0
    free_in_a_7 := 0 }
  bBytes := {
    free_in_b_0 := 0
    free_in_b_1 := 0
    free_in_b_2 := 0
    free_in_b_3 := 0
    free_in_b_4 := 0
    free_in_b_5 := 0
    free_in_b_6 := 0
    free_in_b_7 := 0 }
  cBytes := {
    free_in_c_0 := 0
    free_in_c_1 := 0
    free_in_c_2 := 0
    free_in_c_3 := 0
    free_in_c_4 := 0
    free_in_c_5 := 0
    free_in_c_6 := 0
    free_in_c_7 := 0 }
  chain := {
    carry_0 := 0
    carry_1 := 0
    carry_2 := 0
    carry_3 := 0
    carry_4 := 0
    carry_5 := 0
    carry_6 := 0
    carry_7 := 0
    b_op := 0
    b_op_or_sext := 0 }
  mode := {
    mode32 := 0
    result_is_a := 0
    use_first_byte := 0
    c_is_signed := 0
    mode32_and_c_is_signed := 0 }

/-- Project row `row` of a concrete Clean Binary table to the Binary row input.
    Out-of-range rows use `zeroBinaryRow` only to make the named-column view total. -/
@[reducible]
def binaryTableRowAtOrZero
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.Binary.BinaryRow FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar
  else
    zeroBinaryRow

/-- Named-column Binary view obtained from the concrete Clean Binary table. -/
@[reducible]
def binaryOfTable
    (table : Table FGL) :
    ZiskFv.Airs.Binary.Valid_Binary FGL FGL where
  b_op := fun row => (binaryTableRowAtOrZero table row).chain.b_op
  free_in_a_0 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_0
  free_in_a_1 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_1
  free_in_a_2 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_2
  free_in_a_3 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_3
  free_in_a_4 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_4
  free_in_a_5 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_5
  free_in_a_6 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_6
  free_in_a_7 := fun row => (binaryTableRowAtOrZero table row).aBytes.free_in_a_7
  free_in_b_0 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_0
  free_in_b_1 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_1
  free_in_b_2 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_2
  free_in_b_3 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_3
  free_in_b_4 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_4
  free_in_b_5 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_5
  free_in_b_6 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_6
  free_in_b_7 := fun row => (binaryTableRowAtOrZero table row).bBytes.free_in_b_7
  free_in_c_0 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_0
  free_in_c_1 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_1
  free_in_c_2 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_2
  free_in_c_3 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_3
  free_in_c_4 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_4
  free_in_c_5 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_5
  free_in_c_6 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_6
  free_in_c_7 := fun row => (binaryTableRowAtOrZero table row).cBytes.free_in_c_7
  carry_0 := fun row => (binaryTableRowAtOrZero table row).chain.carry_0
  carry_1 := fun row => (binaryTableRowAtOrZero table row).chain.carry_1
  carry_2 := fun row => (binaryTableRowAtOrZero table row).chain.carry_2
  carry_3 := fun row => (binaryTableRowAtOrZero table row).chain.carry_3
  carry_4 := fun row => (binaryTableRowAtOrZero table row).chain.carry_4
  carry_5 := fun row => (binaryTableRowAtOrZero table row).chain.carry_5
  carry_6 := fun row => (binaryTableRowAtOrZero table row).chain.carry_6
  carry_7 := fun row => (binaryTableRowAtOrZero table row).chain.carry_7
  mode32 := fun row => (binaryTableRowAtOrZero table row).mode.mode32
  result_is_a := fun row => (binaryTableRowAtOrZero table row).mode.result_is_a
  use_first_byte := fun row => (binaryTableRowAtOrZero table row).mode.use_first_byte
  c_is_signed := fun row => (binaryTableRowAtOrZero table row).mode.c_is_signed
  b_op_or_sext := fun row => (binaryTableRowAtOrZero table row).chain.b_op_or_sext
  mode32_and_c_is_signed :=
    fun row => (binaryTableRowAtOrZero table row).mode.mode32_and_c_is_signed
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0
  im_2 := fun _ => 0
  im_3 := fun _ => 0

/-- In-range concrete Binary table projection agrees with `List.get`. -/
theorem binaryTableRowAtOrZero_get
    (table : Table FGL)
    (idx : Fin table.table.length) :
    binaryTableRowAtOrZero table idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar := by
  unfold binaryTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete Binary table has the expected
    `rowAt` view at every in-range index. -/
theorem rowAt_binaryOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Binary.rowAt (binaryOfTable table) idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar := by
  simp [ZiskFv.AirsClean.Binary.rowAt, binaryTableRowAtOrZero_get table idx]
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar
  change
    { aBytes := row.aBytes
      bBytes := row.bBytes
      cBytes := row.cBytes
      chain := row.chain
      mode := row.mode } = row
  cases row
  rfl

/-- The legacy `opBus_row_Binary` view of `binaryOfTable` is the Clean Binary
    operation-bus message evaluated on the same concrete row. -/
theorem opBus_row_Binary_binaryOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.OperationBus.opBus_row_Binary (binaryOfTable table) idx.val =
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.Binary.opBusMessage
          (eval (table.environment (table.table.get idx))
            ZiskFv.AirsClean.Binary.staticLookupComponent.rowInputVar)) 1 := by
  rw [← ZiskFv.AirsClean.Binary.opBusMessage_toEntry_rowAt_eq_opBus_row]
  rw [rowAt_binaryOfTable table idx]

/-- Zero fallback for out-of-range projections from a concrete BinaryExtension
    table. In-range rows are the only rows consumed by the table bridge below. -/
@[reducible]
def zeroBinaryExtensionRow : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL where
  aCols := {
    free_in_a_0 := 0
    free_in_a_1 := 0
    free_in_a_2 := 0
    free_in_a_3 := 0
    free_in_a_4 := 0
    free_in_a_5 := 0
    free_in_a_6 := 0
    free_in_a_7 := 0 }
  cColsLo := {
    free_in_c_0 := 0
    free_in_c_1 := 0
    free_in_c_2 := 0
    free_in_c_3 := 0
    free_in_c_4 := 0
    free_in_c_5 := 0
    free_in_c_6 := 0
    free_in_c_7 := 0 }
  cColsHi := {
    free_in_c_8 := 0
    free_in_c_9 := 0
    free_in_c_10 := 0
    free_in_c_11 := 0
    free_in_c_12 := 0
    free_in_c_13 := 0
    free_in_c_14 := 0
    free_in_c_15 := 0 }
  flags := {
    op := 0
    free_in_b := 0
    op_is_shift := 0
    b_0 := 0
    b_1 := 0 }

/-- Project row `row` of a concrete Clean BinaryExtension table to the
    BinaryExtension row input. Out-of-range rows use `zeroBinaryExtensionRow`
    only to make the named-column view total. -/
@[reducible]
def binaryExtensionTableRowAtOrZero
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.BinaryExtension.BinaryExtensionRow FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      shiftStaticLookupComponent.rowInputVar
  else
    zeroBinaryExtensionRow

/-- Named-column BinaryExtension view obtained from the concrete Clean
    BinaryExtension table. -/
@[reducible]
def binaryExtensionOfTable
    (table : Table FGL) :
    ZiskFv.Airs.BinaryExtension.Valid_BinaryExtension FGL FGL where
  op := fun row => (binaryExtensionTableRowAtOrZero table row).flags.op
  free_in_a_0 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_0
  free_in_a_1 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_1
  free_in_a_2 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_2
  free_in_a_3 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_3
  free_in_a_4 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_4
  free_in_a_5 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_5
  free_in_a_6 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_6
  free_in_a_7 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).aCols.free_in_a_7
  free_in_b := fun row => (binaryExtensionTableRowAtOrZero table row).flags.free_in_b
  free_in_c_0 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_0
  free_in_c_1 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_1
  free_in_c_2 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_2
  free_in_c_3 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_3
  free_in_c_4 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_4
  free_in_c_5 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_5
  free_in_c_6 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_6
  free_in_c_7 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsLo.free_in_c_7
  free_in_c_8 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_8
  free_in_c_9 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_9
  free_in_c_10 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_10
  free_in_c_11 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_11
  free_in_c_12 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_12
  free_in_c_13 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_13
  free_in_c_14 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_14
  free_in_c_15 := fun row =>
    (binaryExtensionTableRowAtOrZero table row).cColsHi.free_in_c_15
  op_is_shift := fun row =>
    (binaryExtensionTableRowAtOrZero table row).flags.op_is_shift
  b_0 := fun row => (binaryExtensionTableRowAtOrZero table row).flags.b_0
  b_1 := fun row => (binaryExtensionTableRowAtOrZero table row).flags.b_1
  gsum := fun _ => 0
  im_0 := fun _ => 0
  im_1 := fun _ => 0
  im_2 := fun _ => 0
  im_3 := fun _ => 0
  im_high_degree_0 := fun _ => 0

/-- In-range concrete BinaryExtension table projection agrees with `List.get`. -/
theorem binaryExtensionTableRowAtOrZero_get
    (table : Table FGL)
    (idx : Fin table.table.length) :
    binaryExtensionTableRowAtOrZero table idx.val =
      eval (table.environment (table.table.get idx))
        shiftStaticLookupComponent.rowInputVar := by
  unfold binaryExtensionTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete BinaryExtension table has the
    expected `rowAt` view at every in-range index. -/
theorem rowAt_binaryExtensionOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.BinaryExtension.rowAt
      (binaryExtensionOfTable table) idx.val =
      eval (table.environment (table.table.get idx))
        shiftStaticLookupComponent.rowInputVar := by
  simp [ZiskFv.AirsClean.BinaryExtension.rowAt,
    binaryExtensionTableRowAtOrZero_get table idx]
  let row :=
    eval (table.environment (table.table.get idx))
      shiftStaticLookupComponent.rowInputVar
  change
    { aCols := row.aCols
      cColsLo := row.cColsLo
      cColsHi := row.cColsHi
      flags := row.flags } = row
  cases row
  rfl

/-- The legacy `opBus_row_BinaryExtension` view of `binaryExtensionOfTable` is
    the Clean BinaryExtension operation-bus message evaluated on the same row. -/
theorem opBus_row_BinaryExtension_binaryExtensionOfTable
    (table : Table FGL)
    (idx : Fin table.table.length) :
    ZiskFv.Airs.OperationBus.opBus_row_BinaryExtension
        (binaryExtensionOfTable table) idx.val =
      ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.BinaryExtension.opBusMessage
          (eval (table.environment (table.table.get idx))
            shiftStaticLookupComponent.rowInputVar)) 1 := by
  rw [← ZiskFv.AirsClean.BinaryExtension.opBusMessage_toEntry_rowAt_eq_opBus_row]
  rw [rowAt_binaryExtensionOfTable table idx]

/-- Zero fallback for out-of-range projections from a concrete Mem table.
    In-range rows are the only rows consumed by the table bridge below. -/
@[reducible]
def zeroMemRow : ZiskFv.AirsClean.Mem.MemRow FGL where
  addr := 0
  step := 0
  sel := 0
  addr_changes := 0
  step_dual := 0
  sel_dual := 0
  value_0 := 0
  value_1 := 0
  wr := 0
  previous_step := 0
  increment_0 := 0
  increment_1 := 0
  read_same_addr := 0

/-- Project row `row` of a concrete Clean Mem table to the Mem row input.
    Out-of-range rows use `zeroMemRow` only to make the named-column view total. -/
@[reducible]
def memTableRowAtOrZero
    (table : Table FGL)
    (row : ℕ) : ZiskFv.AirsClean.Mem.MemRow FGL :=
  if h_row : row < table.table.length then
    eval (table.environment (table.table.get ⟨row, h_row⟩))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  else
    zeroMemRow

/-- Named-column Mem view obtained from the concrete Clean Mem table.

    The Clean table row input contains the primary Mem columns. The stage-2
    permutation columns are supplied separately because they are not fields of
    the Clean `MemRow`. -/
@[reducible]
def memOfTable
    (table : Table FGL)
    (gsum im0 im1 : ℕ → FGL) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL where
  addr := fun row => (memTableRowAtOrZero table row).addr
  step := fun row => (memTableRowAtOrZero table row).step
  sel := fun row => (memTableRowAtOrZero table row).sel
  addr_changes := fun row => (memTableRowAtOrZero table row).addr_changes
  step_dual := fun row => (memTableRowAtOrZero table row).step_dual
  sel_dual := fun row => (memTableRowAtOrZero table row).sel_dual
  value_0 := fun row => (memTableRowAtOrZero table row).value_0
  value_1 := fun row => (memTableRowAtOrZero table row).value_1
  wr := fun row => (memTableRowAtOrZero table row).wr
  previous_step := fun row => (memTableRowAtOrZero table row).previous_step
  increment_0 := fun row => (memTableRowAtOrZero table row).increment_0
  increment_1 := fun row => (memTableRowAtOrZero table row).increment_1
  read_same_addr := fun row => (memTableRowAtOrZero table row).read_same_addr
  gsum := gsum
  im_0 := im0
  im_1 := im1

/-- In-range concrete table projection agrees with `List.get`. -/
theorem memTableRowAtOrZero_get
    (table : Table FGL)
    (idx : Fin table.table.length) :
    memTableRowAtOrZero table idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar := by
  unfold memTableRowAtOrZero
  rw [dif_pos idx.isLt]

/-- The named-column projection of a concrete Mem table has the expected
    `rowAt` view at every in-range index. -/
theorem rowAt_memOfTable
    (table : Table FGL)
    (gsum im0 im1 : ℕ → FGL)
    (idx : Fin table.table.length) :
    ZiskFv.AirsClean.Mem.rowAt (memOfTable table gsum im0 im1) idx.val =
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar := by
  simp [ZiskFv.AirsClean.Mem.rowAt, memTableRowAtOrZero_get table idx]
  let row :=
    eval (table.environment (table.table.get idx))
      ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar
  change
    { addr := row.addr
      step := row.step
      sel := row.sel
      addr_changes := row.addr_changes
      step_dual := row.step_dual
      sel_dual := row.sel_dual
      value_0 := row.value_0
      value_1 := row.value_1
      wr := row.wr
      previous_step := row.previous_step
      increment_0 := row.increment_0
      increment_1 := row.increment_1
      read_same_addr := row.read_same_addr } = row
  cases row
  rfl

/-- Continuation-segment initial memory: start from the finite zero preload for
    the table's active rows, then seed the previous segment's carried-out bytes. -/
@[reducible]
def previousSegmentInitialMemoryOfRows
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (rows : List (Interaction.MemoryBusEntry FGL)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ZiskFv.ZiskCircuit.MemTrace.writeMemoryOfEntry
    (ZiskFv.ZiskCircuit.MemTrace.zeroMemoryOfRows rows)
    (memPreviousSegmentReplayEntry segment)

/-- Explicit row-index bridge from a concrete Clean Mem table to the
    row-indexed generated `Valid_Mem` surface.

    `Table.Constraints` is membership-based (`∀ row ∈ table.table`) and does
    not identify a row's list position with the index consumed by
    `Valid_Mem`/`generated_every_row`. This structure names that missing
    connection without turning it into an anonymous replay-soundness field:
    each concrete table position must evaluate to `rowAt mem idx`, and the
    generated Mem constraints must hold at the same index.

    The generated constraint field cites the complete extracted Mem surface:
    `generated_every_row = segment_every_row ∧ permutation_every_row`, whose
    constituent lemmas mirror the cited `mem.pil` constraints. -/
structure MemTableGeneratedRowsBridge
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL)
    (rowCount : ℕ) : Prop where
  component :
    table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus
  length_eq : table.table.length = rowCount
  rowAt_eq :
    ∀ idx : Fin table.table.length,
      eval (table.environment (table.table.get idx))
        ZiskFv.AirsClean.Mem.componentWithDualMemBus.rowInputVar =
        ZiskFv.AirsClean.Mem.rowAt mem idx.val
  generatedAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val

/-- Build the indexed row bridge from the concrete table projection.

    This discharges the list-position/`rowAt` part definitionally. The remaining
    caller input is exactly the generated Mem every-row fact for that projected
    named-column view. -/
theorem memTableGeneratedRowsBridge_of_memOfTable
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_generatedAt :
      ∀ idx : Fin table.table.length,
        ZiskFv.Airs.Mem.generated_every_row
          segment permutation (memOfTable table gsum im0 im1) idx.val) :
    MemTableGeneratedRowsBridge
      table (memOfTable table gsum im0 im1)
      segment permutation table.table.length where
  component := h_component
  length_eq := rfl
  rowAt_eq := by
    intro idx
    exact (rowAt_memOfTable table gsum im0 im1 idx).symm
  generatedAt := h_generatedAt

/-- Concrete range facts for the indexed Mem table rows.

    These facts name the non-field AIR range-check surface used when turning
    generated field equations into Nat timestamp order:

    * `incrementChunks` mirrors `mem.pil:384-385`.
    * `addrColumns` mirrors `mem.pil:109`, where `addr` is `bits(29)`;
      this is the no-wrap fact needed for byte-address disjointness of
      provider pointers `addr * 8`.
    * `stepColumns` mirrors the `bits(MEM_STEP_BITS)` witness declarations at
      `mem.pil:110` and `mem.pil:122`, with `MEM_STEP_BITS = 40` in the pinned
      RV64IM configuration.
    * `dualStepDelta` mirrors the selector-gated range check
      `mem.pil:397`; it is intentionally conditional on `sel_dual = 1`.

    Keeping this separate from `MemTableGeneratedRowsBridge` avoids silently
    treating selector-gated range checks as unconditional replay soundness. -/
structure MemTableGeneratedRangeFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) : Prop where
  incrementChunks :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.increment_chunks_in_range mem idx.val
  addrColumns :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.addr_columns_in_range mem idx.val
  stepColumns :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.step_columns_in_range mem idx.val
  dualStepDelta :
    ∀ idx : Fin table.table.length,
      mem.sel_dual idx.val = 1 →
        ZiskFv.Airs.Mem.dual_step_delta_in_range mem idx.val

/-- Segment-level range facts for one generated Mem table segment.

    These facts name the segment-global range-check surface used by
    continuation-segment replay:

    * `distanceBaseChunks` mirrors `mem.pil:267-268`, where
      `distance_base[0]` and `distance_base[1]` are 16-bit chunks.

    Together with the generated `mem.pil:265` equation already present in
    `segment_every_row`, these chunks give a coarse bound on
    `previous_segment_addr`. Row-0 generated facts then refine that bound to
    the 29-bit Mem address range required for byte-address no-wrap. -/
structure MemSegmentGeneratedRangeFacts
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) : Prop where
  distanceBaseChunks :
    ZiskFv.Airs.Mem.distance_chunks_in_range
      segment.distance_base_0 segment.distance_base_1

/-- Clean lookup source for the concrete Mem table row range facts.

    This exposes the range-check provenance separately from the replay proof:
    ungated row ranges come from `rowRangeLookups`, while the dual-step delta
    lookup is requested only for rows with `sel_dual = 1`, matching the
    selector-gated `mem.pil:397` range check. -/
structure MemTableGeneratedRangeLookupFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL) : Type 1 where
  rowRanges :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.RowRangeLookupWitness mem idx.val
  dualStepDelta :
    ∀ idx : Fin table.table.length,
      mem.sel_dual idx.val = 1 →
        ZiskFv.AirsClean.Mem.DualStepDeltaRangeLookupWitness mem idx.val

/-- Project concrete Mem table row range facts from lookup-aware Clean
    witnesses. -/
def memTableGeneratedRangeFacts_of_lookupFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h_lookup : MemTableGeneratedRangeLookupFacts table mem) :
    MemTableGeneratedRangeFacts table mem where
  incrementChunks := by
    intro idx
    exact (ZiskFv.AirsClean.Mem.row_ranges_of_lookup_aware_const_soundness
      (h_lookup.rowRanges idx)).1
  addrColumns := by
    intro idx
    exact (ZiskFv.AirsClean.Mem.row_ranges_of_lookup_aware_const_soundness
      (h_lookup.rowRanges idx)).2.1
  stepColumns := by
    intro idx
    exact (ZiskFv.AirsClean.Mem.row_ranges_of_lookup_aware_const_soundness
      (h_lookup.rowRanges idx)).2.2
  dualStepDelta := by
    intro idx h_sel_dual
    exact ZiskFv.AirsClean.Mem.dual_step_delta_in_range_of_lookup_aware_const_soundness
      (h_lookup.dualStepDelta idx h_sel_dual)

/-- Build lookup-aware Mem row range witnesses from the raw generated range
    propositions. This keeps the witness-aware source API constructible for
    generated Lean modules that prove the range facts directly. -/
def memTableGeneratedRangeLookupFacts_of_rangeFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    (h_ranges : MemTableGeneratedRangeFacts table mem) :
    MemTableGeneratedRangeLookupFacts table mem where
  rowRanges := by
    intro idx
    exact ZiskFv.AirsClean.Mem.rowRangeLookupWitness_of_range_facts
      (h_ranges.incrementChunks idx)
      (h_ranges.addrColumns idx)
      (h_ranges.stepColumns idx)
  dualStepDelta := by
    intro idx h_sel_dual
    exact ZiskFv.AirsClean.Mem.dualStepDeltaRangeLookupWitness_of_range_fact
      (h_ranges.dualStepDelta idx h_sel_dual)

/-- Clean lookup source for the segment-level Mem distance-base range facts. -/
structure MemSegmentGeneratedRangeLookupFacts
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) : Type 1 where
  distanceBaseChunks :
    ZiskFv.AirsClean.Mem.DistanceBaseRangeLookupWitness
      segment.distance_base_0 segment.distance_base_1

/-- Project segment-level Mem range facts from lookup-aware Clean witnesses. -/
def memSegmentGeneratedRangeFacts_of_lookupFacts
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    (h_lookup : MemSegmentGeneratedRangeLookupFacts segment) :
    MemSegmentGeneratedRangeFacts segment where
  distanceBaseChunks :=
    ZiskFv.AirsClean.Mem.distance_chunks_in_range_of_lookup_aware_const_soundness
      h_lookup.distanceBaseChunks

/-- Build lookup-aware segment range witnesses from the raw generated segment
    range propositions. -/
def memSegmentGeneratedRangeLookupFacts_of_rangeFacts
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    (h_ranges : MemSegmentGeneratedRangeFacts segment) :
    MemSegmentGeneratedRangeLookupFacts segment where
  distanceBaseChunks :=
    ZiskFv.AirsClean.Mem.distanceBaseRangeLookupWitness_of_range_fact
      h_ranges.distanceBaseChunks

/-- Extractor-facing generated Mem AIR facts for one concrete table segment.

    This is the remaining generated/source surface after the table projection,
    fixed `SEGMENT_L1` shape, active-row equality, and nonempty evidence are
    constructed locally. It intentionally contains only PIL-generated row facts
    and range-check facts; replay soundness is derived downstream from these
    facts by `acceptedMemoryReplayEvidence_of_memTableGeneratedRowsBridge_segmentRangeFacts`. -/
structure MemTableGeneratedAirFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Prop where
  generatedAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val
  rowRanges : MemTableGeneratedRangeFacts table mem
  segmentRanges : MemSegmentGeneratedRangeFacts segment

/-- Split extractor-facing generated Mem constraints for one concrete table.

    `pil-extract mem-air-facts` reports this exact split: generated Mem
    constraints `0..=23` are the `segment_every_row` surface, and constraints
    `24..=33` are the `permutation_every_row` surface. A generated Lean module
    can prove these two fields separately, then assemble
    `MemTableGeneratedAirFacts` without reintroducing a replay-soundness
    assumption. -/
structure MemTableGeneratedConstraintFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Prop where
  segmentAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.segment_every_row segment mem idx.val
  permutationAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.permutation_every_row segment permutation mem idx.val

/-- Type-level package for raw generated Mem facts.

    The individual raw fact families are `Prop`, so this wrapper lets witness
    source callbacks carry them alongside source columns in `Type`. -/
structure MemTableGeneratedRawSourceFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Type where
  constraints : MemTableGeneratedConstraintFacts table mem segment permutation
  rowRanges : MemTableGeneratedRangeFacts table mem
  segmentRanges : MemSegmentGeneratedRangeFacts segment

/-- Clean assertion source for the split generated Mem constraint groups. -/
structure MemTableGeneratedConstraintAssertionFacts
    (table : Table FGL)
    (mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL)
    (permutation : ZiskFv.Airs.Mem.PermutationColumns FGL) : Type 1 where
  segmentAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.SegmentConstraintAssertionWitness segment mem idx.val
  permutationAt :
    ∀ idx : Fin table.table.length,
      ZiskFv.AirsClean.Mem.PermutationConstraintAssertionWitness
        segment permutation mem idx.val

/-- Project split generated Mem constraint facts from their Clean assertion
    witnesses. -/
def memTableGeneratedConstraintFacts_of_assertionFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_assertions :
      MemTableGeneratedConstraintAssertionFacts table mem segment permutation) :
    MemTableGeneratedConstraintFacts table mem segment permutation where
  segmentAt := by
    intro idx
    exact ZiskFv.AirsClean.Mem.segment_every_row_of_constraint_assertions
      (h_assertions.segmentAt idx)
  permutationAt := by
    intro idx
    exact ZiskFv.AirsClean.Mem.permutation_every_row_of_constraint_assertions
      (h_assertions.permutationAt idx)

/-- Build Clean assertion witnesses from raw split generated Mem constraints.

    The assertion circuits contain only constant assertions over the named
    source columns, so this adapter does not add proof content; it just packages
    raw generated facts in the witness-aware source shape. -/
def memTableGeneratedConstraintAssertionFacts_of_constraintFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintFacts table mem segment permutation) :
    MemTableGeneratedConstraintAssertionFacts table mem segment permutation where
  segmentAt := by
    intro idx
    exact ZiskFv.AirsClean.Mem.segmentConstraintAssertionWitness_of_segment_every_row
      (h_constraints.segmentAt idx)
  permutationAt := by
    intro idx
    exact
      ZiskFv.AirsClean.Mem.permutationConstraintAssertionWitness_of_permutation_every_row
        (h_constraints.permutationAt idx)

/-- Recombine the extractor's split generated-constraint groups into the
    `generated_every_row` package consumed by existing replay proofs. -/
theorem generatedAt_of_memTableGeneratedConstraintFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintFacts table mem segment permutation) :
    ∀ idx : Fin table.table.length,
      ZiskFv.Airs.Mem.generated_every_row segment permutation mem idx.val := by
  intro idx
  exact ⟨h_constraints.segmentAt idx, h_constraints.permutationAt idx⟩

/-- Assemble `MemTableGeneratedAirFacts` from the extractor's split generated
    constraint groups plus the explicit range-check surfaces. -/
def memTableGeneratedAirFacts_of_constraintFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintFacts table mem segment permutation)
    (h_rowRanges : MemTableGeneratedRangeFacts table mem)
    (h_segmentRanges : MemSegmentGeneratedRangeFacts segment) :
    MemTableGeneratedAirFacts table mem segment permutation where
  generatedAt := generatedAt_of_memTableGeneratedConstraintFacts h_constraints
  rowRanges := h_rowRanges
  segmentRanges := h_segmentRanges

/-- Assemble raw generated Mem source facts from concrete Clean assertion and
    lookup witnesses. -/
def memTableGeneratedRawSourceFacts_of_witnessFacts
    {table : Table FGL}
    {mem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    (h_constraints :
      MemTableGeneratedConstraintAssertionFacts table mem segment permutation)
    (h_rowRanges : MemTableGeneratedRangeLookupFacts table mem)
    (h_segmentRanges : MemSegmentGeneratedRangeLookupFacts segment) :
    MemTableGeneratedRawSourceFacts table mem segment permutation where
  constraints := memTableGeneratedConstraintFacts_of_assertionFacts h_constraints
  rowRanges := memTableGeneratedRangeFacts_of_lookupFacts h_rowRanges
  segmentRanges := memSegmentGeneratedRangeFacts_of_lookupFacts h_segmentRanges

/-- Build the indexed row bridge from the concrete table projection and the
    compact generated AIR fact package. -/
theorem memTableGeneratedRowsBridge_of_memOfTable_airFacts
    {table : Table FGL}
    {segment : ZiskFv.Airs.Mem.SegmentColumns FGL}
    {permutation : ZiskFv.Airs.Mem.PermutationColumns FGL}
    {gsum im0 im1 : ℕ → FGL}
    (h_component :
      table.component = ZiskFv.AirsClean.Mem.componentWithDualMemBus)
    (h_air :
      MemTableGeneratedAirFacts
        table (memOfTable table gsum im0 im1) segment permutation) :
    MemTableGeneratedRowsBridge
      table (memOfTable table gsum im0 im1)
      segment permutation table.table.length :=
  memTableGeneratedRowsBridge_of_memOfTable h_component h_air.generatedAt

/-- Fixed-column facts for one generated Mem table segment.

    This records the deterministic fixed column declared in `mem.pil:86`:
    `col fixed SEGMENT_L1 = [1,0...]`. The first row of the table segment is a
    segment boundary, and every positive row index is non-boundary. Keeping
    this separate from `MemTableGeneratedRowsBridge` makes the fixed-column
    constructibility obligation explicit instead of hiding it in replay
    evidence. -/
structure MemTableGeneratedFixedColumnFacts
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) : Prop where
  segmentL1_first :
    0 < table.table.length → segment.segment_l1 0 = 1
  segmentL1_nonfirst :
    ∀ idx : Fin table.table.length,
      0 < idx.val → segment.segment_l1 idx.val = 0

/-- Replace a segment-column package's fixed `SEGMENT_L1` column by its
    deterministic shape: row 0 is `1`, all later rows are `0`. -/
@[reducible]
def segmentWithFixedL1
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  { segment with segment_l1 := fun row => if row = 0 then 1 else 0 }

/-- The deterministic `SEGMENT_L1` projection supplies the fixed-column facts
    required by the Mem replay bridge. -/
theorem memTableGeneratedFixedColumnFacts_of_segmentWithFixedL1
    (table : Table FGL)
    (segment : ZiskFv.Airs.Mem.SegmentColumns FGL) :
    MemTableGeneratedFixedColumnFacts table (segmentWithFixedL1 segment) where
  segmentL1_first := by
    intro _h_nonempty
    simp
  segmentL1_nonfirst := by
    intro idx h_pos
    have h_ne : idx.val ≠ 0 := Nat.ne_of_gt h_pos
    simp [h_ne]

/-- Typed Lean target for the Mem AIR facts source reported by
    `pil-extract mem-air-facts`.

    The extractor/report surface identifies the stage-2 accumulator columns,
    the generated segment/permutation formulas, the fixed `SEGMENT_L1` shape,
    and the range-check metadata. This object packages those source columns and
    the resulting `MemTableGeneratedAirFacts` for the concrete table projection.
    It is deliberately a source package, not replay evidence: accepted replay
    and timeline evidence are derived by the constructors below. -/
structure MemTableGeneratedAirSource
    (table : Table FGL) : Type 1 where
  segment : ZiskFv.Airs.Mem.SegmentColumns FGL
  permutation : ZiskFv.Airs.Mem.PermutationColumns FGL
  gsum : ℕ → FGL
  im0 : ℕ → FGL
  im1 : ℕ → FGL
  facts :
    MemTableGeneratedAirFacts
      table (memOfTable table gsum im0 im1)
      (segmentWithFixedL1 segment) permutation

namespace MemTableGeneratedAirSource

@[reducible]
def mem {table : Table FGL} (source : MemTableGeneratedAirSource table) :
    ZiskFv.Airs.Mem.Valid_Mem FGL FGL :=
  memOfTable table source.gsum source.im0 source.im1

@[reducible]
def fixedSegment {table : Table FGL} (source : MemTableGeneratedAirSource table) :
    ZiskFv.Airs.Mem.SegmentColumns FGL :=
  segmentWithFixedL1 source.segment

theorem toFacts {table : Table FGL} (source : MemTableGeneratedAirSource table) :
    MemTableGeneratedAirFacts table source.mem source.fixedSegment source.permutation :=
  source.facts

end MemTableGeneratedAirSource


end ZiskFv.AirsClean.FullEnsemble
