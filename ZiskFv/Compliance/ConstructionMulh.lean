import ZiskFv.Compliance.ConstructionMulhu
import ZiskFv.Compliance.Wrappers.MulH

/-!
# Balance-derived MULH construction

The selected Arith provider is obtained from finished operation-bus balance.
Its lookup-aware `componentWithArithTable.Spec = FullSpec` supplies the shared
Arith-table membership, 16-bit chunks, signed carries, carry chain, and c46.
The only remaining binders are Sail/exec artifacts, the operand correlation,
and the pre-existing signed-witness forge exclusion.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ArithMul (componentWithArithTable primaryOpBusMessage rowAt)

/-- The balance-selected Arith-Mul provider row for a MULH Main request. -/
noncomputable def mulhArow
    (trace : AcceptedZiskTrace numInstructions) (_binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := main_request_mulh_provided trace i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

/-- The provider component's static lookups yield `FullSpec` for the selected
    MULH row. -/
theorem mulhArow_fullSpec_row
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH) :
    ZiskFv.AirsClean.ArithMul.FullSpec (mulhArow trace binding i h_main_active h_main_op) := by
  unfold mulhArow
  set H := main_request_mulh_provided trace i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

theorem mulhArow_fullSpec
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (rowAt (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)) 0) :=
  fullSpec_rowAt_vOfMulwRow
    (mulhArow_fullSpec_row trace binding i h_main_active h_main_op)

theorem mulhArow_match_row
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (mulhArow trace binding i h_main_active h_main_op)) 1) := by
  unfold mulhArow
  set H := main_request_mulh_provided trace i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

theorem mulhArow_mode_pins
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH) :
    (mulhArow trace binding i h_main_active h_main_op).flags.div = 0
      ∧ (mulhArow trace binding i h_main_active h_main_op).flags.main_mul = 0
      ∧ (mulhArow trace binding i h_main_active h_main_op).flags.main_div = 0 := by
  have h_table := (mulhArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (mulhArow trace binding i h_main_active h_main_op).flags.op = 181 := by
    have h_match := mulhArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val).op
          = (mainOfTable trace.program trace.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_MULH] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.mulh_mode_pins_of_row
    (mulhArow trace binding i h_main_active h_main_op) h_table h_op

theorem mulhArow_match
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
        (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨h_div, h_main_mul, h_main_div⟩ :=
    mulhArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithMulSecondary_vOfMulwRow h_div h_main_mul h_main_div
    (mulhArow_match_row trace binding i h_main_active h_main_op)

/-- Sound MULH construction with all shared Arith lookup facts derived from the
    balance-selected provider, never supplied by the caller. -/
theorem construction_mulh_sound_claimed_dead
    (trace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (mulh_input : PureSpec.MulhInput)
    (r1 r2 rd : regidx)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULH)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_store_pc :
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok mulh_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok mulh_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some mulh_input.PC)
    (h_input_rd : mulh_input.rd = regidx_to_fin rd)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC)
    (h_rd_idx :
      mulh_input.rd = Transpiler.wrap_to_regidx (busSub trace i execRow).e2.ptr)
    (bounds : ZiskFv.Compliance.ByteBounds (busSub trace i execRow).e2)
    (h_rs1_value : mulh_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).a_0 0).val
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).a_1 0).val
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).a_2 0).val
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).a_3 0).val)
    (h_rs2_value : mulh_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).b_0 0).val
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).b_1 0).val
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).b_2 0).val
          ((vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).b_3 0).val)
    (h_not_forge :
      ¬ ((
          (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).na 0 = 1
            ∧ (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).nb 0 = 0
            ∧ (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).np 0 = 0)
        ∨ (
          (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).na 0 = 0
            ∧ (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).nb 0 = 1
            ∧ (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)).np 0 = 0))) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Signed }))) (binding i)
      = (bus_effect (busSub trace i execRow).exec_row
          [ (busSub trace i execRow).e0
          , (busSub trace i execRow).e1
          , (busSub trace i execRow).e2 ] (binding i)).2 := by
  have h_full :
      ZiskFv.AirsClean.ArithMul.FullSpec
        (rowAt (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)) 0) :=
    mulhArow_fullSpec trace binding i h_main_active h_main_op
  have h_match_secondary :
      matches_entry (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
          (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)) 0) :=
    mulhArow_match trace binding i h_main_active h_main_op
  let pins :
      ZiskFv.Compliance.MainRowPins
        (mainOfTable trace.program trace.mainTable) i.val 1 OP_MULH :=
    ⟨h_main_active, h_main_op⟩
  have h_core_store_pc : (mainRowWithRomSub trace i).core.store_pc = 0 := by
    have h_row :
        (mainRowWithRomSub trace i).core =
          ZiskFv.AirsClean.Main.rowAt (mainOfTable trace.program trace.mainTable) i.val := by
      have h := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
        trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
      simpa [mainRowWithRomSub,
        ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
          (idx := ⟨i.val, trace.mainTable_index i⟩)] using h.symm
    rw [h_row]
    simpa [ZiskFv.AirsClean.Main.rowAt] using h_store_pc
  let arith_mem :
      ZiskFv.Compliance.ExternalArithMemoryWitness
        (mainOfTable trace.program trace.mainTable) i.val
        (busSub trace i execRow).e2 :=
    { row := mainRowWithRomSub trace i
      row_eq := by
        have h := ZiskFv.AirsClean.FullEnsemble.rowAt_mainOfTable
          trace.program trace.mainTable ⟨i.val, trace.mainTable_index i⟩
        simpa [mainRowWithRomSub,
          ZiskFv.AirsClean.FullEnsemble.mainTableRowAtOrZero_get
            (idx := ⟨i.val, trace.mainTable_index i⟩)] using h.symm
      store_pc_zero := h_core_store_pc
      rd_write_match := ZiskFv.Airs.MemoryBus.matches_memory_entry_refl _ }
  let promises : ZiskFv.EquivCore.Promises.RTypePromises
      (binding i) mulh_input.r1_val mulh_input.r2_val mulh_input.rd mulh_input.PC
      (PureSpec.execute_MULH_mulh_pure mulh_input).nextPC
      r1 r2 rd (busSub trace i execRow).exec_row (busSub trace i execRow).e0
      (busSub trace i execRow).e1 (busSub trace i execRow).e2 :=
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
  exact equiv_MULH_of_fullSpec
    (binding i) mulh_input r1 r2 rd (busSub trace i execRow)
    (mainOfTable trace.program trace.mainTable) i.val
    (vOfMulwRow (mulhArow trace binding i h_main_active h_main_op)) 0
    pins h_match_secondary promises arith_mem bounds
    h_full h_rs1_value h_rs2_value h_not_forge

end ZiskFv.Compliance
