import ZiskFv.Compliance.ConstructionMulh
import ZiskFv.Compliance.Wrappers.MulHSU

/-!
# Balance-derived MULHSU construction

This is the signed-times-unsigned companion to `ConstructionMulh`.  Its shared
Arith lookup facts come only from the balance-selected provider's `FullSpec`.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.ArithMul (componentWithArithTable primaryOpBusMessage rowAt)

noncomputable def mulhsuArow
    (trace : AcceptedZiskTrace numInstructions) (_binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH) :
    ZiskFv.AirsClean.ArithMul.ArithMulRow FGL :=
  let h := main_request_mulhsu_provided trace i h_main_active h_main_op
  componentWithArithTable.rowInput (h.choose.environment h.choose_spec.2.choose)

theorem mulhsuArow_fullSpec_row
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH) :
    ZiskFv.AirsClean.ArithMul.FullSpec (mulhsuArow trace binding i h_main_active h_main_op) := by
  unfold mulhsuArow
  set H := main_request_mulhsu_provided trace i h_main_active h_main_op with hH
  obtain ⟨_h_pt_mem, h_rest⟩ := H.choose_spec
  obtain ⟨h_pr_mem, h_component, h_spec, _h_match⟩ := h_rest.choose_spec
  exact ZiskFv.AirsClean.FullEnsemble.arithMul_fullSpec_of_component_spec
    h_component (h_spec h_rest.choose h_pr_mem)

theorem mulhsuArow_fullSpec
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH) :
    ZiskFv.AirsClean.ArithMul.FullSpec
      (rowAt (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)) 0) :=
  fullSpec_rowAt_vOfMulwRow
    (mulhsuArow_fullSpec_row trace binding i h_main_active h_main_op)

theorem mulhsuArow_match_row
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Channels.OperationBus.OpBusMessage.toEntry
        (ZiskFv.AirsClean.ArithMul.primaryOpBusMessage
          (mulhsuArow trace binding i h_main_active h_main_op)) 1) := by
  unfold mulhsuArow
  set H := main_request_mulhsu_provided trace i h_main_active h_main_op with hH
  exact H.choose_spec.2.choose_spec.2.2.2

theorem mulhsuArow_mode_pins
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH) :
    (mulhsuArow trace binding i h_main_active h_main_op).flags.div = 0
      ∧ (mulhsuArow trace binding i h_main_active h_main_op).flags.main_mul = 0
      ∧ (mulhsuArow trace binding i h_main_active h_main_op).flags.main_div = 0 := by
  have h_table := (mulhsuArow_fullSpec_row trace binding i h_main_active h_main_op).2.1
  have h_op : (mulhsuArow trace binding i h_main_active h_main_op).flags.op = 179 := by
    have h_match := mulhsuArow_match_row trace binding i h_main_active h_main_op
    have h_op := h_match.2.1
    rw [ZiskFv.AirsClean.ArithMul.primaryOpBusMessage_toEntry_op,
        show (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val).op
          = (mainOfTable trace.program trace.mainTable).op i.val from rfl,
        h_main_op] at h_op
    simpa [OP_MULSUH] using h_op.symm
  exact ZiskFv.AirsClean.ArithTableProjections.Mul.mulhsu_mode_pins_of_row
    (mulhsuArow trace binding i h_main_active h_main_op) h_table h_op

theorem mulhsuArow_match
    (trace : AcceptedZiskTrace numInstructions) (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH) :
    matches_entry
      (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
      (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
        (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)) 0) := by
  obtain ⟨h_div, h_main_mul, h_main_div⟩ :=
    mulhsuArow_mode_pins trace binding i h_main_active h_main_op
  exact match_opBus_row_ArithMulSecondary_vOfMulwRow h_div h_main_mul h_main_div
    (mulhsuArow_match_row trace binding i h_main_active h_main_op)

/-- Sound MULHSU construction with all shared Arith lookup facts derived from
    operation-bus balance and the selected provider's `FullSpec`. -/
theorem construction_mulhsu_sound_claimed_dead
    (trace : AcceptedZiskTrace numInstructions)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (mulhsu_input : PureSpec.MulhsuInput)
    (r1 r2 rd : regidx)
    (h_main_op :
      (mainOfTable trace.program trace.mainTable).op i.val = ZiskFv.Trusted.OP_MULSUH)
    (h_main_active :
      (mainOfTable trace.program trace.mainTable).is_external_op i.val = 1)
    (h_store_pc :
      (mainOfTable trace.program trace.mainTable).store_pc i.val = 0)
    (h_input_r1 :
      read_xreg (regidx_to_fin r1) (binding i)
        = EStateM.Result.ok mulhsu_input.r1_val (binding i))
    (h_input_r2 :
      read_xreg (regidx_to_fin r2) (binding i)
        = EStateM.Result.ok mulhsu_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some mulhsu_input.PC)
    (h_input_rd : mulhsu_input.rd = regidx_to_fin rd)
    (execRow : List (Interaction.ExecutionBusEntry FGL))
    (h_exec_len : (busSub trace i execRow).exec_row.length = 2)
    (h_e0_mult : (busSub trace i execRow).exec_row[0]!.multiplicity = -1)
    (h_e1_mult : (busSub trace i execRow).exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸
          (BitVec.ofNat 64 ((busSub trace i execRow).exec_row[1]!.pc).val))
        = (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC)
    (h_rd_idx :
      mulhsu_input.rd = Transpiler.wrap_to_regidx (busSub trace i execRow).e2.ptr)
    (bounds : ZiskFv.Compliance.ByteBounds (busSub trace i execRow).e2)
    (h_rs1_value : mulhsu_input.r1_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).a_0 0).val
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).a_1 0).val
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).a_2 0).val
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).a_3 0).val)
    (h_rs2_value : mulhsu_input.r2_val.toNat
      = ZiskFv.PackedBitVec.MulNoWrap.packed4
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).b_0 0).val
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).b_1 0).val
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).b_2 0).val
          ((vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).b_3 0).val)
    (h_not_forge :
      ¬ ((
          (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).na 0 = 1
            ∧ (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).nb 0 = 0
            ∧ (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).np 0 = 0)
        ∨ (
          (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).na 0 = 0
            ∧ (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).nb 0 = 1
            ∧ (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)).np 0 = 0))) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.MUL
          (r2, r1, rd,
           { result_part := VectorHalf.High
             signed_rs1 := .Signed
             signed_rs2 := .Unsigned }))) (binding i)
      = (bus_effect (busSub trace i execRow).exec_row
          [ (busSub trace i execRow).e0
          , (busSub trace i execRow).e1
          , (busSub trace i execRow).e2 ] (binding i)).2 := by
  have h_full :
      ZiskFv.AirsClean.ArithMul.FullSpec
        (rowAt (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)) 0) :=
    mulhsuArow_fullSpec trace binding i h_main_active h_main_op
  have h_match_secondary :
      matches_entry (opBus_row_Main (mainOfTable trace.program trace.mainTable) i.val)
        (ZiskFv.Airs.ArithMul.opBus_row_ArithMulSecondary
          (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)) 0) :=
    mulhsuArow_match trace binding i h_main_active h_main_op
  let pins :
      ZiskFv.Compliance.MainRowPins
        (mainOfTable trace.program trace.mainTable) i.val 1 OP_MULSUH :=
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
      (binding i) mulhsu_input.r1_val mulhsu_input.r2_val mulhsu_input.rd mulhsu_input.PC
      (PureSpec.execute_MULH_mulhsu_pure mulhsu_input).nextPC
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
  exact equiv_MULHSU_of_fullSpec
    (binding i) mulhsu_input r1 r2 rd (busSub trace i execRow)
    (mainOfTable trace.program trace.mainTable) i.val
    (vOfMulwRow (mulhsuArow trace binding i h_main_active h_main_op)) 0
    pins h_match_secondary promises arith_mem bounds
    h_full h_rs1_value h_rs2_value h_not_forge

end ZiskFv.Compliance
