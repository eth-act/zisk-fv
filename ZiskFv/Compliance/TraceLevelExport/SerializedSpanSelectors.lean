import ZiskFv.Compliance.TraceLevelExport.SerializedSpanBase
import ZiskFv.Compliance.TraceLevelExport.RomDecodeBindingOps
import ZiskFv.AirsClean.FullEnsemble.Balance.MemBusRowBridges

/-!
# Accepted Main selectors on an expanded source span's first row

The source pins are used only after the actual Main/ROM lookup and accepted
Booleanity have identified the physical row's columns. These are row-local
execution-channel facts, not a claim about an architectural state transition.
All indices are physical Main indices; no architectural/physical alignment is
required. In particular an expanded source instruction need not be final.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Air.Flat
open Aeneas Aeneas.Std Result zisk_core
open RawProgramBinding
open ZiskFv.AirsClean.FullEnsemble
open ZiskFv.AirsClean.Main
open ZiskFv.Channels.MemoryBus (MemBusChannel)
open ZiskFv.Channels.ZiskRomBus (ZiskRomMessage)

private lemma bool_of_booleanity {col : FGL} (h : col * (1 - col) = 0) :
    ∃ d : Bool, col = ZiskFv.AirsClean.boolF d := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact ⟨false, by simpa [ZiskFv.AirsClean.boolF] using h0⟩
  · exact ⟨true, by
      simp only [ZiskFv.AirsClean.boolF_true]
      exact (sub_eq_zero.mp h1).symm⟩

/-- The existing selector projections omit `a_src_mem`. Recover that remaining
column with the same accepted Booleanity and packed-flag injectivity argument. -/
private theorem mainAMemorySelectorColumn_of_packFlags_at {n : Nat}
    (trace : AcceptedZiskTrace n) (row : Fin trace.mainTable.table.length)
    (bits : RomFlagBits)
    (h : romFlags (mainTableRowAtOrZero trace.program trace.mainTable row.val) =
      packFlags bits) :
    (mainTableRowAtOrZero trace.program trace.mainTable row.val).rom.a_src_mem =
      ZiskFv.AirsClean.boolF bits.a_src_mem := by
  let r := mainTableRowAtOrZero trace.program trace.mainTable row.val
  obtain ⟨_, _, _, _, _, hb_am, hb_pre, _⟩ :=
    RomDecodeBinding.mainRow_flags_boolean trace row
  obtain ⟨am, eam⟩ := bool_of_booleanity hb_am
  obtain ⟨pre, epre⟩ := bool_of_booleanity hb_pre
  change r.rom.a_src_mem = ZiskFv.AirsClean.boolF am at eam
  change r.rom.is_precompiled = ZiskFv.AirsClean.boolF pre at epre
  obtain ⟨ieo, m32, setpc, storepc⟩ :=
    RomDecodeBinding.romFlagColumns_of_romFlags_eq_packFlags r bits
      (RomDecodeBinding.mainRow_flags_boolean trace row) h
  obtain ⟨areg, aimm, breg, bimm⟩ :=
    RomDecodeBinding.romAllSourceSelectorColumns_of_romFlags_eq_packFlags r bits
      (RomDecodeBinding.mainRow_flags_boolean trace row) h
  obtain ⟨bmem, smem, sind, bind, _, sreg⟩ :=
    RomDecodeBinding.romMemorySelectorColumns_of_romFlags_eq_packFlags r bits
      (RomDecodeBinding.mainRow_flags_boolean trace row) h
  have hpack : romFlags r = packFlags
      { bits with a_src_mem := am, is_precompiled := pre } := by
    simp only [romFlags, packFlags, ieo, m32, setpc, storepc, areg, aimm,
      breg, bimm, bmem, smem, sind, bind, sreg, eam, epre]
  have hbits := RomDecodeBinding.packFlags_inj (hpack.symm.trans h)
  have ham := congrArg RomFlagBits.a_src_mem hbits
  exact eam.trans (congrArg ZiskFv.AirsClean.boolF ham)

/-- Actual PC-control columns on the first row of a width-two JALR lowering. -/
theorem expanded_main_first_core {n rawLength : Nat} (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (mainOfTable trace.program trace.mainTable).set_pc row.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).store_pc row.val = 0 ∧
      (mainOfTable trace.program trace.mainTable).jmp_offset2 row.val = 1 := by
  obtain ⟨_, _, _, _, pins⟩ :=
    lowering.jalr_first_pins_of_width_two widthTwo hrd hrs1
  rcases pins with ⟨_, _, jump, _, _, _, _, _, _, setpc, storepc, _⟩
  have flags := main_first_flags trace start addr rawProgram binding k lowering row atPc
  obtain ⟨_, _, mainSet, mainStore⟩ :=
    RomDecodeBinding.mainFlagColumns_of_packFlags_at trace row _ flags
  have msg := main_first_rom trace start addr rawProgram binding k lowering row atPc
  have mainJump := congrArg ZiskRomMessage.jmp_offset2 msg
  refine ⟨?_, ?_, ?_⟩
  · simpa [romFlagBitsOfExtract, setpc] using mainSet
  · simpa [romFlagBitsOfExtract, storepc] using mainStore
  · rw [mainOfTable_jmp_offset2]
    change (mainTableRowAtOrZero trace.program trace.mainTable row.val).core.jmp_offset2 =
      (lowering.rows.first_row.jmp_offset2.val : FGL) at mainJump
    rw [jump] at mainJump
    have one : ((1#i64).val : FGL) = 1 := by decide
    exact mainJump.trans one

/-- No actual architectural-register or mutable-memory store selector is active.
Unlike the source `store = 0` fact alone, these are accepted Main columns. -/
theorem expanded_main_first_no_write_selectors {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (mainRowWithRomAt trace row).rom.store_reg = 0 ∧
      (mainRowWithRomAt trace row).rom.store_mem = 0 ∧
      (mainRowWithRomAt trace row).rom.store_ind = 0 := by
  obtain ⟨_, _, _, noReg, noMem, noInd⟩ :=
    lowering.jalr_first_no_write_selectors widthTwo hrd hrs1
  obtain ⟨_, mem, ind, _, _, reg⟩ :=
    RomDecodeBinding.mainMemorySelectorColumns_of_packFlags_at trace row _
      (main_first_flags trace start addr rawProgram binding k lowering row atPc)
  exact ⟨by simpa [romFlagBitsOfExtract, noReg] using reg,
    by simpa [romFlagBitsOfExtract, noMem] using mem,
    by simpa [romFlagBitsOfExtract, noInd] using ind⟩

/-- The first row's A side is immediate-only; B is register-or-x0, never mutable
memory. Register previous-access messages remain possible on B; they are reads,
not architectural register updates. -/
theorem expanded_main_first_source_selectors {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (mainRowWithRomAt trace row).rom.a_src_imm = 1 ∧
      (mainRowWithRomAt trace row).rom.a_src_reg = 0 ∧
      (mainRowWithRomAt trace row).rom.a_src_mem = 0 ∧
      (mainRowWithRomAt trace row).rom.b_src_mem = 0 ∧
      (mainRowWithRomAt trace row).rom.b_src_ind = 0 ∧
      ((mainRowWithRomAt trace row).rom.b_src_reg = 0 ∨
        (mainRowWithRomAt trace row).rom.b_src_reg = 1) := by
  obtain ⟨input, _, _, _, pins⟩ :=
    lowering.jalr_first_pins_of_width_two widthTwo hrd hrs1
  rcases pins with ⟨_, _, _, asrc, _, _, bsrc, _⟩
  have flags := main_first_flags trace start addr rawProgram binding k lowering row atPc
  obtain ⟨areg, aimm, _, _⟩ :=
    RomDecodeBinding.romAllSourceSelectorColumns_of_romFlags_eq_packFlags
      (mainRowWithRomAt trace row) _ (RomDecodeBinding.mainRow_flags_boolean trace row) flags
  have amem := mainAMemorySelectorColumn_of_packFlags_at trace row _ flags
  obtain ⟨bmem, _, _, bind, breg, _⟩ :=
    RomDecodeBinding.mainMemorySelectorColumns_of_packFlags_at trace row _ flags
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [romFlagBitsOfExtract, asrc] using aimm
  · simpa [romFlagBitsOfExtract, asrc, zisk_inst.SRC_IMM, zisk_inst.SRC_REG] using areg
  · simpa [romFlagBitsOfExtract, asrc, zisk_inst.SRC_IMM, zisk_inst.SRC_MEM] using amem
  · rcases bsrc with ⟨_, bsrc, _⟩ | ⟨_, bsrc, _⟩
    · change lowering.rows.first_row.b_src = zisk_inst.SRC_IMM at bsrc
      exact ⟨by simpa [romFlagBitsOfExtract, bsrc, zisk_inst.SRC_IMM,
          zisk_inst.SRC_MEM] using bmem,
        by simpa [romFlagBitsOfExtract, bsrc, zisk_inst.SRC_IMM,
          zisk_inst.SRC_IND] using bind,
        Or.inl (by simpa [romFlagBitsOfExtract, bsrc, zisk_inst.SRC_IMM,
          zisk_inst.SRC_REG] using breg)⟩
    · change lowering.rows.first_row.b_src = zisk_inst.SRC_REG at bsrc
      exact ⟨by simpa [romFlagBitsOfExtract, bsrc, zisk_inst.SRC_REG,
          zisk_inst.SRC_MEM] using bmem,
        by simpa [romFlagBitsOfExtract, bsrc, zisk_inst.SRC_REG,
          zisk_inst.SRC_IND] using bind,
        Or.inr (by simpa [romFlagBitsOfExtract, bsrc] using breg)⟩

private theorem cMemInteraction_eval_mult
    (env : Environment FGL) (v : Var MainRowWithRom FGL) :
    (((MemBusChannel.emitted
      (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg))
      (cMemMessageExpr v)).toRaw).eval env).mult =
      -((eval env v).rom.store_mem + (eval env v).rom.store_ind +
        (eval env v).rom.store_reg) := by
  change Expression.eval env
    (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg)) = _
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    ProvableType.eval_field, Expression.eval]
  ring

private theorem cRegPreInteraction_eval_mult
    (env : Environment FGL) (v : Var MainRowWithRom FGL) :
    (((MemBusChannel.emitted v.rom.store_reg
      (cRegPreMessageExpr v)).toRaw).eval env).mult = (eval env v).rom.store_reg := by
  change Expression.eval env v.rom.store_reg = (eval env v).rom.store_reg
  simp only [ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go, ProvableType.eval_field]

/-- Actual physical C pull, including the component's real multiplicity and
Main-table evaluation environment. -/
noncomputable def mainCMemInteractionAt {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) : Interaction FGL :=
  let v := (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
  ((MemBusChannel.emitted (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg))
    (cMemMessageExpr v)).toRaw).eval
      (trace.mainTable.environment (trace.mainTable.table.get row))

/-- The physical C interaction really belongs to the accepted Main trace. -/
theorem mainCMemInteractionAt_mem {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) :
    mainCMemInteractionAt trace row ∈ trace.mainTable.interactionsWith MemBusChannel.toRaw := by
  rw [Table.interactionsWith]
  refine List.mem_flatMap.mpr ⟨trace.mainTable.table.get row,
    List.mem_iff_get.mpr ⟨row, rfl⟩, ?_⟩
  simp [mainCMemInteractionAt, Operations.interactionValuesWith_eq_map,
    trace.mainTable_component, componentWithRomMemAndOpBus_interactionsWith_memBus]

/-- The actual C memory-bus interaction is inactive, not a fabricated legacy
entry with a chosen multiplicity. Therefore this row emits neither a C register
write request nor a C mutable-memory write request. -/
theorem expanded_main_first_cMemInteraction_mult_zero {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (mainCMemInteractionAt trace row).mult = 0 := by
  obtain ⟨reg, mem, ind⟩ := expanded_main_first_no_write_selectors
    trace start addr rawProgram binding k lowering widthTwo hrd hrs1 row atPc
  rw [mainCMemInteractionAt, cMemInteraction_eval_mult,
    ← mainTableRowAtOrZero_get trace.program trace.mainTable row]
  change -((mainRowWithRomAt trace row).rom.store_mem +
    (mainRowWithRomAt trace row).rom.store_ind +
    (mainRowWithRomAt trace row).rom.store_reg) = 0
  rw [mem, ind, reg]
  simp only [add_zero, neg_zero]

/-- All three actual typed Main messages exclude mutable memory: A and C have
opcode zero, while B can only be inactive or a register access (`mem_op = 3`).
Together with the C multiplicity theorem this excludes row-local architectural
register writes and mutable-memory writes, without asserting a state recurrence. -/
theorem expanded_main_first_memory_messages {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (aMemMessage (mainRowWithRomAt trace row)).mem_op = 0 ∧
      ((bMemMessage (mainRowWithRomAt trace row)).mem_op = 0 ∨
        (bMemMessage (mainRowWithRomAt trace row)).mem_op = 3) ∧
      (cMemMessage (mainRowWithRomAt trace row)).mem_op = 0 := by
  obtain ⟨_, ar, am, bm, bi, br⟩ := expanded_main_first_source_selectors
    trace start addr rawProgram binding k lowering widthTwo hrd hrs1 row atPc
  obtain ⟨sr, sm, si⟩ := expanded_main_first_no_write_selectors
    trace start addr rawProgram binding k lowering widthTwo hrd hrs1 row atPc
  refine ⟨by simp [aMemMessage, am, ar], ?_, by simp [cMemMessage, sm, si, sr]⟩
  rcases br with br | br
  · exact Or.inl (by simp [bMemMessage, bm, bi, br])
  · exact Or.inr (by simp [bMemMessage, bm, bi, br])

/-- No interaction in this physical row's actual six-message MemBus roster can
carry a mutable-memory opcode, including the A/B accesses and register-pre
messages. This statement uses membership in the evaluated component roster,
not a source-row selector assumption or a legacy entry with invented fields. -/
theorem expanded_main_first_no_mutable_memory_interaction {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k)
    (mult : Expression FGL)
    (msg : ZiskFv.Channels.MemoryBus.MemBusMessage (Expression FGL))
    (member :
      ((MemBusChannel.emitted mult msg).toRaw).eval
          (trace.mainTable.environment (trace.mainTable.table.get row)) ∈
        trace.mainTable.component.operations.interactionValuesWith MemBusChannel.toRaw
          (trace.mainTable.environment (trace.mainTable.table.get row))) :
    (eval (trace.mainTable.environment (trace.mainTable.table.get row)) msg).mem_op ≠ 1 ∧
      (eval (trace.mainTable.environment (trace.mainTable.table.get row)) msg).mem_op ≠ 2 := by
  obtain ⟨aop, bop, cop⟩ := expanded_main_first_memory_messages
    trace start addr rawProgram binding k lowering widthTwo hrd hrs1 row atPc
  have rowEval :
      eval (trace.mainTable.environment (trace.mainTable.table.get row))
          (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar =
        mainRowWithRomAt trace row :=
    (mainTableRowAtOrZero_get trace.program trace.mainTable row).symm
  have exclude : ∀ x : FGL, x = 0 ∨ x = 3 → x ≠ 1 ∧ x ≠ 2 := by
    intro x hx
    rcases hx with rfl | rfl <;> constructor <;> decide
  rw [trace.mainTable_component, Operations.interactionValuesWith_eq_map,
    componentWithRomMemAndOpBus_interactionsWith_memBus] at member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with h | h | h | h | h | h
  · have op := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
      (h_msg := congrArg Interaction.msg h)
    rw [eval_aRegPreMessageExpr, rowEval] at op
    exact exclude _ (Or.inr op)
  · have op := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
      (h_msg := congrArg Interaction.msg h)
    rw [eval_aMemMessageExpr, rowEval] at op
    exact exclude _ (Or.inl (op.trans aop))
  · have op := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
      (h_msg := congrArg Interaction.msg h)
    rw [eval_bRegPreMessageExpr, rowEval] at op
    exact exclude _ (Or.inr op)
  · have op := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
      (h_msg := congrArg Interaction.msg h)
    rw [eval_bMemMessageExpr, rowEval] at op
    exact exclude _ (bop.elim (fun hzero => Or.inl (op.trans hzero))
      (fun hreg => Or.inr (op.trans hreg)))
  · have op := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
      (h_msg := congrArg Interaction.msg h)
    rw [eval_cRegPreMessageExpr, rowEval] at op
    exact exclude _ (Or.inr op)
  · have op := memBusMessage_mem_op_eq_of_eval_emitted_provider_msg_eq
      (h_msg := congrArg Interaction.msg h)
    rw [eval_cMemMessageExpr, rowEval] at op
    exact exclude _ (Or.inl (op.trans cop))

/-- The C register-pre push is inactive as well. Thus neither half of Main's
register-write handshake is active on the expanded first row. -/
theorem expanded_main_first_cRegPreInteraction_mult_zero {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (hrd : lowering.rows.decode.rd.val < 32)
    (hrs1 : lowering.rows.decode.rs1.val < 32)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    (((MemBusChannel.emitted
      (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar.rom.store_reg
      (cRegPreMessageExpr
        (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar)).toRaw).eval
      (trace.mainTable.environment (trace.mainTable.table.get row))).mult = 0 := by
  rw [cRegPreInteraction_eval_mult,
    ← mainTableRowAtOrZero_get trace.program trace.mainTable row]
  exact (expanded_main_first_no_write_selectors
    trace start addr rawProgram binding k lowering widthTwo hrd hrs1 row atPc).1

end ZiskFv.Compliance.SerializedExecutionRows
