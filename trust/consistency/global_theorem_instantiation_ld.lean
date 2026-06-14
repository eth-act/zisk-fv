import ZiskFv.Compliance
import ZiskFv.AirsClean.Main.Circuit

/-!
Concrete LD instantiation of the global theorem.

This witness intentionally has the selected memory read as the first accepted
memory row, so its construction evidence uses `priorRows = []`.  The separate
`memory_prefix_alignment_witness.lean` consistency check covers a concrete
non-empty store prefix for `MemoryPrefixStateAlignment`.
-/

namespace ZiskFv.TrustConsistency

open Goldilocks
open Interaction
open ZiskFv.AirsClean.Main
open ZiskFv.EquivCore.Promises

private def ldPmaAttrs : PMA :=
  { cacheable := false
    coherent := false
    executable := true
    readable := true
    writable := true
    read_idempotent := true
    write_idempotent := true
    misaligned_fault := misaligned_fault.AlignmentFault
    reservability := default
    supports_cbo_zero := false }

private def ldPmaRegion : PMA_Region :=
  { base := 0#64
    size := BitVec.ofNat 64 (2 ^ 32)
    attributes := ldPmaAttrs
    include_in_device_tree := false }

private def ldModeRegs : ZiskFv.Compliance.ModeRegsFull :=
  { mstatus := 0#64
    pmaRegion := ldPmaRegion
    misa := 0#64
    mseccfg := 0#64 }

private def ldByteMemory : Std.ExtHashMap Nat (BitVec 8) :=
  let mem0 :=
    (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).mem
  let mem1 := mem0.insert 0 (0#8)
  let mem2 := mem1.insert 1 (0#8)
  let mem3 := mem2.insert 2 (0#8)
  let mem4 := mem3.insert 3 (0#8)
  let mem5 := mem4.insert 4 (0#8)
  let mem6 := mem5.insert 5 (0#8)
  let mem7 := mem6.insert 6 (0#8)
  mem7.insert 7 (0#8)

private def ldRegs :=
  let regs0 :=
    (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource).regs
  let regs1 := regs0.insert Register.PC (0#64)
  let regs2 := regs1.insert Register.cur_privilege Privilege.Machine
  let regs3 := regs2.insert Register.mstatus ldModeRegs.mstatus
  let regs4 := regs3.insert Register.pma_regions [ldModeRegs.pmaRegion]
  let regs5 := regs4.insert Register.htif_tohost_base (none : Option (BitVec 64))
  let regs6 := regs5.insert Register.misa ldModeRegs.misa
  regs6.insert Register.mseccfg ldModeRegs.mseccfg

private def ldState :
    PreSail.SequentialState RegisterType Sail.trivialChoiceSource :=
  { (default : PreSail.SequentialState RegisterType Sail.trivialChoiceSource) with
    regs := ldRegs
    mem := ldByteMemory }

private def ldInput : PureSpec.LdInput :=
  { r1 := 0#5
    imm := 0#12
    rd := 0#5
    r1_val := 0#64
    PC := 0#64
    data0 := 0#8
    data1 := 0#8
    data2 := 0#8
    data3 := 0#8
    data4 := 0#8
    data5 := 0#8
    data6 := 0#8
    data7 := 0#8 }

private def ldExecRow : List (Interaction.ExecutionBusEntry FGL) :=
  [ { multiplicity := -1, pc := 0, timestamp := 0 },
    { multiplicity := 1, pc := 4, timestamp := 1 } ]

private def ldRegRead : Interaction.MemoryBusEntry FGL :=
  { multiplicity := -1
    as := 1
    ptr := 0
    value_0 := 0
    value_1 := 0
    timestamp := 1 }

private def ldMemRead : Interaction.MemoryBusEntry FGL :=
  { multiplicity := -1
    as := 2
    ptr := 0
    value_0 := 0
    value_1 := 0
    timestamp := 2 }

private def ldRegWrite : Interaction.MemoryBusEntry FGL :=
  { multiplicity := 1
    as := 1
    ptr := 0
    value_0 := 0
    value_1 := 0
    timestamp := 3 }

private def ldBus : ZiskFv.Compliance.BusRows :=
  { exec_row := ldExecRow
    e0 := ldRegRead
    e1 := ldMemRead
    e2 := ldRegWrite }

private def ldRomBits : RomFlagBits :=
  { a_src_imm := false
    a_src_mem := false
    is_precompiled := false
    b_src_imm := false
    b_src_mem := true
    is_external_op := false
    store_pc := false
    store_mem := false
    store_ind := false
    set_pc := false
    m32 := false
    b_src_ind := false
    a_src_reg := true
    b_src_reg := false
    store_reg := true }

private def ldRomMessage : ZiskFv.Channels.ZiskRomBus.ZiskRomMessage FGL :=
  { line := 0
    a_offset_imm0 := 0
    a_imm1 := 0
    b_offset_imm0 := 0
    b_imm1 := 0
    ind_width := 8
    op := ZiskFv.Trusted.OP_COPYB
    store_offset := 0
    jmp_offset1 := 4
    jmp_offset2 := 4
    flags := packFlags ldRomBits }

private def ldMainFree : MainRomFreeCols :=
  { a_0 := 0
    a_1 := 0
    b_0 := 0
    b_1 := 0
    im_high_degree_2 := 0
    segment_l1 := 0
    addr0 := 0
    addr1 := 0
    addr2 := 0
    main_step := 0 }

private def ldMainRow : MainRowWithRom FGL :=
  mainRomRowOf ldRomMessage ldRomBits .internalCopyB ldMainFree

private def ldMain : ZiskFv.Airs.Main.Valid_Main FGL FGL :=
  ZiskFv.AirsClean.Main.validOfRow ldMainRow.core

private def ldMemRow : ZiskFv.AirsClean.Mem.MemRow FGL :=
  { addr := 0
    step := 2
    sel := 1
    addr_changes := 1
    step_dual := 0
    sel_dual := 0
    value_0 := 0
    value_1 := 0
    wr := 0
    previous_step := 0
    increment_0 := 0
    increment_1 := 0
    read_same_addr := 0 }

private def ldMem : ZiskFv.Airs.Mem.Valid_Mem FGL FGL :=
  ZiskFv.AirsClean.Mem.validOfRow ldMemRow

private def emptyEnv : Environment FGL :=
  { get := fun _ => 0
    data := fun _ _ => #[] }

private def ldMainRowVar : Var ZiskFv.AirsClean.Main.MainRowWithRom FGL :=
  { core :=
      { a_0 := .const ldMainRow.core.a_0
        a_1 := .const ldMainRow.core.a_1
        b_0 := .const ldMainRow.core.b_0
        b_1 := .const ldMainRow.core.b_1
        c_0 := .const ldMainRow.core.c_0
        c_1 := .const ldMainRow.core.c_1
        flag := .const ldMainRow.core.flag
        pc := .const ldMainRow.core.pc
        is_external_op := .const ldMainRow.core.is_external_op
        op := .const ldMainRow.core.op
        m32 := .const ldMainRow.core.m32
        ind_width := .const ldMainRow.core.ind_width
        set_pc := .const ldMainRow.core.set_pc
        jmp_offset1 := .const ldMainRow.core.jmp_offset1
        jmp_offset2 := .const ldMainRow.core.jmp_offset2
        store_pc := .const ldMainRow.core.store_pc
        im_high_degree_2 := .const ldMainRow.core.im_high_degree_2
        segment_l1 := .const ldMainRow.core.segment_l1 }
    rom :=
      { a_offset_imm0 := .const ldMainRow.rom.a_offset_imm0
        a_imm1 := .const ldMainRow.rom.a_imm1
        b_offset_imm0 := .const ldMainRow.rom.b_offset_imm0
        b_imm1 := .const ldMainRow.rom.b_imm1
        store_offset := .const ldMainRow.rom.store_offset
        a_src_imm := .const ldMainRow.rom.a_src_imm
        a_src_mem := .const ldMainRow.rom.a_src_mem
        is_precompiled := .const ldMainRow.rom.is_precompiled
        b_src_imm := .const ldMainRow.rom.b_src_imm
        b_src_mem := .const ldMainRow.rom.b_src_mem
        store_mem := .const ldMainRow.rom.store_mem
        store_ind := .const ldMainRow.rom.store_ind
        b_src_ind := .const ldMainRow.rom.b_src_ind
        a_src_reg := .const ldMainRow.rom.a_src_reg
        b_src_reg := .const ldMainRow.rom.b_src_reg
        store_reg := .const ldMainRow.rom.store_reg
        addr0 := .const ldMainRow.rom.addr0
        addr1 := .const ldMainRow.rom.addr1
        addr2 := .const ldMainRow.rom.addr2
        main_step := .const ldMainRow.rom.main_step } }

private def ldMemRowVar : Var ZiskFv.AirsClean.Mem.MemRow FGL :=
  ZiskFv.AirsClean.Mem.constVar ldMemRow

private theorem evalLdMainRowVar :
    eval emptyEnv ldMainRowVar = ldMainRow := by
  simp [ldMainRowVar, ldMainRow, ldRomMessage, ldRomBits, ldMainFree,
    mainRomRowOf, packFlags, ZiskFv.AirsClean.boolF,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    CircuitType.eval_expr, Expression.eval]

private theorem evalLdMemRowVar :
    eval emptyEnv ldMemRowVar = ldMemRow := by
  simp [ldMemRowVar, ldMemRow, ZiskFv.AirsClean.Mem.constVar,
    ProvableStruct.eval_eq_eval, ProvableStruct.eval,
    ProvableStruct.fromComponents, ProvableStruct.components,
    ProvableStruct.toComponents, ProvableStruct.eval.go,
    CircuitType.eval_expr, Expression.eval]

private def ldMainMult : Expression FGL := .const (-1)

private def ldProviderMult : Expression FGL := .const 1

private def ldMainInteraction : Interaction FGL :=
  ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted ldMainMult
    (ZiskFv.AirsClean.Main.bMemMessageExpr ldMainRowVar)).toRaw).eval emptyEnv

private def ldProviderInteraction : Interaction FGL :=
  ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted ldProviderMult
    (ZiskFv.AirsClean.Mem.memBusMessageExpr ldMemRowVar)).toRaw).eval emptyEnv

private theorem ldMainEval :
    ldMainInteraction =
      ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted ldMainMult
        (ZiskFv.AirsClean.Main.bMemMessageExpr ldMainRowVar)).toRaw).eval
        emptyEnv := by
  rfl

private theorem ldProviderEval :
    ldProviderInteraction =
      ((ZiskFv.Channels.MemoryBus.MemBusChannel.emitted ldProviderMult
        (ZiskFv.AirsClean.Mem.memBusMessageExpr ldMemRowVar)).toRaw).eval
        emptyEnv := by
  rfl

private theorem ldMsg :
    ldProviderInteraction.msg = ldMainInteraction.msg := by
  unfold ldProviderInteraction ldMainInteraction
  simp only [AbstractInteraction.eval, ChannelInteraction.toRaw,
    Channel.emitted, emitted]
  rw [← ProvableType.toElements_eval emptyEnv
      (ZiskFv.AirsClean.Mem.memBusMessageExpr ldMemRowVar),
    ← ProvableType.toElements_eval emptyEnv
      (ZiskFv.AirsClean.Main.bMemMessageExpr ldMainRowVar)]
  have h_eval_msg :
      eval emptyEnv (ZiskFv.AirsClean.Mem.memBusMessageExpr ldMemRowVar) =
        eval emptyEnv (ZiskFv.AirsClean.Main.bMemMessageExpr ldMainRowVar) := by
    rw [ZiskFv.AirsClean.Mem.eval_memBusMessageExpr,
      ZiskFv.AirsClean.Main.eval_bMemMessageExpr, evalLdMemRowVar,
      evalLdMainRowVar]
    norm_num [ldMemRow, ldMainRow, ldRomMessage, ldRomBits, ldMainFree,
      ZiskFv.AirsClean.Mem.memBusMessage,
      ZiskFv.AirsClean.Main.bMemMessage, mainRomRowOf,
      ZiskFv.AirsClean.boolF]
  rw [h_eval_msg]

private theorem ldMainRowEq :
    (eval emptyEnv ldMainRowVar).core =
      ZiskFv.AirsClean.Main.rowAt ldMain 0 := by
  rw [evalLdMainRowVar]
  simp [ldMain, ZiskFv.AirsClean.Main.rowAt,
    ZiskFv.AirsClean.Main.validOfRow]

private theorem ldMemRowEq :
    eval emptyEnv ldMemRowVar = ZiskFv.AirsClean.Mem.rowAt ldMem 0 := by
  rw [evalLdMemRowVar]
  simp [ldMem, ldMemRow,
    ZiskFv.AirsClean.Mem.rowAt, ZiskFv.AirsClean.Mem.validOfRow]

private theorem ldMainSpec :
    ZiskFv.AirsClean.Main.Spec (eval emptyEnv ldMainRowVar).core := by
  rw [evalLdMainRowVar]
  norm_num [ldMainRow, ldRomMessage, ldRomBits, ldMainFree,
    mainRomRowOf, ZiskFv.AirsClean.Main.Spec, ZiskFv.AirsClean.boolF,
    ZiskFv.Trusted.OP_COPYB]

private theorem ldStorePcZero :
    (eval emptyEnv ldMainRowVar).core.store_pc = 0 := by
  rw [evalLdMainRowVar]
  rfl

private theorem ldMainBMatch :
    ZiskFv.Airs.MemoryBus.matches_memory_entry ldBus.e1
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.bMemMessage (eval emptyEnv ldMainRowVar)) (-1) 2) := by
  rw [evalLdMainRowVar]
  norm_num [ZiskFv.Airs.MemoryBus.matches_memory_entry, ldBus, ldMemRead,
    ldMainRow, ldRomMessage, ldRomBits, ldMainFree, mainRomRowOf,
    ZiskFv.AirsClean.Main.bMemMessage, ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
    ZiskFv.AirsClean.boolF]

private theorem ldMainCMatch :
    ZiskFv.Airs.MemoryBus.matches_memory_entry ldBus.e2
      (ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry
        (ZiskFv.AirsClean.Main.cMemMessage (eval emptyEnv ldMainRowVar)) 1 1) := by
  rw [evalLdMainRowVar]
  norm_num [ZiskFv.Airs.MemoryBus.matches_memory_entry, ldBus, ldRegWrite,
    ldMainRow, ldRomMessage, ldRomBits, ldMainFree, mainRomRowOf,
    ZiskFv.AirsClean.Main.cMemMessage, ZiskFv.Channels.MemoryBus.MemBusMessage.toEntry,
    ZiskFv.AirsClean.boolF]

private theorem ldAddr1 :
    (eval emptyEnv ldMainRowVar).rom.addr1.toNat =
      ldInput.r1_val.toNat + (BitVec.signExtend 64 ldInput.imm).toNat := by
  rw [evalLdMainRowVar]
  rfl

private theorem ldAddr2ZeroIff :
    Transpiler.wrap_to_regidx (eval emptyEnv ldMainRowVar).rom.addr2 = 0 ↔
      ldInput.rd = 0 := by
  rw [evalLdMainRowVar]
  simp [ldMainRow, ldRomMessage, ldRomBits, ldMainFree,
    mainRomRowOf, ldInput, Transpiler.wrap_to_regidx]

private theorem ldAddr2Idx :
    ldInput.rd.toNat =
      (Transpiler.wrap_to_regidx (eval emptyEnv ldMainRowVar).rom.addr2).val := by
  rw [evalLdMainRowVar]
  rfl

private theorem ldMemSel : ldMem.sel 0 = 1 := by
  rfl

private theorem ldMemWr : ldMem.wr 0 = 0 := by
  rfl

private theorem ldPromises :
    LoadStructuralPromises ldState ldModeRegs.mstatus ldModeRegs.pmaRegion
      ldModeRegs.misa ldModeRegs.mseccfg
      (PureSpec.ld_state_assumptions ldInput ldState)
      (PureSpec.execute_LOADD_pure ldInput).nextPC
      ldBus.exec_row ldBus.e0 ldBus.e1 ldBus.e2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RISC_V_assumptions ldState ldRegs ldModeRegs ldPmaRegion ldPmaAttrs
    simp [Sail.readReg, PreSail.readReg, Std.ExtDHashMap.get?_insert,
      Std.ExtDHashMap.get?_insert_self]
  · unfold PureSpec.ld_state_assumptions ldState ldRegs ldInput ldByteMemory
    simp [LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.rX,
      Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self,
      Std.ExtHashMap.getElem_insert, Std.ExtHashMap.getElem_insert_self]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private def ldEnv : ZiskFv.Compliance.OpEnvelope ldState ldMain 0 :=
  ZiskFv.Compliance.OpEnvelope.ld
    ldInput ldModeRegs ldMem ldBus
    ⟨rfl, rfl⟩ ldPromises 0
    ldMainEval ldProviderEval ldMsg ldMainRowEq ldMemRowEq ldMainSpec
    ldStorePcZero ldMainBMatch ldMainCMatch ldAddr1 ldAddr2ZeroIff
    ldAddr2Idx ldMemSel ldMemWr

private theorem ldBridge : ldEnv.aeneasBridgeTrust := by
  rfl

private theorem ldInitialAgreement :
    ZiskFv.ZiskCircuit.MemTrace.ReplayMemoryAgreement ldState ldByteMemory := by
  intro addr
  rfl

private theorem ldSelectedReadReplayAgreement :
    ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement ldByteMemory
      (ZiskFv.ZiskCircuit.MemTrace.eventOfEntry ldMemRead) := by
  unfold ZiskFv.ZiskCircuit.MemTrace.ReadEventReplayAgreement
    ZiskFv.ZiskCircuit.MemTrace.eventOfEntry ldByteMemory ldMemRead
  simp [Std.ExtHashMap.getElem_insert, Std.ExtHashMap.getElem_insert_self,
    ZiskFv.ZiskCircuit.MemTrace.MemEvent.byteAt,
    ZiskFv.Channels.MemoryBusBytes.byteAt,
    ZiskFv.Channels.MemoryBusBytes.byteOf]

private theorem ldPrefixReadSound :
    ZiskFv.ZiskCircuit.MemTrace.MemoryBusRowsPrefixReadSound
      ldByteMemory [ldMemRead] := by
  intro priorRows row laterRows h_rows _h_as _h_mult
  cases priorRows with
  | nil =>
      simp at h_rows
      rcases h_rows with ⟨h_row, _h_laterRows⟩
      subst row
      exact ldSelectedReadReplayAgreement
  | cons _priorHead priorTail =>
      cases priorTail <;> simp at h_rows

private def ldReplayFacts :
    ZiskFv.AirsClean.Mem.GeneratedMemReplayFacts ldState [ldMemRead] :=
  { initialMemory := ldByteMemory
    prefixReadSound := ldPrefixReadSound
    initialAgreement := ldInitialAgreement }

private theorem ldMemoryConstruction :
    ldEnv.memoryTimelineConstructionEvidence := by
  exact ⟨ldState, [ldMemRead], ldReplayFacts, [], [], rfl, rfl⟩

private theorem ldNoKnownDefect :
    ZiskFv.Compliance.Defects.NoKnownDefect ldEnv := by
  intro id h_block
  cases id <;>
    simp [ZiskFv.Compliance.Defects.Blocks,
      ZiskFv.Compliance.Defects.MaliciousSignedMulWitnessShape,
      ZiskFv.Compliance.Defects.ArithDivDynamicWitnessShape,
      ZiskFv.Compliance.Defects.FenceKnownGoodShape, ldEnv] at h_block

theorem global_theorem_instantiation_ld :
    ldEnv.exec_eq :=
  ZiskFv.Compliance.zisk_riscv_compliant_program_bus
    ldEnv ldBridge ldMemoryConstruction ldNoKnownDefect

#print axioms global_theorem_instantiation_ld

end ZiskFv.TrustConsistency
