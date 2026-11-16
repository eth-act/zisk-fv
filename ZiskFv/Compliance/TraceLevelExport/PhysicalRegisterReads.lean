import ZiskFv.Compliance.TraceLevelExport.PhysicalRegisterFold
import ZiskFv.Compliance.TraceLevelExport.RegisterCoverageBridge

set_option maxRecDepth 10000

/-!
# Register reads from the actual physical C-write prefix

The accepted raw register walk identifies the last genuine physical C request.
The finite recurrence is `actualPhysicalRegFile`, not a family of invented
architectural steps on auxiliary rows. No canonical32 chunk bound is inferred
from a packed BitVec64 value: the final lane conversion still needs the actual
source-provider bounds at the identified physical writer.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Air.Flat
open Goldilocks Interaction
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainTableRowAtOrZero mainTableRowAtOrZero_get)
open ZiskFv.Channels.MemoryBus
open ZiskFv.Compliance.Instantiation (RegSlot RegWalkStep)

/-- Invert the real C-request projection; no fabricated legacy bus entry is used. -/
theorem actualCRegisterWriteAt_some_memop3
    {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) {entry : MemoryBusEntry FGL}
    (written : actualCRegisterWriteAt trace row = some entry) :
    (cMemMessage (mainRowWithRomAt trace row)).mem_op = 3 ∧
      entry = (cMemMessage (mainRowWithRomAt trace row)).toEntry 1 1 := by
  unfold actualCRegisterWriteAt at written
  split at written
  · cases written
  · split at written
    · rename_i registerOp
      exact ⟨registerOp, (Option.some.inj written).symm⟩
    · cases written

private theorem rawC_eval_mult (env : Environment FGL) (v : Var MainRowWithRom FGL) :
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

/-- `main.pil:323-328`: actual register mode makes the physical C pull active
with its real multiplicity -1. Accepted Booleanity, not a selector promise,
excludes the mutable-store alternatives. -/
theorem actualCRegisterWriteAt_of_memop3
    {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length)
    (registerOp : (cMemMessage (mainRowWithRomAt trace row)).mem_op = 3) :
    actualCRegisterWriteAt trace row =
      some ((cMemMessage (mainRowWithRomAt trace row)).toEntry 1 1) := by
  obtain ⟨register, memory, indirect⟩ :=
    cMemMessage_reg_selectors_of_memop3 trace row registerOp
  have mult : (mainCMemInteractionAt trace row).mult = -1 := by
    rw [mainCMemInteractionAt, rawC_eval_mult,
      ← mainTableRowAtOrZero_get trace.program trace.mainTable row]
    simp only [memory, indirect, register, zero_add, add_zero]
  rw [actualCRegisterWriteAt,
    if_neg (by rw [mult]; exact neg_ne_zero.mpr one_ne_zero), if_pos registerOp]

/-- Every timestamp is the real fixed physical Main index plus its source slot
(1/2/3). The upper bound comes from the existing indexed fixed schema. -/
theorem physicalRegSlot_timestamp_val {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) (slot : RegSlot) :
    (Instantiation.RegWalkStep.timestamp
      (mainTableRowAtOrZero trace.program trace.mainTable row.val, slot)).val =
      (match slot with | .a => 1 | .b => 2 | .c => 3) + 4 * row.val := by
  have step := mainRowAt_main_step trace.mainTable_component row.isLt
  have capacity := main_index_lt_mainFixedCapacity trace.mainTable_component row.isLt
  cases slot <;>
    simp only [Instantiation.RegWalkStep.timestamp, RegSlot.readTimestamp, step]
  · exact slot_timestamp_val (by decide : (1 : Nat) ≤ 3) capacity
  · exact slot_timestamp_val (by decide : (2 : Nat) ≤ 3) capacity
  · exact slot_timestamp_val (by decide : (3 : Nat) ≤ 3) capacity

/-- A genuine selected C write, not a semantic step-label, is on the reader's
actual raw walk whenever it is earlier and targets the queried register. -/
theorem actualCRegisterWriteAt_mem_bootWalk
    {n : Nat} (trace : AcceptedZiskTrace n) (reader writer : Fin n)
    (before : writer.val < reader.val) (slot : RegSlot) (operand : slot = .a ∨ slot = .b)
    {path : List RegWalkStep} {last : RegWalkStep}
    (head : path.head? = some
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val, slot))
    (lastAt : path.getLast? = some last)
    (sites : ∀ w ∈ path, IsActiveWitnessMainRow trace w)
    (chain : List.IsChain RegWalkStep.AnswersRegPre path)
    (boot : BootAnchoredStep trace last)
    (r : Fin 32)
    (readRegister : Transpiler.wrap_to_regidx (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).ptr = r)
    (entry : MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace
      ⟨writer.val, trace.mainTable_index writer⟩ = some entry)
    (writeRegister : Transpiler.wrap_to_regidx entry.ptr = r) :
    (mainTableRowAtOrZero trace.program trace.mainTable writer.val, RegSlot.c) ∈ path := by
  obtain ⟨registerOp, entryEq⟩ := actualCRegisterWriteAt_some_memop3 trace _ written
  have entryPtr : entry.ptr =
      (cMemMessage (mainTableRowAtOrZero trace.program trace.mainTable writer.val)).ptr :=
    congrArg MemoryBusEntry.ptr entryEq
  apply physicalCRegPull_mem_bootWalk trace
    ⟨reader.val, trace.mainTable_index reader⟩
    ⟨writer.val, trace.mainTable_index writer⟩ before slot operand
    head lastAt sites chain boot registerOp
  rw [← entryPtr]
  exact writeRegister.trans readRegister.symm

/-- Local finite-fold extensionality. The hypothesis concerns the actual
physical requests and will be discharged by raw-walk completeness below. -/
theorem actualPhysicalRegFile_eq_of_no_writes_between
    {n : Nat} (trace : AcceptedZiskTrace n) (r : Fin 32)
    (a b : Nat) (ordered : a ≤ b) (bounded : b ≤ n)
    (noWrite : ∀ writer : Fin n, a ≤ writer.val → writer.val < b →
      ∀ entry : MemoryBusEntry FGL,
        actualCRegisterWriteAt trace ⟨writer.val, trace.mainTable_index writer⟩ = some entry →
        Transpiler.wrap_to_regidx entry.ptr ≠ r) :
    actualPhysicalRegFile trace b bounded r =
      actualPhysicalRegFile trace a (Nat.le_trans ordered bounded) r := by
  induction b generalizing a with
  | zero =>
    have zero : a = 0 := Nat.eq_zero_of_le_zero ordered
    subst a
    rfl
  | succ b ih =>
    by_cases same : a = b + 1
    · subst a
      rfl
    · have ordered' : a ≤ b := by omega
      have below : b < n := by omega
      have previous := ih a ordered' (Nat.le_of_lt below)
        (fun writer ha hb entry written => noWrite writer ha (by omega) entry written)
      rw [actualPhysicalRegFile_succ trace ⟨b, below⟩]
      unfold actualCRegisterAction
      cases written : actualCRegisterWriteAt trace
          ⟨b, trace.mainTable_index ⟨b, below⟩⟩ with
      | none => simpa only [written] using previous
      | some entry =>
        have other : Transpiler.wrap_to_regidx entry.ptr ≠ r :=
          noWrite (⟨b, below⟩ : Fin n) ordered' (Nat.lt_succ_self b) entry written
        simpa only [written, if_neg other] using previous

/-- The selected physical request updates its actual destination. Abstracting
the previous file keeps reduction local to the C action, not the finite fold. -/
theorem actualCRegisterAction_of_some
    {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) (regs : Fin 32 → BitVec 64)
    (entry : MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace row = some entry)
    (r : Fin 32) (target : Transpiler.wrap_to_regidx entry.ptr = r) :
    actualCRegisterAction trace row regs r = entryRegValue entry := by
  unfold actualCRegisterAction
  rw [written]
  exact if_pos target

theorem actualPhysicalRegFile_succ_of_write
    {n : Nat} (trace : AcceptedZiskTrace n) (writer : Fin n)
    (entry : MemoryBusEntry FGL)
    (written : actualCRegisterWriteAt trace
      ⟨writer.val, trace.mainTable_index writer⟩ = some entry)
    (r : Fin 32) (target : Transpiler.wrap_to_regidx entry.ptr = r) :
    actualPhysicalRegFile trace (writer.val + 1) (Nat.succ_le_of_lt writer.isLt) r =
      entryRegValue entry := by
  exact (congrFun (actualPhysicalRegFile_succ trace writer) r).trans
    (actualCRegisterAction_of_some trace _ _ entry written r target)

private theorem read_memop3_of_mem_ne_head :
    ∀ (path : List RegWalkStep) (p q : RegWalkStep),
      path.head? = some p → List.IsChain RegWalkStep.AnswersRegPre path →
      q ∈ path → q ≠ p → (q.2.readMessage q.1).mem_op = 3 := by
  intro path
  induction path with
  | nil => intro p q head chain member different; simp at member
  | cons a rest ih =>
    intro p q head chain member different
    have first : a = p := by simpa using head
    subst p
    rcases List.mem_cons.mp member with same | member
    · exact False.elim (different same)
    · cases rest with
      | nil => simp at member
      | cons b tail =>
        obtain ⟨link, chain'⟩ := List.isChain_cons_cons.mp chain
        by_cases same : q = b
        · rw [same, congrArg MemBusMessage.mem_op link]
          cases a.2 <;> rfl
        · exact ih b q rfl chain' member same

/-- Exact last-write characterization at an actual physical prefix cut. The
writer is a real Fin n physical index, its actual raw C projection is selected,
and no total architectural decode is assigned to the other physical rows. -/
theorem bootWalk_actualPhysicalRegFile_lastWrite
    {n : Nat} (trace : AcceptedZiskTrace n) (reader : Fin n)
    (slot : RegSlot) (operand : slot = .a ∨ slot = .b)
    {path : List RegWalkStep} {last : RegWalkStep}
    (head : path.head? = some
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val, slot))
    (lastAt : path.getLast? = some last)
    (sites : ∀ w ∈ path, IsActiveWitnessMainRow trace w)
    (chain : List.IsChain RegWalkStep.AnswersRegPre path)
    (boot : BootAnchoredStep trace last)
    (r : Fin 32)
    (readRegister : Transpiler.wrap_to_regidx (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).ptr = r) :
    (((slot.regPreMessage
          (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_0 = 0 ∧
      (slot.regPreMessage
          (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_1 = 0 ∧
      actualPhysicalRegFile trace reader.val (Nat.le_of_lt reader.isLt) r = 0) ∨
    ∃ (writer : Fin n) (entry : MemoryBusEntry FGL), writer.val < reader.val ∧
      actualCRegisterWriteAt trace ⟨writer.val, trace.mainTable_index writer⟩ = some entry ∧
      Transpiler.wrap_to_regidx entry.ptr = r ∧
      actualPhysicalRegFile trace reader.val (Nat.le_of_lt reader.isLt) r = entryRegValue entry ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_0 = entry.value_0 ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_1 = entry.value_1) := by
  let readerSite : RegWalkStep :=
    (mainTableRowAtOrZero trace.program trace.mainTable reader.val, slot)
  have operandNeC : slot ≠ RegSlot.c := by
    rcases operand with rfl | rfl <;> decide
  have cNeReader : ∀ writer : Fin n,
      (mainTableRowAtOrZero trace.program trace.mainTable writer.val, RegSlot.c) ≠ readerSite := by
    intro writer same
    exact operandNeC (congrArg Prod.snd same).symm
  rcases bootWalk_head_value_strong trace path readerSite last
      head lastAt sites chain boot with
    ⟨lo, hi, noC⟩ | ⟨supplier, member, supplierC, lo, hi, maximal⟩
  · have noWrite : ∀ writer : Fin n, 0 ≤ writer.val → writer.val < reader.val →
        ∀ entry : MemoryBusEntry FGL,
          actualCRegisterWriteAt trace ⟨writer.val, trace.mainTable_index writer⟩ = some entry →
          Transpiler.wrap_to_regidx entry.ptr ≠ r := by
      intro writer _ before entry written target
      have onWalk := actualCRegisterWriteAt_mem_bootWalk trace reader writer before
        slot operand head lastAt sites chain boot r readRegister entry written target
      exact noC _ onWalk (cNeReader writer) rfl
    have zero := actualPhysicalRegFile_eq_of_no_writes_between trace r 0 reader.val
      (Nat.zero_le _) (Nat.le_of_lt reader.isLt) noWrite
    exact Or.inl ⟨lo, hi, by simpa only [actualPhysicalRegFile_zero] using zero⟩
  · have different : supplier ≠ readerSite := by
      intro same
      have slots := congrArg Prod.snd same
      rw [supplierC] at slots
      exact operandNeC slots.symm
    obtain ⟨index, inTable, rowEq⟩ :=
      isActiveWitnessMainRow_eq_mainTableRow trace (sites supplier member)
    have supplierEq : supplier =
        (mainTableRowAtOrZero trace.program trace.mainTable index, RegSlot.c) :=
      Prod.ext rowEq supplierC
    have supplierTime : supplier.timestamp.val = 3 + 4 * index := by
      rw [supplierEq]
      exact physicalRegSlot_timestamp_val trace ⟨index, inTable⟩ .c
    have nonempty : path ≠ [] := List.ne_nil_of_mem member
    have headEq : path.head nonempty = readerSite :=
      Option.some.inj ((List.head?_eq_some_head nonempty).symm.trans head)
    have supplierLe := timestamp_val_le_head_of_mem_chain trace nonempty sites chain member
    rw [headEq] at supplierLe
    have readerTime : readerSite.timestamp.val ≤ 2 + 4 * reader.val := by
      rcases operand with rfl | rfl
      · have exactTime : readerSite.timestamp.val = 1 + 4 * reader.val :=
          physicalRegSlot_timestamp_val trace
            ⟨reader.val, trace.mainTable_index reader⟩ .a
        rw [exactTime]
        exact Nat.add_le_add_right (by decide : (1 : Nat) ≤ 2) _
      · exact physicalRegSlot_timestamp_val trace
          ⟨reader.val, trace.mainTable_index reader⟩ .b |>.le
    have before : index < reader.val := by omega
    let writer : Fin n := ⟨index, Nat.lt_trans before reader.isLt⟩
    let entry := (cMemMessage
      (mainTableRowAtOrZero trace.program trace.mainTable writer.val)).toEntry 1 1
    have registerOp : (cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable writer.val)).mem_op = 3 := by
      have operation := read_memop3_of_mem_ne_head path readerSite supplier
        head chain member different
      rw [supplierEq] at operation
      exact operation
    have written : actualCRegisterWriteAt trace
        ⟨writer.val, trace.mainTable_index writer⟩ = some entry :=
      actualCRegisterWriteAt_of_memop3 trace _ registerOp
    have samePtr := bootWalk_head_ptr trace path readerSite head chain sites
      supplier member different
    have target : Transpiler.wrap_to_regidx entry.ptr = r := by
      rw [supplierEq] at samePtr
      change (cMemMessage
        (mainTableRowAtOrZero trace.program trace.mainTable writer.val)).ptr = _ at samePtr
      exact (congrArg Transpiler.wrap_to_regidx samePtr).trans readRegister
    have noLater : ∀ later : Fin n, writer.val + 1 ≤ later.val → later.val < reader.val →
        ∀ other : MemoryBusEntry FGL,
          actualCRegisterWriteAt trace ⟨later.val, trace.mainTable_index later⟩ = some other →
          Transpiler.wrap_to_regidx other.ptr ≠ r := by
      intro later strictlyAfter beforeReader other laterWritten laterTarget
      have onWalk := actualCRegisterWriteAt_mem_bootWalk trace reader later beforeReader
        slot operand head lastAt sites chain boot r readRegister other laterWritten laterTarget
      have bounded := maximal _ onWalk (cNeReader later) rfl
      have laterTime :
          (Instantiation.RegWalkStep.timestamp
            (mainTableRowAtOrZero trace.program trace.mainTable later.val, RegSlot.c)).val =
            3 + 4 * later.val :=
        physicalRegSlot_timestamp_val trace ⟨later.val, trace.mainTable_index later⟩ .c
      rw [laterTime, supplierTime] at bounded
      change index + 1 ≤ later.val at strictlyAfter
      omega
    have unchanged := actualPhysicalRegFile_eq_of_no_writes_between trace r
      (writer.val + 1) reader.val (by exact Nat.succ_le_of_lt before)
      (Nat.le_of_lt reader.isLt) noLater
    have fileEq := unchanged.trans
      (actualPhysicalRegFile_succ_of_write trace writer entry written r target)
    refine Or.inr ⟨writer, entry, before, written, target, fileEq, ?_, ?_⟩
    · rw [supplierEq] at lo
      exact lo
    · rw [supplierEq] at hi
      exact hi

/-- The path and boot anchor here are constructed from this same accepted raw
Main row. Selector and pointer hypotheses are exactly the local A/B register
read conditions, not an architectural layout or success premise. -/
theorem physicalRegisterRead_lastWrite
    {n : Nat} (trace : AcceptedZiskTrace n) (reader : Fin n)
    (slot : RegSlot) (operand : slot = .a ∨ slot = .b)
    (selected : slot.selector
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val) = 1)
    (r : Fin 32)
    (readRegister : Transpiler.wrap_to_regidx (slot.regPreMessage
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).ptr = r) :
    (((slot.regPreMessage
          (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_0 = 0 ∧
      (slot.regPreMessage
          (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_1 = 0 ∧
      actualPhysicalRegFile trace reader.val (Nat.le_of_lt reader.isLt) r = 0) ∨
    ∃ (writer : Fin n) (entry : MemoryBusEntry FGL), writer.val < reader.val ∧
      actualCRegisterWriteAt trace ⟨writer.val, trace.mainTable_index writer⟩ = some entry ∧
      Transpiler.wrap_to_regidx entry.ptr = r ∧
      actualPhysicalRegFile trace reader.val (Nat.le_of_lt reader.isLt) r = entryRegValue entry ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_0 = entry.value_0 ∧
      (slot.regPreMessage
        (mainTableRowAtOrZero trace.program trace.mainTable reader.val)).value_1 = entry.value_1) := by
  have inTable := trace.mainTable_index reader
  have rowEval : mainTableRowAtOrZero trace.program trace.mainTable reader.val =
      eval (trace.mainTable.environment trace.mainTable.table[reader.val])
        (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar :=
    mainTableRowAtOrZero_get trace.program trace.mainTable ⟨reader.val, inTable⟩
  obtain ⟨path, last, head, lastAt, sites, chain, boot⟩ :=
    exists_bootWalk trace trace.mainTable_mem trace.mainTable_component
      (List.getElem_mem inTable) slot (by rw [← rowEval]; exact selected)
  have headAt : path.head? = some
      (mainTableRowAtOrZero trace.program trace.mainTable reader.val, slot) := by
    simpa only [← rowEval] using head
  exact bootWalk_actualPhysicalRegFile_lastWrite trace reader slot operand
    headAt lastAt sites chain boot r readRegister

end ZiskFv.Compliance.SerializedExecutionRows
