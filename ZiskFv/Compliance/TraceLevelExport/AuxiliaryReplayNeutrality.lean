import ZiskFv.Compliance.TraceLevelExport.PhysicalReplaySpine

/-!
# Replay projection of the actual Main roster

The typed roster is proved equal to the existing component's six RAW
interactions. Its mutable replay projection retains request activity but uses
PIL mem_op1/2 for READ/WRITE semantics: RAW Main multiplicity is a request
sign, not the legacy bus_effect write sign. Register and inactive messages are
excluded ONLY from mutable replay, never from RAW channel balance.
-/

namespace ZiskFv.Compliance.SerializedExecutionRows

open Air.Flat Interaction
open ZiskFv.Channels.MemoryBus
open ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.FullEnsemble (mainOfTable)
open RawProgramBinding
open ZiskFv.ZiskCircuit.MemTrace

/-- Typed form of the MAINTAINED six-interaction Main roster. The equality
below prevents this proof-facing view from becoming an unchecked second bus. -/
def mainTypedMemRoster {n : Nat} (trace : AcceptedZiskTrace n) :
    List (Expression FGL × MemBusMessage (Expression FGL)) :=
  let v := (componentWithRomMemAndOpBus trace.programLength trace.program).rowInputVar
  [(v.rom.a_src_reg, aRegPreMessageExpr v),
   (-(v.rom.a_src_mem + v.rom.a_src_reg), aMemMessageExpr v),
   (v.rom.b_src_reg, bRegPreMessageExpr v),
   (-(v.rom.b_src_mem + v.rom.b_src_ind + v.rom.b_src_reg), bMemMessageExpr v),
   (v.rom.store_reg, cRegPreMessageExpr v),
   (-(v.rom.store_mem + v.rom.store_ind + v.rom.store_reg), cMemMessageExpr v)]

theorem mainTypedMemRoster_exact {n : Nat} (trace : AcceptedZiskTrace n) :
    (mainTypedMemRoster trace).map (fun pair =>
      (MemBusChannel.emitted pair.1 pair.2).toRaw) =
      trace.mainTable.component.operations.interactionsWith MemBusChannel.toRaw := by
  rw [trace.mainTable_component, componentWithRomMemAndOpBus_interactionsWith_memBus]
  rfl

/-- This is an explicit mutable-memory projection, not a RAW parser/default.
Activity is the actual request multiplicity; read/write legacy signs are fixed
by the source PIL opcode, not by reinterpreting Main's negative request sign. -/
def mutableReplayRowsOfTyped (mult : FGL) (message : MemBusMessage FGL) :
    List (MemoryBusEntry FGL) :=
  if mult = 0 then []
  else if message.mem_op = 1 then [message.toEntry (-1) 2]
  else if message.mem_op = 2 then [message.toEntry 1 2]
  else []

theorem mutableReplayRowsOfTyped_eq_nil (mult : FGL) (message : MemBusMessage FGL)
    (notRead : message.mem_op ≠ 1) (notWrite : message.mem_op ≠ 2) :
    mutableReplayRowsOfTyped mult message = [] := by
  simp [mutableReplayRowsOfTyped, notRead, notWrite]

/-- Replay-order projection of EVERY entry in this physical row's actual
six-message roster, including the three register-pre messages. -/
noncomputable def mainMutableReplayRowsAt {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) : List (MemoryBusEntry FGL) :=
  let env := trace.mainTable.environment (trace.mainTable.table.get row)
  (mainTypedMemRoster trace).flatMap fun pair =>
    mutableReplayRowsOfTyped (((MemBusChannel.emitted pair.1 pair.2).toRaw).eval env).mult
      (eval env pair.2)

/-- The actual C write projection; x0 filtering is the architectural fold's
existing away-from-zero condition, not a fabricated auxiliary instruction. -/
noncomputable def actualCRegisterWriteAt {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length) : Option (MemoryBusEntry FGL) :=
  if (mainCMemInteractionAt trace row).mult = 0 then none
  else if (cMemMessage (mainRowWithRomAt trace row)).mem_op = 3 then
    some ((cMemMessage (mainRowWithRomAt trace row)).toEntry 1 1)
  else none

theorem actualCRegisterWriteAt_of_mult_zero {n : Nat} (trace : AcceptedZiskTrace n)
    (row : Fin trace.mainTable.table.length)
    (zero : (mainCMemInteractionAt trace row).mult = 0) :
    actualCRegisterWriteAt trace row = none := by
  simp [actualCRegisterWriteAt, zero]

/-- The actual source-expanded first row contributes NO mutable replay event,
not merely a zero C write. All six roster members are discharged by the source
no-mutable-op theorem, with required register bounds derived from source success. -/
theorem expanded_main_first_mutable_replay_rows_nil {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k) :
    mainMutableReplayRowsAt trace row = [] := by
  obtain ⟨hrd, hrs1⟩ := expanded_source_register_bounds lowering widthTwo
  have projected (pair : Expression FGL × MemBusMessage (Expression FGL))
      (member : pair ∈ mainTypedMemRoster trace) :
      mutableReplayRowsOfTyped
        (((MemBusChannel.emitted pair.1 pair.2).toRaw).eval
          (trace.mainTable.environment (trace.mainTable.table.get row))).mult
        (eval (trace.mainTable.environment (trace.mainTable.table.get row)) pair.2) = [] := by
    have actual : ((MemBusChannel.emitted pair.1 pair.2).toRaw).eval
          (trace.mainTable.environment (trace.mainTable.table.get row)) ∈
        trace.mainTable.component.operations.interactionValuesWith MemBusChannel.toRaw
          (trace.mainTable.environment (trace.mainTable.table.get row)) := by
      rw [Operations.interactionValuesWith_eq_map, ← mainTypedMemRoster_exact trace]
      exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨pair, member, rfl⟩, rfl⟩
    have exclude := expanded_main_first_no_mutable_memory_interaction trace start addr rawProgram
      binding k lowering widthTwo hrd hrs1 row atPc pair.1 pair.2 actual
    exact mutableReplayRowsOfTyped_eq_nil _ _ exclude.1 exclude.2
  unfold mainMutableReplayRowsAt
  exact List.flatMap_eq_nil_iff.mpr projected

/-- Actual mutable replay and actual C write both stutter on the expanded
auxiliary row. No Sail auxiliary action or new caller read/selector oracle. -/
theorem expanded_main_first_replay_and_register_neutral {n rawLength : Nat}
    (trace : AcceptedZiskTrace n)
    (start : Fin rawLength → Fin trace.programLength)
    (addr : Fin rawLength → FGL) (rawProgram : Fin rawLength → BitVec 32)
    (binding : ProgramRowsBinding trace start addr rawProgram)
    (k : Fin rawLength) (lowering : SuccessfulRowLowering (rawProgram k))
    (widthTwo : lowering.width = 2)
    (row : Fin trace.mainTable.table.length)
    (atPc : (mainOfTable trace.program trace.mainTable).pc row.val = addr k)
    (memory : Std.ExtHashMap Nat (BitVec 8)) :
    replayMemoryAfterBusRows memory (mainMutableReplayRowsAt trace row) = memory ∧
      actualCRegisterWriteAt trace row = none := by
  obtain ⟨hrd, hrs1⟩ := expanded_source_register_bounds lowering widthTwo
  have zero := expanded_main_first_cMemInteraction_mult_zero trace start addr rawProgram
    binding k lowering widthTwo hrd hrs1 row atPc
  constructor
  · rw [expanded_main_first_mutable_replay_rows_nil trace start addr rawProgram binding
      k lowering widthTwo row atPc]
    rfl
  · exact actualCRegisterWriteAt_of_mult_zero trace row zero

end ZiskFv.Compliance.SerializedExecutionRows
