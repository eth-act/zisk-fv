import ZiskFv.AirsClean.MainMirrorWeld
import ZiskFv.AirsClean.Main.MemoryWiring
import ZiskFv.AirsClean.Main.RomWiring

/-! INTERNAL representation gauge, not a native source column. Every value of
`im_high_degree_2` is retained as a family parameter. Equality of the COMPLETE
live circuit and its COMPLETE operation list covers assertions, witnesses,
writes, ROM lookup, six memory messages, operation message and three register
step messages, rather than selecting a favorable subset of constraints.
No existing Main representation, Accepted interface or Root changes here. -/
namespace ZiskFv.AirsClean.PublicIoMainGauge

open Goldilocks ZiskFv.AirsClean.Main
open ZiskFv.AirsClean.ZiskInstructionRom (Program)

def replace {F : Type} (row : MainRowWithRom F) (gauge : F) : MainRowWithRom F :=
  { row with core := { row.core with im_high_degree_2 := gauge } }

theorem replace_idempotent {F : Type} (row : MainRowWithRom F) (first second : F) :
    replace (replace row first) second = replace row second := rfl

theorem core_spec (row : MainRowWithRom FGL) (first second : FGL) :
    Spec (replace row first).core ↔ Spec (replace row second).core := Iff.rfl

theorem assumptions (row : MainRowWithRom FGL) (first second : FGL) :
    Assumptions (replace row first).core ↔ Assumptions (replace row second).core := Iff.rfl

theorem rom_boolean_spec (row : MainRowWithRom FGL) (first second : FGL) :
    RomBoolSpec (replace row first) ↔ RomBoolSpec (replace row second) := Iff.rfl

theorem address_spec (row : MainRowWithRom FGL) (first second : FGL) :
    AddressSpec (replace row first) ↔ AddressSpec (replace row second) := Iff.rfl

theorem source_spec (row : MainRowWithRom FGL) (first second : FGL) :
    SourceSpec (replace row first) ↔ SourceSpec (replace row second) := Iff.rfl

theorem transition (previous current : MainRowWithRom FGL)
    (previousFirst previousSecond currentFirst currentSecond : FGL) :
    transitionBetween (replace previous previousFirst) (replace current currentFirst) ↔
      transitionBetween (replace previous previousSecond) (replace current currentSecond) := Iff.rfl

/-- Equality of the complete circuit, including all monadic effects. -/
theorem whole_circuit (length : Nat) (program : Program length)
    (row : Var MainRowWithRom FGL) (first second : Expression FGL) :
    mainWithRomMemAndOpBus length program (replace row first) =
      mainWithRomMemAndOpBus length program (replace row second) := rfl

/-- Not only the selected assertion slice: the entire operations value. -/
theorem whole_operations (length : Nat) (program : Program length)
    (row : Var MainRowWithRom FGL) (first second : Expression FGL) (offset : Nat) :
    (mainWithRomMemAndOpBus length program (replace row first)).operations offset =
      (mainWithRomMemAndOpBus length program (replace row second)).operations offset := by
  rw [whole_circuit length program row first second]

theorem all_exposed_channels (length : Nat) (program : Program length)
    (row : Var MainRowWithRom FGL) (first second : Expression FGL) (offset : Nat) :
    (mainWithRomMemAndOpBusElaborated length program).exposedChannels (replace row first) offset =
      (mainWithRomMemAndOpBusElaborated length program).exposedChannels (replace row second) offset := rfl

theorem rom_message (row : MainRowWithRom FGL) (first second : FGL) :
    romMessage (replace row first) = romMessage (replace row second) := rfl

theorem operation_message (row : Var MainRowWithRom FGL) (first second : Expression FGL) :
    opBusMessageExpr (replace row first).core = opBusMessageExpr (replace row second).core := rfl

theorem source_operation_message (row : Var MainRowWithRom FGL)
    (first second : Expression FGL) :
    sourceOpBusMessageExpr (replace row first) = sourceOpBusMessageExpr (replace row second) := rfl

theorem all_source_memory_messages (row : Var MainRowWithRom FGL)
    (first second : Expression FGL) :
    sourcePerRowMemoryMessages (replace row first) =
      sourcePerRowMemoryMessages (replace row second) := rfl

theorem all_live_memory_messages (row : Var MainRowWithRom FGL)
    (first second : Expression FGL) :
    livePerRowMemoryMessages (replace row first) =
      livePerRowMemoryMessages (replace row second) := rfl

/-- All 38 physical witness projections are independent of the gauge. The
out-of-profile behavior of the existing extractor is preserved, not expanded. -/
theorem extracted_projection (row : MainRowWithRom FGL) (first second : FGL)
    (id column physicalRow rotation : Nat) :
    mainValue (extractedMainRow (replace row first)) id column physicalRow rotation =
      mainValue (extractedMainRow (replace row second)) id column physicalRow rotation := by
  unfold mainValue
  split <;> rfl

/-- A raw row is NOT equal across gauges: raw slot16 is precisely the
uninterpreted model coordinate. All remaining raw positions agree. -/
theorem all_other_raw_cells (row : MainRowWithRom FGL) (first second : FGL)
    (index : Fin 41) (notGauge : index.val ≠ 16) :
    (mainRawRow (replace row first))[index.val]'(by simp) =
      (mainRawRow (replace row second))[index.val]'(by simp) := by
  fin_cases index <;> simp_all [mainRawRow, replace]

end ZiskFv.AirsClean.PublicIoMainGauge
