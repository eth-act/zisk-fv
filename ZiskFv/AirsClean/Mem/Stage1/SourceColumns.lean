import Extraction.LookupWiring
import Extraction.SourceDimensions
import Mathlib.Tactic.FinCases

/-! INTERNAL Mem-specific source inventory, not another trace profile or getter.

Pinned ZisK b63274507a040bf9e09d22214df43066e8f80cb7:
* pil/zisk.pil102 selects Mem(N:2**22,large_mem:1,dual_mem:1).
* pil/config.pil1–3 fixes MEM_STEP_BITS=38.
* state-machines/mem/pil/mem.pil109–123,156,171,365,373–374,388
  declares the thirteen stage1 cells, including value[0]/value[1].
* pil/src/pil_helpers/traces.rs295–304 independently declares native fixed
  order SEGMENT_L1/__L1__, MemTraceRow field order/widths and MemTrace alias.

Widths describe the packed representation only. They are NOT added as range
validators on unpacked F-storage. Actual source layout/profile consumption
belongs to the sole shared NativeTraceCells reader, not this inventory. -/
namespace ZiskFv.AirsClean.Mem.Stage1.SourceColumns

open Extraction.LookupWiring

abbrev Column := Fin 13

def physicalRows : Nat := Extraction.SourceDimensions.Mem.rowCount

def stage1Symbols : List SourceSchema.Symbol :=
  SourceSchema.air_Mem.symbols.filter fun symbol =>
    symbol.kind == .witness && symbol.stage == some 1

/-- Independent expected full PIL declaration roster, before array flattening. -/
def expectedSymbols : List SourceSchema.Symbol := [
  ⟨some 0, some 14, "addr", .witness, some 1, 0, 0, []⟩,
  ⟨some 0, some 14, "step", .witness, some 1, 1, 0, []⟩,
  ⟨some 0, some 14, "sel", .witness, some 1, 2, 0, []⟩,
  ⟨some 0, some 14, "addr_changes", .witness, some 1, 3, 0, []⟩,
  ⟨some 0, some 14, "step_dual", .witness, some 1, 4, 0, []⟩,
  ⟨some 0, some 14, "sel_dual", .witness, some 1, 5, 0, []⟩,
  ⟨some 0, some 14, "value", .witness, some 1, 6, 1, [2]⟩,
  ⟨some 0, some 14, "wr", .witness, some 1, 8, 0, []⟩,
  ⟨some 0, some 14, "previous_step", .witness, some 1, 9, 0, []⟩,
  ⟨some 0, some 14, "l_increment", .witness, some 1, 10, 0, []⟩,
  ⟨some 0, some 14, "h_increment", .witness, some 1, 11, 0, []⟩,
  ⟨some 0, some 14, "read_same_addr", .witness, some 1, 12, 0, []⟩]

theorem actual_symbols : stage1Symbols = expectedSymbols := rfl

/-- Complete logical stage width, counting the source value[2] array twice. -/
def logicalWidth : Nat :=
  stage1Symbols.foldl (fun width symbol => width + symbol.lengths.prod) 0

theorem actual_logical_width : logicalWidth = 13 := rfl

theorem actual_rows : physicalRows = 4194304 := rfl

theorem actual_scope :
    Extraction.SourceDimensions.Mem.airGroupIndex = 0 ∧
    Extraction.SourceDimensions.Mem.airIndex = 14 ∧
    SourceSchema.air_Mem.groupIndex = 0 ∧ SourceSchema.air_Mem.airIndex = 14 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A source-identity key, not a shared decoder Kind or a new native Profile. -/
def nativeKey : Column → String × List Nat
  | ⟨0, _⟩ => ("addr", [])
  | ⟨1, _⟩ => ("step", [])
  | ⟨2, _⟩ => ("sel", [])
  | ⟨3, _⟩ => ("addr_changes", [])
  | ⟨4, _⟩ => ("step_dual", [])
  | ⟨5, _⟩ => ("sel_dual", [])
  | ⟨6, _⟩ => ("value", [0])
  | ⟨7, _⟩ => ("value", [1])
  | ⟨8, _⟩ => ("wr", [])
  | ⟨9, _⟩ => ("previous_step", [])
  | ⟨10, _⟩ => ("l_increment", [])
  | ⟨11, _⟩ => ("h_increment", [])
  | ⟨_, _⟩ => ("read_same_addr", [])

/-- Logical PIL-symbol resolution for this actual scalar/rank1 source roster.
Unsupported rank/index combinations fail; no native operand r.id is inferred. -/
def pilColumn? (key : String × List Nat) : Option Nat := do
  let symbol ← stage1Symbols.find? fun symbol => symbol.name == key.1
  match symbol.dimensions, symbol.lengths, key.2 with
  | 0, [], [] => some symbol.index
  | 1, [length], [index] => if index < length then some (symbol.index + index) else none
  | _, _, _ => none

theorem native_order_is_pil_order (column : Column) :
    pilColumn? (nativeKey column) = some column.val := by
  fin_cases column <;> rfl

/-- No two native logical cells are silently merged at an array or field key. -/
theorem native_keys_injective : Function.Injective nativeKey := by
  intro left right equal
  have h := congrArg pilColumn? equal
  rw [native_order_is_pil_order, native_order_is_pil_order] at h
  exact Fin.ext (Option.some.inj h)

theorem every_pil_ordinal_has_native_cell (column : Column) :
    ∃ native : Column, pilColumn? (nativeKey native) = some column.val :=
  ⟨column, native_order_is_pil_order column⟩

/-- Independent native trace_row! packed layout inventory; not an unpacked
range checker and not a decoder. Shared generated profile equality comes later. -/
def packedWidth : Column → Nat
  | ⟨0, _⟩ => 29 | ⟨1, _⟩ => 38 | ⟨2, _⟩ => 1 | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 38 | ⟨5, _⟩ => 1 | ⟨6, _⟩ => 32 | ⟨7, _⟩ => 32
  | ⟨8, _⟩ => 1 | ⟨9, _⟩ => 40 | ⟨10, _⟩ => 22 | ⟨11, _⟩ => 16
  | ⟨_, _⟩ => 1

def bitOffset : Column → Nat
  | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 29 | ⟨2, _⟩ => 67 | ⟨3, _⟩ => 68
  | ⟨4, _⟩ => 69 | ⟨5, _⟩ => 107 | ⟨6, _⟩ => 108 | ⟨7, _⟩ => 140
  | ⟨8, _⟩ => 172 | ⟨9, _⟩ => 173 | ⟨10, _⟩ => 213 | ⟨11, _⟩ => 235
  | ⟨_, _⟩ => 251

theorem packed_total_bits : (List.ofFn packedWidth).sum = 252 := rfl

theorem packed_words : (252 + 63) / 64 = 4 := rfl

theorem actual_fixed_roster :
    SourceSchema.air_Mem.symbols.filter (fun symbol => symbol.kind == .fixed) =
      [⟨some 0, some 14, "Mem.SEGMENT_L1", .fixed, some 0, 0, 0, []⟩,
       ⟨some 0, some 14, "__L1__", .fixed, some 0, 1, 0, []⟩] := rfl

end ZiskFv.AirsClean.Mem.Stage1.SourceColumns
