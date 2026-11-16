import ZiskFv.AirsClean.ByteMemoryPhysicalRows
import ZiskFv.AirsClean.PublicIoMainTraceLayout

/-!
Independent Byte/Read field inventories against the SINGLE shared
actual Rust AST renderer. No Main profile/coordinate facts are borrowed.
These closed facts become checked reliance only after the actual generated
RuntimeMainTraceLayout package and this consumer have passed their gates.
Native word stride, logical PIL column and bit offset are distinct quantities.
-/
namespace ZiskFv.AirsClean.ByteMemoryTraceProfiles

open Extraction.RuntimeMainTraceLayout
open Extraction.LookupWiring
open ByteMemoryPhysicalRows

/-- Actual dedicated source profile, selected without a fallback AIR. -/
def profile : ByteMemoryPhysicalRows.Air → Profile
  | .byte => byteProfile
  | .readByte => readByteProfile

private def lanes (field : String) (count width : Nat) : List (String × List Nat × Nat) :=
  (List.range count).map (fun index => (field, [index], width))

def byteFields : List (String × List Nat × Nat) :=
  [("sel_high_4b", [], 1), ("sel_high_2b", [], 1), ("sel_high_b", [], 1),
   ("direct_value", [], 32), ("composed_value", [], 32), ("written_composed_value", [], 32),
   ("written_byte_value", [], 8), ("value_16b", [], 16), ("value_8b", [], 8),
   ("byte_value", [], 8), ("addr_w", [], 29), ("step", [], 40), ("is_write", [], 1),
   ("mem_write_values", [0], 32), ("mem_write_values", [1], 32), ("bus_byte", [], 8)]

def readFields : List (String × List Nat × Nat) :=
  [("sel_high_4b", [], 1), ("sel_high_2b", [], 1), ("sel_high_b", [], 1),
   ("direct_value", [], 32), ("composed_value", [], 32), ("value_16b", [], 16),
   ("value_8b", [], 8), ("byte_value", [], 8), ("addr_w", [], 29), ("step", [], 40)]

def expectedFields : ByteMemoryPhysicalRows.Air → List (String × List Nat × Nat)
  | .byte => byteFields | .readByte => readFields

theorem actual_source_cells (air : ByteMemoryPhysicalRows.Air) :
    (profile air).cells =
      ZiskFv.AirsClean.PublicIoMainTraceLayout.expectedCells (expectedFields air) 0 := by
  cases air <;> decide +kernel

theorem actual_source_scope (air : ByteMemoryPhysicalRows.Air) :
    (profile air).nativeGroup = 0 ∧ (profile air).nativeAir = air.airId ∧
    (profile air).nativeRows = air.pilRows ∧
    (profile air).unpackedWords = air.logicalWidth := by
  cases air <;> decide +kernel

theorem actual_separate_packed_strides :
    byteProfile.packedBits = 281 ∧ byteProfile.packedWords = 5 ∧
    readByteProfile.packedBits = 168 ∧ readByteProfile.packedWords = 3 := by
  decide +kernel

/-- Flatten the actual PIL witness symbols, retaining logical index/array rank.
This follows the existing shared Main inventory convention, not a new parser. -/
def compiledCells (air : ByteMemoryPhysicalRows.Air) : List (String × List Nat × Nat) :=
  ((air.schema.symbols.filter (fun symbol =>
      decide (symbol.kind = .witness ∧ symbol.stage = some 1))).flatMap fun symbol =>
    (List.range symbol.lengths.prod).map fun offset =>
      (symbol.name, if symbol.dimensions = 0 then [] else [offset], symbol.index + offset))

theorem actual_native_PIL_coordinate_order (air : ByteMemoryPhysicalRows.Air) :
    ((profile air).cells.zipIdx.map fun (cell, column) => (cell.field, cell.indices, column)) =
      compiledCells air := by
  cases air <;> decide +kernel

end ZiskFv.AirsClean.ByteMemoryTraceProfiles
