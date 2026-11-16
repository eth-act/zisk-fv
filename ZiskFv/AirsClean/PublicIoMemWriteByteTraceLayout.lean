import Extraction.RuntimeMemWriteByteTraceLayout
import ZiskFv.AirsClean.PublicIoMainTraceLayout

/-! INTERNAL source descriptor contract, not a raw-word decoder or an unpacked
range validator. These independent rosters pin native names/order/array indices,
widths, packed positions and the actual Rust declaration/alias token trees.
Canonical Profile/Cell types and the existing expected-offset fold are reused.
No native ABI/materialization, compiled-PIL binding, actual populated-row coverage,
Rust execution, Accepted-witness, or public-output binding is asserted. -/
namespace ZiskFv.AirsClean.PublicIoMemWriteByteTraceLayout

open Extraction.RuntimeNativeValuesLayout Extraction.RuntimeMainTraceLayout
open Extraction.RuntimeMemWriteByteTraceLayout

/-- Independent actual-source Mem contract; not produced from emitted cells. -/
def expectedMemFields : List (String × List Nat × Nat) :=
  [("addr", [], 29), ("step", [], 38), ("sel", [], 1),
   ("addr_changes", [], 1), ("step_dual", [], 38), ("sel_dual", [], 1),
   ("value", [0], 32), ("value", [1], 32), ("wr", [], 1),
   ("previous_step", [], 40), ("l_increment", [], 22), ("h_increment", [], 16),
   ("read_same_addr", [], 1)]

/-- The array is two distinct source-indexed coordinates, not an extra column. -/
def expectedWriteByteFields : List (String × List Nat × Nat) :=
  [("sel_high_4b", [], 1), ("sel_high_2b", [], 1), ("sel_high_b", [], 1),
   ("direct_value", [], 32), ("composed_value", [], 32),
   ("written_composed_value", [], 32), ("written_byte_value", [], 8),
   ("value_16b", [], 16), ("value_8b", [], 8), ("byte_value", [], 8),
   ("addr_w", [], 29), ("step", [], 40),
   ("mem_write_values", [0], 32), ("mem_write_values", [1], 32)]

theorem actual_mem_fields :
    memProfile.cells = PublicIoMainTraceLayout.expectedCells expectedMemFields 0 := by
  decide +kernel

theorem actual_write_byte_fields :
    writeByteProfile.cells =
      PublicIoMainTraceLayout.expectedCells expectedWriteByteFields 0 := by
  decide +kernel

theorem actual_source_scopes :
    memProfile.nativeName = "MemTraceRow" ∧ memProfile.rowParameter = "R" ∧
    memProfile.nativeRows = 4194304 ∧ memProfile.nativeGroup = 0 ∧ memProfile.nativeAir = 14 ∧
    writeByteProfile.nativeName = "MemAlignWriteByteTraceRow" ∧
    writeByteProfile.rowParameter = "R" ∧ writeByteProfile.nativeRows = 4194304 ∧
    writeByteProfile.nativeGroup = 0 ∧ writeByteProfile.nativeAir = 20 := by
  decide +kernel

/-- Source bit sums and packed ceilings are derived separately from the emitter.
These are native descriptors, NOT claims that logical cm1 count is packed stride. -/
theorem actual_native_counts_and_offsets :
    memProfile.unpackedWords = 13 ∧ memProfile.packedBits = 252 ∧
    memProfile.packedBits = (expectedMemFields.map fun field => field.2.2).sum ∧
    memProfile.packedWords = 4 ∧
    memProfile.cells.map Cell.bitOffset = [0, 29, 67, 68, 69, 107, 108, 140, 172, 173, 213, 235, 251] ∧
    writeByteProfile.unpackedWords = 14 ∧ writeByteProfile.packedBits = 272 ∧
    writeByteProfile.packedBits = (expectedWriteByteFields.map fun field => field.2.2).sum ∧
    writeByteProfile.packedWords = 5 ∧
    writeByteProfile.cells.map Cell.bitOffset = [0, 1, 2, 3, 35, 67, 99, 107, 123, 131, 139, 168, 208, 240] := by
  decide +kernel

/-- Distinct field/index identities give one descriptor per physical coordinate;
this is not an execution/row-population or bus-multiplicity theorem. -/
theorem actual_coordinates_once :
    (memProfile.cells.map fun cell => (cell.field, cell.indices)).Nodup ∧
    (writeByteProfile.cells.map fun cell => (cell.field, cell.indices)).Nodup := by
  decide +kernel

private def i := Token.ident
private def l := Token.literal
private def p (text : String) := Token.punct text false
private def par (children : List Token) := Token.group "parenthesis" (Tokens.ofList children)
private def bra (children : List Token) := Token.group "brace" (Tokens.ofList children)
private def brk (children : List Token) := Token.group "bracket" (Tokens.ofList children)
private def ubit (width : String) : List Token := [i "ubit", par [l width]]
private def rustField (name : String) (type : List Token) : List Token :=
  [i name, p ":"] ++ type ++ [p ","]
private def declaration (name : String) (fields : List (String × List Token)) : List Token :=
  [i "trace_row", p "!", par [i name, p "<", i "F", p ">",
    bra (fields.flatMap fun field => rustField field.1 field.2)], p ";"]
private def aliasDeclaration (name air : String) : List Token :=
  [i "pub", i "type", i name, p "<", i "R", p ">", p "=", i "GenericTrace", p "<",
   i "R", p ",", l "4194304", p ",", l "0", p ",", l air, p ">", p ";"]

/-- Exact source spelling/types, independent of descriptor width interpretation. -/
def expectedMemDeclaration : List Token := declaration "MemTraceRow"
  [("addr", ubit "29"), ("step", ubit "38"), ("sel", [i "bit"]),
   ("addr_changes", [i "bit"]), ("step_dual", ubit "38"), ("sel_dual", [i "bit"]),
   ("value", [brk [i "u32", p ";", l "2"]]), ("wr", [i "bit"]),
   ("previous_step", ubit "40"), ("l_increment", ubit "22"),
   ("h_increment", [i "u16"]), ("read_same_addr", [i "bit"])]

def expectedWriteByteDeclaration : List Token := declaration "MemAlignWriteByteTraceRow"
  [("sel_high_4b", [i "bit"]), ("sel_high_2b", [i "bit"]), ("sel_high_b", [i "bit"]),
   ("direct_value", [i "u32"]), ("composed_value", [i "u32"]),
   ("written_composed_value", [i "u32"]), ("written_byte_value", [i "u8"]),
   ("value_16b", [i "u16"]), ("value_8b", [i "u8"]), ("byte_value", [i "u8"]),
   ("addr_w", ubit "29"), ("step", ubit "40"),
   ("mem_write_values", [brk [i "u32", p ";", l "2"]])]

def fragmentTokens? (name : String) : Option (List Token) :=
  (Extraction.RuntimeMemWriteByteTraceLayout.sourceFragments.find? fun fragment =>
    fragment.name == name).map fun fragment =>
      fragment.tokens.map NativeValuesLayout.semanticToken

/-- Closed fidelity pins: not self-generated expected values, source hash checks,
or a proof of generic Rust/syn/quote semantics. No Root caller premise is added. -/
def sourceDeclarationsAccepted : Bool :=
  fragmentTokens? "MemTraceRow" == some expectedMemDeclaration &&
  fragmentTokens? "MemTrace.alias" == some (aliasDeclaration "MemTrace" "14") &&
  fragmentTokens? "MemAlignWriteByteTraceRow" == some expectedWriteByteDeclaration &&
  fragmentTokens? "MemAlignWriteByteTrace.alias" ==
    some (aliasDeclaration "MemAlignWriteByteTrace" "20")

theorem actual_source_declarations : sourceDeclarationsAccepted = true := by
  decide +kernel

theorem actual_fragment_roster :
    Extraction.RuntimeMemWriteByteTraceLayout.sourceFragments.map SourceFragment.name =
      ["MemTraceRow", "MemTrace.alias", "MemAlignWriteByteTraceRow", "MemAlignWriteByteTrace.alias"] ∧
    (Extraction.RuntimeMemWriteByteTraceLayout.sourceFragments.all fun fragment =>
      fragment.sourceFile == "pil_helpers/traces.rs" &&
      decide (fragment.startByte < fragment.endByte)) = true := by
  decide +kernel

end ZiskFv.AirsClean.PublicIoMemWriteByteTraceLayout
