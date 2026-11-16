import ZiskFv.AirsClean.MemAlignWriteByte.NativeTraceWords
import ZiskFv.AirsClean.NativeValuesLayout
import Extraction.RuntimeMainTraceLayout
import Extraction.SourceDimensions

/-! INTERNAL bounded trace_row! source profile. The native declaration order,
bit widths, packed positions and GenericTrace metadata are not inferred from
PIL indices. Their independent comparison is proved below. This is not a Rust
compiler, ABI, pointer/materialization or compiled-native-operand proof. -/
namespace ZiskFv.AirsClean.PublicIoMainTraceLayout

open Goldilocks Extraction.RuntimeNativeValuesLayout
open Extraction.RuntimeMainTraceLayout Extraction.LookupWiring

/-- Independent source contract, not a reordered copy of generated indices. -/
def expectedFields : List (String × List Nat × Nat) :=
  [("a", [0], 32), ("a", [1], 32), ("b", [0], 32), ("b", [1], 32),
   ("c", [0], 32), ("c", [1], 32), ("flag", [], 1), ("pc", [], 32),
   ("a_src_imm", [], 1), ("a_src_mem", [], 1), ("a_offset_imm0", [], 64),
   ("a_imm1", [], 32), ("is_precompiled", [], 1), ("b_src_imm", [], 1),
   ("b_src_mem", [], 1), ("b_offset_imm0", [], 64), ("b_imm1", [], 32),
   ("b_src_ind", [], 1), ("ind_width", [], 4), ("is_external_op", [], 1),
   ("op", [], 8), ("store_pc", [], 1), ("store_mem", [], 1),
   ("store_ind", [], 1), ("store_offset", [], 64), ("set_pc", [], 1),
   ("jmp_offset1", [], 64), ("jmp_offset2", [], 64), ("m32", [], 1),
   ("addr1", [], 32), ("a_reg_prev_mem_step", [], 38),
   ("b_reg_prev_mem_step", [], 38), ("store_reg_prev_mem_step", [], 38),
   ("store_reg_prev_value", [0], 32), ("store_reg_prev_value", [1], 32),
   ("a_src_reg", [], 1), ("b_src_reg", [], 1), ("store_reg", [], 1)]

def expectedCells : List (String × List Nat × Nat) → Nat → List Cell
  | [], _ => []
  | (name, indices, width) :: rest, offset =>
    ⟨name, indices, width, offset⟩ :: expectedCells rest (offset + width)

theorem actual_native_fields : mainProfile.cells = expectedCells expectedFields 0 := by decide +kernel

theorem actual_native_scope :
    mainProfile.nativeRows = 4194304 ∧ mainProfile.nativeGroup = 0 ∧ mainProfile.nativeAir = 12 ∧
    mainProfile.nativeRows = Extraction.SourceDimensions.Main.rowCount ∧
    mainProfile.rowParameter = "R" := by decide

theorem actual_scalar_and_packed_widths :
    mainProfile.cells.length = 38 ∧ mainProfile.packedBits = 846 ∧ mainProfile.packedWords = 14 := by decide

/-- The three additionally approved consumers need NATIVE strides, not the
logical cm1 column count asserted to be a packed word count. Full descriptor
lists and source ordinals remain available in each actual generated profile. -/
theorem bounded_component_native_strides :
    binaryProfile.nativeRows = 4194304 ∧ binaryProfile.nativeGroup = 0 ∧
    binaryProfile.nativeAir = SourceSchema.air_Binary.airIndex ∧
    binaryProfile.unpackedWords = 39 ∧ binaryProfile.packedBits = 222 ∧
    binaryProfile.packedWords = 4 ∧
    byteProfile.nativeRows = 4194304 ∧ byteProfile.nativeGroup = 0 ∧
    byteProfile.nativeAir = SourceSchema.air_MemAlignByte.airIndex ∧
    byteProfile.unpackedWords = 16 ∧ byteProfile.packedBits = 281 ∧
    byteProfile.packedWords = 5 ∧
    readByteProfile.nativeRows = 4194304 ∧ readByteProfile.nativeGroup = 0 ∧
    readByteProfile.nativeAir = SourceSchema.air_MemAlignReadByte.airIndex ∧
    readByteProfile.unpackedWords = 10 ∧ readByteProfile.packedBits = 168 ∧
    readByteProfile.packedWords = 3 := by decide +kernel

/-- Flatten scalar/one-dimensional compiled witness symbols, preserving their
actual base index and rank. Main's independent native shapes above have only
these ranks; no general rank-to-native-offset shortcut is introduced. -/
def compiledCells : List (String × List Nat × Nat) :=
  ((SourceSchema.air_Main.symbols.filter fun symbol =>
      decide (symbol.kind = .witness ∧ symbol.stage = some 1)).flatMap fun symbol =>
    (List.range symbol.lengths.prod).map fun offset =>
      (symbol.name, if symbol.lengths = [] then [] else [offset], symbol.index + offset))

theorem actual_native_compiled_cell_order :
    (mainProfile.cells.zipIdx.map fun (cell, column) => (cell.field, cell.indices, column)) =
      compiledCells := by decide +kernel

def fragmentTokens? (name : String) : Option (List Token) :=
  (Extraction.RuntimeMainTraceLayout.sourceFragments.find? fun fragment => fragment.name == name).map
    (fun fragment => fragment.tokens.map NativeValuesLayout.semanticToken)

private def i := Token.ident
private def p (text : String) := Token.punct text false
private def par (tokens : List Token) := Token.group "parenthesis" (Tokens.ofList tokens)
private def bra (tokens : List Token) := Token.group "brace" (Tokens.ofList tokens)
private def brk (tokens : List Token) := Token.group "bracket" (Tokens.ofList tokens)
private def path (names : List String) : List Token :=
  (names.map fun name => [i name]).intersperse [p ":", p ":"] |>.flatten
private def call (name : String) (args : List Token) := [i name, par args]
private def typeCase (name : String) (arguments : List Token) :=
  path ["BitType", name] ++ (if arguments = [] then [] else [par arguments])

private def expectedSizeBody : List Token :=
  [i "match", i "ty", bra (
    typeCase "Bit" [i "_"] ++ [p "=", p ">", .literal "1", p ","] ++
    typeCase "Generic" [] ++ [p "=", p ">", .literal "1", p ","] ++
    typeCase "Array" [i "inner", p ",", i "len"] ++ [p "=", p ">",
      bra (call "calculate_field_size" [i "inner"] ++ [p "*", i "len"])])]

private def expectedFieldTypeBody : List Token :=
  [i "match", i "ty", bra (
    typeCase "Bit" [i "_"] ++ [p "=", p ">", i "quote", p "!", bra [i "F"], p ","] ++
    typeCase "Generic" [] ++ [p "=", p ">", i "quote", p "!", bra [i "F"], p ","] ++
    typeCase "Array" [i "inner", p ",", i "len"] ++ [p "=", p ">", bra (
      [i "let", i "inner_type", p "="] ++ call "generate_f_field_type" [i "inner"] ++
      [p ";", i "quote", p "!", bra [brk [p "#", i "inner_type", p ";", p "#", i "len"]]])])]

private def expectedBufferReturn : List Token :=
  [i "unsafe", bra (path ["Vec", "from_raw_parts"] ++
    [par [i "ptr", i "as", p "*", i "mut", i "F", p ",", i "original_len", p ",", i "original_capacity"]])]

private def typedLet (name typeName : String) (value : List Token) : List Token :=
  [i "let", i name, p ":", i typeName, p "="] ++ value ++ [p ";"]
private def mask (width : List Token) : List Token :=
  [par [par ([.literal "1u128", p "<", p "<"] ++ width), p "-", .literal "1"],
    i "as", i "u64"]
private def packedAt (index : List Token) : List Token :=
  [i "self", p ".", i "packed", brk index]
private def expectedArrayGetter : List Token :=
  [bra (
    [p "#", par [p "#", i "bounds_checks"], p "*"] ++
    typedLet "flat" "usize" [p "#", i "runtime_flat"] ++
    typedLet "bit_offset" "usize" [p "#", i "base_offset", p "+", i "flat", p "*", p "#", i "bit_width"] ++
    typedLet "word" "usize" [i "bit_offset", p "/", .literal "64"] ++
    typedLet "bit_start" "usize" [i "bit_offset", p "%", .literal "64"] ++
    typedLet "raw_value" "u64" (
      [i "if", i "bit_start", p "+", p "#", i "bit_width", p "<", p "=", .literal "64",
       bra (typedLet "mask_bits" "u64" (mask [p "#", i "bit_width"]) ++
         [par (packedAt [i "word"] ++ [p ">", p ">", i "bit_start"]), p "&", i "mask_bits"]),
       i "else", bra (
         typedLet "low_bits" "usize" [.literal "64", p "-", i "bit_start"] ++
         typedLet "high_bits" "usize" [p "#", i "bit_width", p "-", i "low_bits"] ++
         typedLet "low_mask" "u64" (mask [i "low_bits"]) ++
         typedLet "high_mask" "u64" (mask [i "high_bits"]) ++
         [i "let", i "low", p "=", par (packedAt [i "word"] ++ [p ">", p ">", i "bit_start"]),
           p "&", i "low_mask", p ";", i "let", i "high", p "="] ++
         packedAt [i "word", p "+", .literal "1"] ++ [p "&", i "high_mask", p ";",
           par [i "high", p "<", p "<", i "low_bits"], p "|", i "low"])]) ++
    [p "#", i "conversion"])]

/-- Independently stated source equations. Raw functions, fragments, source
locations and both packed accessor bodies remain in the emitted catalogue;
these pins support the bounded unpacked F-word model, not whole Rust execution. -/
def sourceRulesAccepted : Bool :=
  [ ("unpacked.row_size", call "calculate_row_size" [i "fields"]),
    ("unpacked.fields", call "get_unpacked_fields" [i "fields"]),
    ("calculate_field_size.body", expectedSizeBody),
    ("generate_f_field_type.body", expectedFieldTypeBody),
    ("packed.array.getter", expectedArrayGetter),
    ("GenericTrace.new.row_size", path ["R", "ROW_SIZE"]),
    ("GenericTrace.new.num_rows", [i "NUM_ROWS"]),
    ("GenericTrace.new.expected_len", [i "num_rows", p "*", i "row_size"]),
    ("GenericTrace.new.src_buffer_len", [i "buffer", p ".", i "len", par []]),
    ("GenericTrace.new.src_buffer_capacity", [i "buffer", p ".", i "capacity", par []]),
    ("GenericTrace.buffer.original_len", [i "self", p ".", i "src_buffer_len"]),
    ("GenericTrace.buffer.original_capacity", [i "self", p ".", i "src_buffer_capacity"]),
    ("GenericTrace.buffer.return", expectedBufferReturn),
    ("pil.SEGMENT_L1.assignment", [i "SEGMENT_L1", p "=", brk [.literal "1", p ",", .literal "0", p ".", p ".", p "."], p ";"]),
    ("pil.SEGMENT_STEP.assignment", [i "SEGMENT_STEP", p "=", brk [.literal "0", p ".", p ".", par [i "N", p "-", .literal "1"]], p ";"]),
    ("pil.STEP.assignment", [i "STEP", p "=", i "main_segment", p "*", i "N", p "+", i "SEGMENT_STEP", p ";"]),
    ("pil.addr0.assignment", [i "addr0", p "=", i "a_offset_imm0", p ";"]),
    ("pil.addr2.assignment", [i "addr2", p "=", i "store_offset", p "+", i "store_ind", p "*", i "a", brk [.literal "0"], p ";"])
  ].all fun (name, expected) => decide (fragmentTokens? name = some expected)

theorem actual_source_rules : sourceRulesAccepted = true := by decide +kernel

/-- First native packed word is exactly the two 32-bit A lanes in this source
profile. This does not claim a live native image has been authenticated. -/
theorem actual_first_packed_word :
    mainProfile.cells.take 2 = [⟨"a", [0], 32, 0⟩, ⟨"a", [1], 32, 32⟩] := by decide

def firstWordLanes (word : UInt64) : Nat × Nat :=
  (word.toNat % 2 ^ 32, word.toNat / 2 ^ 32)

theorem valid_both_A_lanes :
    (firstWordLanes 0).1 < 2 ^ 32 ∧ (firstWordLanes 0).2 < 2 ^ 32 ∧
    (firstWordLanes (UInt64.ofNat GL_prime)).1 < 2 ^ 32 ∧
    (firstWordLanes (UInt64.ofNat GL_prime)).2 < 2 ^ 32 := by decide +kernel

theorem distinct_decoded_lanes :
    firstWordLanes 0 ≠ firstWordLanes (UInt64.ofNat GL_prime) := by decide +kernel

/-- Reuses the source owner's exact native conditional canonicalization, never
a second field decoder or word store. This is an information-loss obstruction,
not an accepted forgery, reachable execution, Rust ABI theorem or source bug. -/
theorem no_canonical_field_only_packed_decoder :
    ¬ ∃ decode : FGL → Nat × Nat, ∀ word : UInt64,
      decode (MemAlignWriteByte.RawSource.NativeTraceWords.unpackedField word) =
        firstWordLanes word := by
  rintro ⟨decode, hdecode⟩
  have first := hdecode 0
  have second := hdecode (UInt64.ofNat GL_prime)
  rw [MemAlignWriteByte.RawSource.NativeTraceWords.unpacked_zero] at first
  rw [MemAlignWriteByte.RawSource.NativeTraceWords.unpacked_prime] at second
  exact distinct_decoded_lanes (first.symm.trans second)

end ZiskFv.AirsClean.PublicIoMainTraceLayout
