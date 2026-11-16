import Extraction.RuntimeNativeValuesLayout
import ZiskFv.AirsClean.MemAlignWriteByte.RawSource
import ZiskFv.Field.Goldilocks

/-! INTERNAL bounded source-pinned F-word layout interpretation.
The actual native declaration AST and actual values!/buffer AST are independent
inputs to the pins below. No Rust compiler/C-ABI/pointer authentication follows.
PIL logical indices are NEVER used as native addresses. Source setup/map/row
addressing remains owned by RawSource.Native's source-object constructor. -/
namespace ZiskFv.AirsClean.NativeValuesLayout

open Goldilocks Extraction.RuntimeNativeValuesLayout
open Extraction.LookupWiring
open ZiskFv.AirsClean.MemAlignWriteByte

/- Source whitespace is immaterial to this bounded token-tree interpretation;
raw tokens including punctuation jointness and all spans remain in metadata. -/
mutual
  def semanticToken : Token → Token
    | .ident value => .ident value
    | .literal value => .literal value
    | .punct value _ => .punct value false
    | .group delimiter children => .group delimiter (semanticTokens children)
  def semanticTokens : Tokens → Tokens
    | .nil => .nil
    | .cons head tail => .cons (semanticToken head) (semanticTokens tail)
end

def fragmentTokens? (name : String) : Option (List Token) :=
  (sourceFragments.find? fun fragment => fragment.name == name).map fun fragment =>
    fragment.tokens.map semanticToken

private def i := Token.ident
private def p (value : String) := Token.punct value false
private def par (children : List Token) := Token.group "parenthesis" (Tokens.ofList children)
private def bra (children : List Token) := Token.group "brace" (Tokens.ofList children)
private def brk (children : List Token) := Token.group "bracket" (Tokens.ofList children)
private def path (names : List String) : List Token :=
  (names.map fun name => [i name]).intersperse [p ":", p ":"] |>.flatten
private def field (base : List Token) (name : String) : List Token := base ++ [p ".", i name]
private def call (callee args : List Token) : List Token := callee ++ [par args]
private def method (base : List Token) (name : String) (args : List Token := []) : List Token :=
  call (field base name) args
private def comma (parts : List (List Token)) : List Token := (parts.intersperse [p ","]).flatten
private def trailingComma (parts : List (List Token)) : List Token :=
  (parts.map fun part => part ++ [p ","]).flatten
private def letStmt (name : String) (value : List Token) (mutable := false) : List Token :=
  [i "let"] ++ (if mutable then [i "mut"] else []) ++ [i name, p "="] ++ value ++ [p ";"]
private def assign (target value : List Token) : List Token := target ++ [p "="] ++ value ++ [p ";"]
private def structExpr (name : String) (fields : List (List Token)) : List Token :=
  [i name, bra (trailingComma fields)]
private def named (name : String) (value : List Token) : List Token := [i name, p ":"] ++ value
private def hole (name : String) : List Token := [p "#", i name]
private def genericMethod (base : List Token) (name : String) (types args : List Token) : List Token :=
  field base name ++ [p ":", p ":", p "<"] ++ types ++ [p ">", par args]
private def nullPtr := call (path ["std", "ptr", "null_mut"]) []
private def emptyVec := call (path ["Vec", "new"]) []
private def rustVec (value size : List Token) : List Token := [i "vec", p "!", brk (value ++ [p ";"] ++ size)]
private def selfField (name : String) := field [i "self"] name
private def pointerType := [p "*", i "mut", i "u8"]

/-- Independent expected scalar rules, not values repacked from the renderer. -/
def expectedScalarRules : List ScalarRule :=
  [⟨0, "F", "is_ident", "Ok", 1⟩, ⟨1, "FieldExtension", "is_ident", "Ok", 3⟩]

private def scalarPattern := path ["syn", "Type", "Path"] ++ [par [i "type_path"]]
private def arrayPattern := path ["syn", "Type", "Array"] ++ [par [i "type_array"]]
private def scalarGuard (tag : String) := call [i "is_ident"]
  [i "type_path", p ",", .literal s!"\"{tag}\""]

private def expectedIdentBody : List Token :=
  [bra (method (method (field (field [i "type_path"] "path") "segments") "last") "is_some_and"
    ([p "|", i "seg", p "|"] ++ field [i "seg"] "ident" ++ [p "=", p "=", i "name"]))]

private def expectedFieldDefinition : List Token :=
  field (method (field [i "fields"] "named") "iter") "map" ++
  [par [p "|", i "field", p "|", bra (
    [i "let", i "Field", bra [i "ident", p ",", i "ty", p ",", p ".", p "."], p "=", i "field", p ";",
     i "quote", p "!", bra ([i "pub"] ++ hole "ident" ++ [p ":"] ++ hole "ty" ++ [p ","])])]]

private def expectedRowStruct : List Token :=
  [i "quote", p "!", bra (
    [p "#", brk [i "repr", par [i "C"]],
     p "#", brk [i "derive", par [i "Debug", p ",", i "Clone", p ",", i "Copy"]],
     i "pub", i "struct"] ++ hole "row_struct_name" ++ [p "<"] ++ hole "generics" ++
    [p ">", bra [p "#", par (hole "field_definitions"), p "*"], i "impl", p "<"] ++
    hole "generics" ++ [p ":", i "Copy", p ">"] ++ hole "row_struct_name" ++
    [p "<"] ++ hole "generics" ++ [p ">", bra (
      [i "pub", i "const", i "TOTAL_SIZE", p ":", i "usize", p "="] ++ hole "total_size" ++ [p ";"])])]

private def expectedTotalSize : List Token :=
  let mapped := method (method (field [i "fields"] "named") "iter") "map"
    ([p "|", i "field", p "|"] ++ call [i "calculate_field_slots"] ([p "&"] ++ field [i "field"] "ty"))
  let collected := genericMethod mapped "collect"
    [i "Result", p "<", i "Vec", p "<", i "usize", p ">", p ">"] [] ++ [p "?"]
  genericMethod (method collected "into_iter") "sum" [i "usize"] []

private def expectedArrayElement : List Token :=
  call [i "calculate_field_slots"] ([p "&"] ++ field [i "type_array"] "elem") ++ [p "?"]
private def expectedArrayResult : List Token := call [i "Ok"] [i "len", p "*", i "elem_slots"]

/-- The error handler cannot change a successful decimal parse. Its actual AST
is retained, but its diagnostic text is not a semantic layout promise. -/
def arrayLengthRule : Bool :=
  let ruleHead := genericMethod (method (method (field [i "type_array"] "len") "to_token_stream")
    "to_string") "parse" [i "usize"] []
  match fragmentTokens? "array_rule.len" with
  | some tokens =>
    decide (tokens.take ruleHead.length = ruleHead) &&
      match tokens.drop ruleHead.length with
      | [.punct "." _, .ident "map_err", .group "parenthesis" _, .punct "?" _] => true
      | _ => false
  | none => false

private def rowType : List Token := hole "row_struct_name" ++ [p "<"] ++ hole "generics" ++ [p ">"]
private def pointerView (receiver : List Token) : List Token :=
  [i "unsafe", bra (
    letStmt "ptr" (method receiver "as_mut_ptr" ++ [i "as", p "*", i "mut"] ++ rowType) ++
    [p "&", i "mut", p "*", i "ptr"])]

private def expectedNew : List Token :=
  let size := hole "row_struct_name" ++ [p ":", p ":", p "<"] ++ hole "generics" ++
    [p ">", p ":", p ":", i "TOTAL_SIZE"]
  let initial := hole "generics" ++ [p ":", p ":", i "default", par []]
  letStmt "buffer" (rustVec initial size) true ++
  letStmt "slice_values" (pointerView [i "buffer"]) ++
  hole "values_struct_name" ++ [bra [i "buffer", p ":", i "buffer", p ",", i "slice_values", p ","]]

private def expectedGuardView : List Token :=
  letStmt "slice_values" (pointerView [i "external_buffer_rw"]) ++ hole "values_struct_name" ++
  [bra ([i "buffer", p ":"] ++ emptyVec ++ [p ",", i "slice_values", p ","])]
private def expectedGetBuffer : List Token :=
  letStmt "buffer" (call (path ["std", "mem", "take"]) ([p "&", i "mut"] ++ selfField "buffer")) ++ [i "buffer"]
private def expectedSetter (target parameter : String) : List Token :=
  [bra (assign (selfField target) (call [i "Some"] [i parameter]) ++ [i "self"])]
private def expectedGetter (storage : String) : List Token :=
  [bra (method (selfField storage) "as_ptr" ++ [i "as"] ++ pointerType)]
private def expectedInit (storage : String) : List Token :=
  [bra (assign (selfField storage) (rustVec (path ["F", "ZERO"]) [i "size"]))]

private def expectedAirInstanceNew : List Token :=
  let info (name : String) := field [i "trace_info"] name
  [bra (
    letStmt "airgroup_id" (info "airgroup_id") ++ letStmt "air_id" (info "air_id") ++
    letStmt "num_rows" (info "num_rows") ++
    letStmt "airvalues" (method (info "air_values") "unwrap_or_default") ++
    letStmt "airgroup_values" (method (info "airgroup_values") "unwrap_or_default") ++
    structExpr "AirInstance" [[i "airgroup_id"], [i "air_id"], [i "num_rows"],
      named "n_cols_trace" (info "n_cols"), named "trace" (info "trace"),
      named "aux_trace" emptyVec, named "custom_commits_fixed" emptyVec,
      [i "airgroup_values"], [i "airvalues"], named "evals" emptyVec, named "challenges" emptyVec,
      named "shared_buffer" (info "shared_buffer"), named "fixed" emptyVec,
      named "is_packed" (info "is_packed"), named "stream_id" [.literal "0"]])]

private def expectedFromTrace : List Token :=
  let trace := field [i "traces"] "trace"
  let custom := method (field [i "traces"] "custom_traces") "as_mut"
  let customBody :=
    letStmt "traces" emptyVec true ++
    [i "for", i "custom_trace", i "in"] ++ method [i "custom_traces"] "iter_mut" ++
    [bra (method [i "traces"] "push" (structExpr "CustomCommitInfo"
      [named "trace" (method [i "custom_trace"] "get_buffer"),
       named "commit_id" (method (method [i "custom_trace"] "commit_id") "unwrap")]) ++ [p ";"])] ++
    assign [i "trace_info"] (method [i "trace_info"] "with_custom_traces" [i "traces"])
  [bra (
    letStmt "trace_info" (call (path ["TraceInfo", "new"]) (comma
      ((["airgroup_id", "air_id", "num_cols", "num_rows", "get_buffer", "is_shared_buffer", "is_packed"].map
        fun name => method trace name) ++ [[]]))) true ++
    [i "if", i "let", i "Some", par [i "custom_traces"], p "="] ++ custom ++ [bra customBody] ++
    [i "if", i "let", i "Some", par [i "air_values"], p "="] ++
    method (field [i "traces"] "air_values") "as_mut" ++
    [bra (assign [i "trace_info"] (method [i "trace_info"] "with_air_values"
      (method [i "air_values"] "get_buffer")))] ++
    call (path ["AirInstance", "new"]) [i "trace_info"])]

private def expectedParams : List Token :=
  let fromSlot (name : String) := method [i "air_instance"] name
  let fromSelf (name : String) := method [i "self"] name
  let select (yes no : List Token) := [i "if", i "gen_proof", bra yes, i "else", bra no]
  [bra (
    letStmt "air_instance" (method (method (selfField "air_instances" ++ [brk [i "instance_id"]]) "read") "unwrap") ++
    letStmt "challenges" (select (fromSlot "get_challenges_ptr") (fromSelf "get_challenges_ptr")) ++
    [i "let", i "aux_trace", p ":"] ++ pointerType ++ [p "="] ++
    select nullPtr (fromSlot "get_aux_trace_ptr") ++ [p ";", i "let", i "const_pols", p ":"] ++
    pointerType ++ [p "="] ++ select nullPtr (fromSlot "get_fixed_ptr") ++ [p ";"] ++
    structExpr "StepsParams" [named "trace" (fromSlot "get_trace_ptr"), [i "aux_trace"],
      named "public_inputs" (fromSelf "get_publics_ptr"), named "proof_values" (fromSelf "get_proof_values_ptr"),
      [i "challenges"], named "airgroup_values" (fromSlot "get_airgroup_values_ptr"),
      named "airvalues" (fromSlot "get_airvalues_ptr"), named "evals" (fromSlot "get_evals_ptr"),
      named "xdivxsub" nullPtr, named "p_const_pols" [i "const_pols"], named "p_const_tree" nullPtr,
      named "custom_commits_fixed" (fromSlot "get_custom_commits_fixed_ptr")])]

def storageHeaderAccepted : Bool :=
  let storageHead := [i "pub", i "struct"] ++ hole "values_struct_name" ++
    [p "<", p "'", i "a", p ","] ++ hole "generics" ++
    [p ">", bra (
      [i "pub", i "buffer", p ":", i "Vec", p "<"] ++ hole "generics" ++ [p ">", p ",",
       i "pub", i "slice_values", p ":", p "&", p "'", i "a", i "mut"] ++
      rowType ++ [p ","])]
  match fragmentTokens? "values_impl.values_struct" with
  | some [.ident "quote", .punct "!" _, .group "brace" body] =>
      decide (body.toList.take storageHead.length = storageHead)
  | _ => false

/-- A closed conjunction over independently expected AST features. No caller
supplies a source-rule equality, successful parse, layout or authentication. -/
def rulesAccepted : Bool :=
  decide (scalarRules = expectedScalarRules ∧ extensionAlias = .array .f 3 "3" ∧
    slotArmCount = 4 ∧ arrayArmIndex = 2) &&
  ([ ("slot_rule.scrutinee", [i "ty"]),
     ("scalar_rule.0.pattern", scalarPattern), ("scalar_rule.1.pattern", scalarPattern),
     ("scalar_rule.0.guard", scalarGuard "F"), ("scalar_rule.1.guard", scalarGuard "FieldExtension"),
     ("array_rule.pattern", arrayPattern), ("array_rule.elem_slots", expectedArrayElement),
     ("array_rule.result", expectedArrayResult), ("is_ident", expectedIdentBody),
     ("values_impl.field_definitions", expectedFieldDefinition),
     ("values_impl.row_struct", expectedRowStruct), ("values_impl.total_size", expectedTotalSize),
     ("values_impl.quoted.new", expectedNew), ("values_impl.quoted.from_vec_guard", expectedGuardView),
     ("values_impl.quoted.get_buffer", expectedGetBuffer),
     ("TraceInfo.with_air_values", expectedSetter "air_values" "air_values"),
     ("FromTrace.with_air_values", expectedSetter "air_values" "air_values"),
     -- Actual mechanical distinction: no invented GROUP transfer via TraceInfo.
     ("TraceInfo.with_airgroup_values", expectedSetter "air_values" "airgroup_values"),
     ("FromTrace.with_airgroup_values", expectedSetter "airgroup_values" "airgroup_values"),
     ("AirInstance.new", expectedAirInstanceNew), ("AirInstance.new_from_trace", expectedFromTrace),
     ("AirInstance.get_airvalues_ptr", expectedGetter "airvalues"),
     ("AirInstance.get_airgroup_values_ptr", expectedGetter "airgroup_values"),
     ("AirInstance.init_airvalues", expectedInit "airvalues"),
     ("AirInstance.init_airgroup_values", expectedInit "airgroup_values"),
     ("ProofCtx.get_air_instance_params", expectedParams)] : List (String × List Token)).all
       (fun (name, expected) => decide (fragmentTokens? name = some expected)) &&
       arrayLengthRule && storageHeaderAccepted

/-- This independently pinned AST check is intentionally a kernel obligation,
not a renderer assertion or comparison of a source string with itself. -/
theorem actual_rules_accepted : rulesAccepted = true := by decide +kernel

def scalarWidth? (tag : String) : Option Nat :=
  (scalarRules.find? fun rule => rule.typeTag == tag).map ScalarRule.width

def slots? : NativeType → Option Nat
  | .f => scalarWidth? "F"
  | .extensionF => scalarWidth? "FieldExtension"
  | .array element length _ => do return length * (← slots? element)

def declaration? (name : String) : Option Declaration :=
  match declarations.filter (fun declaration => declaration.name == name) with
  | [declaration] => some declaration
  | _ => none

def fieldBase? (fields : List Extraction.RuntimeNativeValuesLayout.Field) (name : String)
    (offset : Nat := 0) : Option (NativeType × Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
    if field.name == name then some (field.nativeType, offset)
    else do fieldBase? rest name (offset + (← slots? field.nativeType))

def element? : NativeType → List Nat → Nat → Option (NativeType × Nat)
  | .array element length _, index :: rest, offset =>
    if index < length then do element? element rest (offset + index * (← slots? element)) else none
  | nativeType, [], offset => some (nativeType, offset)
  | _, _, _ => none

/-- The closed source-rule pin is checked once by `actual_rules_accepted`,
not recomputed for each buffer address. -/
def address? (declarationName fieldName : String) (indices : List Nat) (expected : NativeType) : Option Nat := do
  let declaration ← declaration? declarationName
  let (nativeType, base) ← fieldBase? declaration.fields fieldName
  let (leaf, address) ← element? nativeType indices base
  if leaf = expected then some address else none

theorem address_rules_checked (declarationName fieldName : String) (indices : List Nat)
    (expected : NativeType) :
    address? declarationName fieldName indices expected = (do
      let declaration ← declaration? declarationName
      let (nativeType, base) ← fieldBase? declaration.fields fieldName
      let (leaf, address) ← element? nativeType indices base
      if leaf = expected then some address else none) := rfl

inductive Air where | main | mem | binary | byte | readByte | writeByte
  deriving DecidableEq

def Air.nativeName : Air → String
  | .main => "Main" | .mem => "Mem" | .binary => "Binary" | .byte => "MemAlignByte"
  | .readByte => "MemAlignReadByte" | .writeByte => "MemAlignWriteByte"

def Air.schema : Air → Extraction.LookupWiring.SourceSchema.Air
  | .main => SourceSchema.air_Main | .mem => SourceSchema.air_Mem | .binary => SourceSchema.air_Binary
  | .byte => SourceSchema.air_MemAlignByte | .readByte => SourceSchema.air_MemAlignReadByte
  | .writeByte => SourceSchema.air_MemAlignWriteByte

def Air.expectedIndex : Air → Nat
  | .main => 12 | .mem => 14 | .binary => 22 | .byte => 18
  | .readByte => 19 | .writeByte => 20

theorem actual_AIR_scope (air : Air) :
    air.schema.groupIndex = 0 ∧ air.schema.airIndex = air.expectedIndex ∧
    air.schema.groupName = "Zisk" ∧ air.schema.airName = air.nativeName := by
  cases air <;> decide

def scalarAddress? (air : Air) (field : String) (indices : List Nat := []) : Option Nat :=
  address? (air.nativeName ++ "AirValues") field indices .f

def groupAddress? (air : Air) : Option Nat :=
  address? (air.nativeName ++ "AirGroupValues") "gsum_result" [] .extensionF

def mainAddresses : List (Option Nat) :=
  [scalarAddress? .main "main_last_segment", scalarAddress? .main "main_segment",
   scalarAddress? .main "segment_initial_pc", scalarAddress? .main "segment_previous_c" [0],
   scalarAddress? .main "segment_previous_c" [1], scalarAddress? .main "segment_next_pc",
   scalarAddress? .main "segment_last_c" [0], scalarAddress? .main "segment_last_c" [1]]

/-- Six independently expected PIL declarations for eight base cells. -/
def expectedContinuationSymbols : List SourceSchema.Symbol :=
  [⟨some 0, some 12, "Main.main_last_segment", .airValue, some 1, 0, 0, []⟩,
   ⟨some 0, some 12, "Main.main_segment", .airValue, some 1, 1, 0, []⟩,
   ⟨some 0, some 12, "Main.segment_initial_pc", .airValue, some 1, 2, 0, []⟩,
   ⟨some 0, some 12, "Main.segment_previous_c", .airValue, some 1, 3, 1, [2]⟩,
   ⟨some 0, some 12, "Main.segment_next_pc", .airValue, some 1, 5, 0, []⟩,
   ⟨some 0, some 12, "Main.segment_last_c", .airValue, some 1, 6, 1, [2]⟩]

def continuationSymbols (schema : SourceSchema.Air) : List SourceSchema.Symbol :=
  schema.symbols.filter fun symbol =>
    decide (symbol.kind = .airValue ∧ symbol.stage = some 1 ∧ symbol.index < 8)

theorem actual_continuation_symbols :
    continuationSymbols SourceSchema.air_Main = expectedContinuationSymbols := by decide

/-- Logical PIL indices; the native addresses above are derived separately. -/
def logicalCells (symbols : List SourceSchema.Symbol) : List Nat :=
  symbols.flatMap fun symbol =>
    (List.range symbol.lengths.prod).map fun offset => symbol.index + offset

theorem actual_logical_cells_once :
    logicalCells (continuationSymbols SourceSchema.air_Main) = List.range 8 := by decide

def declarationFields? (name : String) : Option (List (String × NativeType)) :=
  (declaration? name).map fun declaration =>
    declaration.fields.map fun field => (field.name, field.nativeType)

theorem actual_main_native_prefix :
    (declarationFields? "MainAirValues").map (List.take 6) =
      some [("main_last_segment", .f), ("main_segment", .f), ("segment_initial_pc", .f),
        ("segment_previous_c", .array .f 2 "2"), ("segment_next_pc", .f),
        ("segment_last_c", .array .f 2 "2")] := by decide

theorem actual_mem_native_fields :
    declarationFields? "MemAirValues" = some [
      ("segment_id", .f), ("is_first_segment", .f), ("is_last_segment", .f),
      ("previous_segment_value", .array .f 2 "2"), ("previous_segment_step", .f),
      ("previous_segment_addr", .f), ("segment_last_value", .array .f 2 "2"),
      ("segment_last_step", .f), ("segment_last_addr", .f),
      ("distance_base", .array .f 2 "2"), ("distance_end", .array .f 2 "2"),
      ("im_direct", .array .extensionF 6 "6")] := by decide

theorem actual_mem_inverse_symbol :
    (SourceSchema.air_Mem.symbols.filter fun symbol =>
      symbol.name == "Mem.im_direct") =
      [⟨some 0, some 14, "Mem.im_direct", .airValue, some 2, 15, 1, [6]⟩] := by decide

theorem actual_group_native_fields (air : Air) :
    declarationFields? (air.nativeName ++ "AirGroupValues") =
      some [("gsum_result", .extensionF)] := by
  cases air <;> decide

theorem actual_group_symbol (air : Air) :
    (air.schema.symbols.filter fun symbol => decide (symbol.kind = .airGroupValue)) =
      [⟨some 0, none, "Zisk.gsum_result", .airGroupValue, some 2, 0, 0, []⟩] := by
  cases air <;> decide

theorem actual_mem_inverse_addresses (index : Fin 6) :
    address? "MemAirValues" "im_direct" [index.val] .extensionF =
      some (15 + 3 * index.val) := by
  fin_cases index <;> rw [address_rules_checked] <;> decide

theorem actual_main_addresses : mainAddresses = (List.range 8).map some := by
  simp only [mainAddresses, scalarAddress?, address_rules_checked]
  decide

theorem actual_main_PIL_native_agreement :
    mainAddresses = (logicalCells (continuationSymbols SourceSchema.air_Main)).map some := by
  rw [actual_logical_cells_once, actual_main_addresses]

theorem actual_group_address (air : Air) : groupAddress? air = some 0 := by
  cases air <;> rw [groupAddress?, address_rules_checked] <;> decide

inductive PaddingAir where | binary | byte | readByte | writeByte deriving DecidableEq

def PaddingAir.air : PaddingAir → Air
  | .binary => .binary | .byte => .byte | .readByte => .readByte | .writeByte => .writeByte

def paddingAddress? (air : PaddingAir) : Option Nat := scalarAddress? air.air "padding_size"

theorem actual_padding_address (air : PaddingAir) : paddingAddress? air = some 0 := by
  cases air <;>
    simp only [paddingAddress?, PaddingAir.air, scalarAddress?, address_rules_checked] <;> decide

def PaddingAir.inverseCount : PaddingAir → Nat
  | .binary => 1 | .byte => 2 | .readByte => 2 | .writeByte => 3

def PaddingAir.inverseLiteral : PaddingAir → String
  | .binary => "1" | .byte => "2" | .readByte => "2" | .writeByte => "3"

theorem actual_padding_native_fields (air : PaddingAir) :
    declarationFields? (air.air.nativeName ++ "AirValues") =
      some [("padding_size", .f),
        ("im_direct", .array .extensionF air.inverseCount air.inverseLiteral)] := by
  cases air <;> decide

theorem actual_padding_symbol (air : PaddingAir) :
    (air.air.schema.symbols.filter fun symbol =>
      decide (symbol.kind = .airValue ∧ symbol.stage = some 1)) =
      [⟨some 0, some air.air.expectedIndex, air.air.nativeName ++ ".padding_size",
        .airValue, some 1, 0, 0, []⟩] := by
  cases air <;> decide


/-- Same selected Params buffer, not free values or a caller's equality promise. -/
def mainWords? (params : RawSource.Params FGL) : Option (Vector FGL 8) := do
  let addresses ← mainAddresses.mapM id
  match addresses with
  | [a, b, c, d, e, f, g, h] =>
    return #v[← RawSource.readWord? params .airValue a, ← RawSource.readWord? params .airValue b,
      ← RawSource.readWord? params .airValue c, ← RawSource.readWord? params .airValue d,
      ← RawSource.readWord? params .airValue e, ← RawSource.readWord? params .airValue f,
      ← RawSource.readWord? params .airValue g, ← RawSource.readWord? params .airValue h]
  | _ => none

def paddingValue? (air : PaddingAir) (params : RawSource.Params FGL) : Option FGL := do
  let address ← paddingAddress? air
  RawSource.readWord? params .airValue address

/-- Separate AIR-GROUP buffer; never AIR values or a claimed FromTrace GROUP path. -/
def groupWords? (air : Air) (params : RawSource.Params FGL) : Option (Vector FGL 3) := do
  let address ← groupAddress? air
  return #v[← RawSource.readWord? params .airGroupValue address,
    ← RawSource.readWord? params .airGroupValue (address + 1),
    ← RawSource.readWord? params .airGroupValue (address + 2)]

theorem padding_reads_actual_buffer (air : PaddingAir) (params : RawSource.Params FGL) :
    paddingValue? air params = params.airvalues[0]? := by
  simp [paddingValue?, actual_padding_address, RawSource.readWord?, RawSource.buffer?]

theorem group_reads_actual_buffer (air : Air) (params : RawSource.Params FGL) :
    groupWords? air params = (do
      return #v[← params.airgroupValues[0]?, ← params.airgroupValues[1]?, ← params.airgroupValues[2]?]) := by
  simp [groupWords?, actual_group_address, RawSource.readWord?, RawSource.buffer?]

theorem main_reads_actual_buffer (params : RawSource.Params FGL) :
    mainWords? params = (do
      return #v[← params.airvalues[0]?, ← params.airvalues[1]?, ← params.airvalues[2]?,
        ← params.airvalues[3]?, ← params.airvalues[4]?, ← params.airvalues[5]?,
        ← params.airvalues[6]?, ← params.airvalues[7]?]) := by
  have haddresses : mainAddresses = [some 0, some 1, some 2, some 3,
      some 4, some 5, some 6, some 7] := by
    rw [actual_main_addresses]
    rfl
  simp [mainWords?, haddresses, RawSource.readWord?, RawSource.buffer?]

/-- The six Mem Direct inverse elements are Ext3 AFTER fifteen stage1 F words.
This is not a row-auxTrace address or an AIR-GROUP accessor. -/
def memInverseWords? (index : Fin 6) (params : RawSource.Params FGL) :
    Option (Vector FGL 3) := do
  let address ← address? "MemAirValues" "im_direct" [index.val] .extensionF
  return #v[← RawSource.readWord? params .airValue address,
    ← RawSource.readWord? params .airValue (address + 1),
    ← RawSource.readWord? params .airValue (address + 2)]

theorem mem_inverse_reads_actual_buffer (index : Fin 6) (params : RawSource.Params FGL) :
    memInverseWords? index params = (do
      return #v[← params.airvalues[15 + 3 * index.val]?,
        ← params.airvalues[(15 + 3 * index.val) + 1]?,
        ← params.airvalues[(15 + 3 * index.val) + 2]?]) := by
  simp [memInverseWords?, actual_mem_inverse_addresses, RawSource.readWord?, RawSource.buffer?]

end ZiskFv.AirsClean.NativeValuesLayout
