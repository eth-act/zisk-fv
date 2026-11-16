//! Bounded Main/Binary/Byte/Read trace_row! profiles; child of the values renderer.
//! Reuses its AST fragments, spans, token representation and Lean serializer.
//! This emits source facts, NOT Rust/C-ABI or native-buffer authentication.
use super::*;

#[derive(Clone)]
enum TraceShape { Bits(usize), Field, Array(Box<TraceShape>, usize) }
struct TraceField { name: syn::Ident, shape: TraceShape }
struct TraceDeclaration { name: syn::Ident, fields: Vec<TraceField> }

fn trace_shape(input: ParseStream<'_>) -> syn::Result<TraceShape> {
    if input.peek(syn::token::Bracket) {
        let content; syn::bracketed!(content in input);
        let element = trace_shape(&content)?;
        content.parse::<syn::Token![;]>()?;
        let length = content.parse::<syn::LitInt>()?.base10_parse()?;
        if !content.is_empty() { return Err(content.error("unsupported trace array length")) }
        return Ok(TraceShape::Array(Box::new(element), length))
    }
    let tag: syn::Ident = input.parse()?;
    Ok(match tag.to_string().as_str() {
        "bit" => TraceShape::Bits(1), "u8" => TraceShape::Bits(8),
        "u16" => TraceShape::Bits(16), "u32" => TraceShape::Bits(32),
        "u64" => TraceShape::Bits(64), "F" => TraceShape::Field,
        "ubit" => {
            let content; syn::parenthesized!(content in input);
            let width = content.parse::<syn::LitInt>()?.base10_parse()?;
            if !(1..=64).contains(&width) || !content.is_empty() {
                return Err(content.error("unsupported trace bit width"))
            }
            TraceShape::Bits(width)
        }
        _ => return Err(syn::Error::new_spanned(tag, "unsupported Main trace profile type")),
    })
}
impl Parse for TraceDeclaration {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name = input.parse()?;
        let generics: syn::Generics = input.parse()?;
        bare_f(&generics).map_err(|error| input.error(error.to_string()))?;
        let content; syn::braced!(content in input);
        let mut fields = Vec::new();
        while !content.is_empty() {
            let name = content.parse()?;
            content.parse::<syn::Token![:]>()?;
            fields.push(TraceField { name, shape: trace_shape(&content)? });
            if !content.is_empty() { content.parse::<syn::Token![,]>()?; }
        }
        if !input.is_empty() { return Err(input.error("unsupported trace declaration suffix")) }
        Ok(Self { name, fields })
    }
}

struct ScalarCell { field: String, indices: Vec<usize>, width: usize, bit_offset: usize }
fn scalar_cells(shape: &TraceShape, field: &str, indices: &mut Vec<usize>,
    bit_offset: &mut usize, result: &mut Vec<ScalarCell>) -> Result<()> {
    match shape {
        TraceShape::Bits(width) => {
            result.push(ScalarCell { field: field.to_owned(), indices: indices.clone(),
                width: *width, bit_offset: *bit_offset });
            *bit_offset += width;
        }
        TraceShape::Array(element, length) => {
            for index in 0..*length {
                indices.push(index); scalar_cells(element, field, indices, bit_offset, result)?;
                indices.pop();
            }
        }
        TraceShape::Field => bail!("Main trace contains generic F storage; packed profile not implemented"),
    }
    Ok(())
}

fn unique_statement<'a>(block: &'a syn::Block, label: &str,
    matches: impl Fn(&syn::Stmt) -> bool) -> Result<&'a syn::Stmt> {
    let mut found = None;
    for statement in &block.stmts {
        if matches(statement) {
            ensure!(found.replace(statement).is_none(), "duplicate actual source statement {label}");
        }
    }
    found.with_context(|| format!("missing actual source statement {label}"))
}

fn is_offset_target(expression: &syn::Expr) -> bool {
    let syn::Expr::Unary(deref) = expression else { return false };
    matches!(deref.op, syn::UnOp::Deref(_)) &&
        matches!(deref.expr.as_ref(), syn::Expr::Path(path) if path.qself.is_none() && path.path.is_ident("offset"))
}

fn dimensions_initializer(block: &syn::Block) -> Result<&syn::Expr> {
    let statement = unique_statement(block, "array dimensions tuple", |statement| {
        let syn::Stmt::Local(local) = statement else { return false };
        let syn::Pat::Tuple(tuple) = &local.pat else { return false };
        tuple.elems.len() == 3 && tuple.elems.iter().zip(["bit_width", "dims", "acc_dims"])
            .all(|(pattern, name)| matches!(pattern, syn::Pat::Ident(pattern) if pattern.ident == name))
    })?;
    let syn::Stmt::Local(local) = statement else { bail!("actual dimensions selection is not a local binding") };
    Ok(local.init.as_ref().context("actual dimensions tuple lacks initializer")?.expr.as_ref())
}

fn pil_assignments(tokens: proc_macro2::TokenStream, source: &str,
    result: &mut Vec<Fragment>) -> Result<()> {
    let tokens: Vec<_> = tokens.into_iter().collect();
    for (index, token) in tokens.iter().enumerate() {
        if let proc_macro2::TokenTree::Group(group) = token {
            pil_assignments(group.stream(), source, result)?;
        }
        let proc_macro2::TokenTree::Ident(name) = token else { continue };
        if !["addr0", "addr2", "SEGMENT_L1", "SEGMENT_STEP", "STEP"].iter().any(|target| name == *target) { continue }
        let Some(proc_macro2::TokenTree::Punct(equal)) = tokens.get(index + 1) else { continue };
        if equal.as_char() != '=' { continue }
        if tokens.get(index + 2).is_some_and(|next|
            matches!(next, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == '=')) { continue }
        let end = tokens[index + 2..].iter().position(|token|
            matches!(token, proc_macro2::TokenTree::Punct(punct) if punct.as_char() == ';'))
            .context("unterminated actual PIL address assignment")? + index + 2;
        let span = token.span().join(tokens[end].span()).context("cannot join actual PIL source spans")?;
        result.push(fragment(&format!("pil.{name}.assignment"), "main/pil/main.pil", source, span)?);
    }
    Ok(())
}

struct RenderedProfile {
    output_name: &'static str,
    native_name: String,
    row_parameter: String,
    constants: [usize; 3],
    cells: Vec<ScalarCell>,
    packed_bits: usize,
}

fn extract_profile(ast: &syn::File, source: &str, output_name: &'static str,
    row_name: &str, alias_name: &str, fragments: &mut Vec<Fragment>) -> Result<RenderedProfile> {
    let mut declaration = None;
    let mut alias = None;
    for item in &ast.items {
        if let syn::Item::Macro(item) = item {
            if item.mac.path.is_ident("trace_row") {
                let Some(proc_macro2::TokenTree::Ident(name)) = item.mac.tokens.clone().into_iter().next() else { continue };
                if name != row_name { continue }
                let parsed: TraceDeclaration = syn::parse2(item.mac.tokens.clone())
                    .with_context(|| format!("unsupported actual {row_name} declaration"))?;
                ensure!(declaration.replace(parsed).is_none(), "duplicate actual {row_name}");
                fragments.push(fragment(row_name, "pil_helpers/traces.rs", source, item.span())?);
            }
        }
        if let syn::Item::Type(item) = item {
            if item.ident == alias_name {
                ensure!(alias.replace(item).is_none(), "duplicate actual {alias_name}");
                fragments.push(fragment(&format!("{alias_name}.alias"), "pil_helpers/traces.rs", source, item.span())?);
            }
        }
    }
    let declaration = declaration.with_context(|| format!("missing actual {row_name}"))?;
    let alias = alias.with_context(|| format!("missing actual {alias_name}"))?;
    let syn::Type::Path(alias_type) = alias.ty.as_ref() else { bail!("unsupported {alias_name} alias") };
    let segment = alias_type.path.segments.last().context("empty native trace alias path")?;
    ensure!(segment.ident == "GenericTrace", "{alias_name} no longer uses actual GenericTrace");
    let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments else { bail!("missing trace alias arguments") };
    let Some(syn::GenericArgument::Type(syn::Type::Path(row_type))) = arguments.args.first()
        else { bail!("unsupported actual trace row type parameter") };
    ensure!(row_type.qself.is_none() && row_type.path.segments.len() == 1, "unsupported row type path");
    let row_parameter = row_type.path.segments[0].ident.to_string();
    let mut constants = Vec::new();
    for argument in arguments.args.iter().skip(1) {
        let syn::GenericArgument::Const(syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(value), .. })) = argument
            else { bail!("unsupported actual trace alias row/group/AIR expression") };
        constants.push(value.base10_parse::<usize>()?);
    }
    ensure!(constants.len() == 3, "unsupported actual trace alias arity");
    let mut cells = Vec::new();
    let mut packed_bits = 0;
    for field in declaration.fields {
        scalar_cells(&field.shape, &field.name.to_string(), &mut Vec::new(), &mut packed_bits, &mut cells)?;
    }
    Ok(RenderedProfile { output_name, native_name: declaration.name.to_string(), row_parameter,
        constants: [constants[0], constants[1], constants[2]], cells, packed_bits })
}

/// A separate additive module; the existing FOUR-input render is unchanged.
pub(crate) fn render(traces: &str, trace_row: &str, packed_row: &str,
    unpacked_row: &str, generic_trace: &str, main_pil: &str) -> Result<String> {
    let traces_ast = syn::parse_file(traces).context("parsing actual trace declarations")?;
    let mut fragments = Vec::new();
    let mut profiles = Vec::new();
    for (output, row_name, alias_name) in [
        ("mainProfile", "MainTraceRow", "MainTrace"),
        ("binaryProfile", "BinaryTraceRow", "BinaryTrace"),
        ("byteProfile", "MemAlignByteTraceRow", "MemAlignByteTrace"),
        ("readByteProfile", "MemAlignReadByteTraceRow", "MemAlignReadByteTrace"),
    ] {
        profiles.push(extract_profile(&traces_ast, traces, output, row_name, alias_name, &mut fragments)?);
    }
    for (name, source, functions) in [
        ("macros/src/trace_row.rs", trace_row, &["parse_bit_type", "get_bit_count", "trace_row_entrypoint", "contains_generic", "compute_total_bits", "is_array", "collect_dimensions"][..]),
        ("macros/src/packed_row.rs", packed_row, &["packed_row_impl", "get_packed_fields", "get_packed_setters_getters", "add_packed_setter_getter", "add_packed_array_setter_getter", "emit_contained_packed_accessor", "emit_split_packed_accessor", "flatten_index_expr", "type_for_bitwidth"][..]),
        ("macros/src/unpacked_row.rs", unpacked_row, &["unpacked_row_impl", "get_unpacked_fields", "calculate_row_size", "calculate_field_size", "generate_f_field_type"][..]),
    ] {
        let ast = syn::parse_file(source).with_context(|| format!("parsing actual {name}"))?;
        if name == "macros/src/trace_row.rs" {
            fragments.push(fragment("TraceRowInput.parse", name, source,
                method(&ast, "TraceRowInput", "parse")?.span())?);
        }
        for function_name in functions {
            let body = function(&ast, function_name)?;
            fragments.push(fragment(function_name, name, source, body.span())?);
            let named_bindings: &[(&str, &str)] = match *function_name {
                "packed_row_impl" => &[
                    ("packed_row_impl.packed_bits", "packed_bits"),
                    ("packed_row_impl.packed_words", "packed_words"),
                    ("packed_row_impl.generic_field_count", "generic_field_count"),
                    ("packed_row_impl.total_row_size", "total_row_size")],
                "get_packed_setters_getters" => &[("packed.offset.initial", "offset")],
                "add_packed_setter_getter" => &[
                    ("scalar.bit_width", "bit_width"), ("scalar.rust_type", "rust_type"),
                    ("scalar.start", "start"), ("scalar.end", "end"),
                    ("scalar.word_start", "word_start"), ("scalar.word_end", "word_end"),
                    ("scalar.bit_start", "bit_start"), ("scalar.dispatch", "tokens")],
                "add_packed_array_setter_getter" => &[
                    ("array.rust_type", "rust_type"), ("array.runtime_idents", "runtime_idents"),
                    ("array.total_len", "total_len"), ("array.base_offset", "base_offset"),
                    ("array.runtime_flat", "runtime_flat"), ("array.conversion", "conversion")],
                "emit_contained_packed_accessor" =>
                    &[("scalar.contained.getter_conversion", "getter_conversion")],
                "emit_split_packed_accessor" =>
                    &[("scalar.split.getter_conversion", "getter_conversion")],
                _ => &[],
            };
            for (output_name, binding_name) in named_bindings {
                fragments.push(fragment(output_name, name, source, binding(&body.block, binding_name)?.span())?);
            }
            if ["contains_generic", "compute_total_bits", "is_array", "collect_dimensions", "flatten_index_expr", "type_for_bitwidth"]
                .contains(function_name) {
                fragments.push(fragment(&format!("{function_name}.body"), name, source, body.block.span())?);
            }
            if *function_name == "get_packed_setters_getters" {
                let statement = unique_statement(&body.block, "packed dispatch", |statement|
                    matches!(statement, syn::Stmt::Expr(syn::Expr::ForLoop(_), _)))?;
                fragments.push(fragment("packed.dispatch", name, source, statement.span())?);
            }
            if *function_name == "add_packed_setter_getter" {
                let statement = unique_statement(&body.block, "scalar offset update", |statement|
                    matches!(statement, syn::Stmt::Expr(syn::Expr::Assign(assign), Some(_))
                        if is_offset_target(&assign.left)))?;
                fragments.push(fragment("scalar.offset_update", name, source, statement.span())?);
            }
            if *function_name == "add_packed_array_setter_getter" {
                fragments.push(fragment("array.dimensions", name, source,
                    dimensions_initializer(&body.block)?.span())?);
                let statement = unique_statement(&body.block, "array offset update", |statement|
                    matches!(statement, syn::Stmt::Expr(syn::Expr::Binary(assign), Some(_))
                        if matches!(assign.op, syn::BinOp::AddAssign(_)) && is_offset_target(&assign.left)))?;
                fragments.push(fragment("array.offset_update", name, source, statement.span())?);
            }
            if *function_name == "calculate_field_size" || *function_name == "generate_f_field_type" {
                fragments.push(fragment(&format!("{function_name}.body"), name, source,
                    last_expression(&body.block)?.span())?);
            }
            if *function_name == "emit_contained_packed_accessor" || *function_name == "emit_split_packed_accessor" {
                let Some(syn::Stmt::Macro(quoted)) = body.block.stmts.last()
                    else { bail!("unsupported actual final accessor quote boundary in {function_name}") };
                ensure!(quoted.semi_token.is_none() && quoted.mac.path.is_ident("quote"),
                    "actual final accessor emission is not a quote! expression");
                let getter = quoted_body(quoted.mac.tokens.clone(), "getter_name")?;
                fragments.push(fragment(&format!("{function_name}.getter"), name, source, getter.span())?);
                let bindings: &[&str] = if *function_name == "emit_contained_packed_accessor" {
                    &["mask_bits"]
                } else { &["low_bits", "high_bits", "low_mask", "high_mask"] };
                for binding_name in bindings {
                    fragments.push(fragment(&format!("{function_name}.{binding_name}"), name, source,
                        binding(&body.block, binding_name)?.span())?);
                }
            }
            if *function_name == "add_packed_array_setter_getter" {
                let Some(syn::Stmt::Expr(syn::Expr::MethodCall(push), _)) = body.block.stmts.last()
                    else { bail!("unsupported actual packed array accessor emission boundary") };
                ensure!(push.method == "push" && push.args.len() == 1, "unsupported packed array quote sink");
                let getter = quoted_body(quote_tokens(push.args.first().unwrap())?, "getter_name")?;
                fragments.push(fragment("packed.array.getter", name, source, getter.span())?);
                fragments.push(fragment("packed.array.getter.signature", name, source,
                    quoted_signature(quote_tokens(push.args.first().unwrap())?, "getter_name")?)?);
            }
            if *function_name == "unpacked_row_impl" {
                fragments.push(fragment("unpacked.row_size", name, source, binding(&body.block, "row_size")?.span())?);
                fragments.push(fragment("unpacked.fields", name, source, binding(&body.block, "unpacked_fields")?.span())?);
            }
            if *function_name == "get_unpacked_fields" {
                let dispatch = unique_statement(&body.block, "actual unpacked field dispatch",
                    |statement| matches!(statement, syn::Stmt::Expr(syn::Expr::ForLoop(_), _)))?;
                fragments.push(fragment("unpacked.dispatch", name, source, dispatch.span())?);
            }
        }
    }
    let generic = syn::parse_file(generic_trace).context("parsing actual GenericTrace")?;
    for item in &generic.items {
        let syn::Item::Impl(item) = item else { continue };
        let syn::Type::Path(path) = item.self_ty.as_ref() else { continue };
        if !path.path.segments.last().is_some_and(|segment| segment.ident == "GenericTrace") || item.trait_.is_some() { continue }
        for member in &item.items {
            let syn::ImplItem::Fn(member) = member else { continue };
            let name = member.sig.ident.to_string();
            if ["new_from_vec", "get_buffer", "num_rows", "num_cols", "is_packed"].contains(&name.as_str()) {
                fragments.push(fragment(&format!("GenericTrace.{name}"), "common/src/trace.rs", generic_trace, member.span())?);
            }
            if name == "new_from_vec" {
                for binding_name in ["row_size", "num_rows", "expected_len", "src_buffer_len", "src_buffer_capacity", "src_element_size"] {
                    fragments.push(fragment(&format!("GenericTrace.new.{binding_name}"), "common/src/trace.rs", generic_trace, binding(&member.block, binding_name)?.span())?);
                }
            }
            if name == "get_buffer" {
                for binding_name in ["buffer", "original_len", "original_capacity"] {
                    fragments.push(fragment(&format!("GenericTrace.buffer.{binding_name}"), "common/src/trace.rs", generic_trace, binding(&member.block, binding_name)?.span())?);
                }
                fragments.push(fragment("GenericTrace.buffer.return", "common/src/trace.rs", generic_trace, last_expression(&member.block)?.span())?);
            }
        }
    }
    // PIL rotation apostrophes are not Rust tokens. Select only the actual
    // bounded single-assignment lines, without supplying expected RHS text.
    // Preserve every byte position/newline; the SAME token/span lexer then
    // projects these source statements, not a substitute PIL implementation.
    let mut selected = main_pil.as_bytes().iter().map(|byte|
        if *byte == b'\n' { b'\n' } else { b' ' }).collect::<Vec<_>>();
    let mut offset = 0;
    for line in main_pil.split_inclusive('\n') {
        if let Some((left, right)) = line.split_once('=') {
            let name = left.split_whitespace().last().unwrap_or("");
            if ["addr0", "addr2", "SEGMENT_L1", "SEGMENT_STEP", "STEP"].contains(&name)
                && !right.trim_start().starts_with('=') {
                selected[offset..offset + line.len()].copy_from_slice(line.as_bytes());
            }
        }
        offset += line.len();
    }
    let selected = String::from_utf8(selected).context("bounded PIL source projection is not UTF8")?;
    pil_assignments(proc_macro2::TokenStream::from_str(&selected)
        .map_err(|error| anyhow::anyhow!("lexing bounded actual Main PIL assignments: {error}"))?, main_pil, &mut fragments)?;
    let mut out = String::from("import Extraction.RuntimeNativeValuesLayout\n\nnamespace Extraction.RuntimeMainTraceLayout\nopen Extraction.RuntimeNativeValuesLayout\n\nstructure Cell where\n  field : String\n  indices : List Nat\n  width : Nat\n  bitOffset : Nat\n  deriving Repr, DecidableEq\n\nstructure Profile where\n  nativeName : String\n  rowParameter : String\n  nativeRows : Nat\n  nativeGroup : Nat\n  nativeAir : Nat\n  packedBits : Nat\n  cells : List Cell\n  deriving Repr, DecidableEq\n\ndef Profile.unpackedWords (profile : Profile) : Nat := profile.cells.length\ndef Profile.packedWords (profile : Profile) : Nat := (profile.packedBits + 63) / 64\n\n");
    for profile in profiles {
        writeln!(out, "def {} : Profile := ⟨{}, {}, {}, {}, {}, {}, [", profile.output_name,
            lean_string(&profile.native_name)?, lean_string(&profile.row_parameter)?,
            profile.constants[0], profile.constants[1], profile.constants[2], profile.packed_bits)?;
        for cell in profile.cells {
            writeln!(out, "  ⟨{}, [{}], {}, {}⟩,", lean_string(&cell.field)?,
                cell.indices.iter().map(usize::to_string).collect::<Vec<_>>().join(", "), cell.width, cell.bit_offset)?;
        }
        writeln!(out, "]⟩\n")?;
    }
    writeln!(out, "def sourceFragments : List SourceFragment := [")?;
    for fragment in fragments {
        let source = match fragment.source {
            "pil_helpers/traces.rs" => traces, "macros/src/trace_row.rs" => trace_row,
            "macros/src/packed_row.rs" => packed_row, "macros/src/unpacked_row.rs" => unpacked_row,
            "common/src/trace.rs" => generic_trace, "main/pil/main.pil" => main_pil,
            _ => bail!("unknown actual Main trace source owner"),
        };
        let bytes = fragment.span.byte_range(); let location = fragment.span.start();
        writeln!(out, "  ⟨{}, {}, {}, {}, {}, {}, {}, {}⟩,", lean_string(&fragment.name)?, lean_string(fragment.source)?, bytes.start, bytes.end, location.line, location.column,
            lean_string(source_slice(source, fragment.span)?)?, render_tokens(fragment.tokens)?)?;
    }
    writeln!(out, "]\nend Extraction.RuntimeMainTraceLayout")?;
    Ok(out)
}

/// Additive Mem/WriteByte declarations only. The FOUR-profile renderer above,
/// its output module and its source-rule fragments are deliberately unchanged.
/// The caller first compares both existing artifacts with their frozen bytes.
pub(crate) fn render_mem_write_byte(traces: &str) -> Result<String> {
    let ast = syn::parse_file(traces).context("parsing actual Mem/WriteByte trace declarations")?;
    let mut fragments = Vec::new();
    let profiles = [
        extract_profile(&ast, traces, "memProfile", "MemTraceRow", "MemTrace", &mut fragments)?,
        extract_profile(&ast, traces, "writeByteProfile", "MemAlignWriteByteTraceRow",
            "MemAlignWriteByteTrace", &mut fragments)?,
    ];
    let mut out = String::from("import Extraction.RuntimeMainTraceLayout\n\nnamespace Extraction.RuntimeMemWriteByteTraceLayout\nopen Extraction.RuntimeMainTraceLayout Extraction.RuntimeNativeValuesLayout\n\n");
    for profile in profiles {
        writeln!(out, "def {} : Profile := ⟨{}, {}, {}, {}, {}, {}, [", profile.output_name,
            lean_string(&profile.native_name)?, lean_string(&profile.row_parameter)?,
            profile.constants[0], profile.constants[1], profile.constants[2], profile.packed_bits)?;
        for cell in profile.cells {
            writeln!(out, "  ⟨{}, [{}], {}, {}⟩,", lean_string(&cell.field)?,
                cell.indices.iter().map(usize::to_string).collect::<Vec<_>>().join(", "),
                cell.width, cell.bit_offset)?;
        }
        writeln!(out, "]⟩\n")?;
    }
    writeln!(out, "def sourceFragments : List SourceFragment := [")?;
    for fragment in fragments {
        let bytes = fragment.span.byte_range();
        let location = fragment.span.start();
        writeln!(out, "  ⟨{}, {}, {}, {}, {}, {}, {}, {}⟩,",
            lean_string(&fragment.name)?, lean_string(fragment.source)?,
            bytes.start, bytes.end, location.line, location.column,
            lean_string(source_slice(traces, fragment.span)?)?, render_tokens(fragment.tokens)?)?;
    }
    writeln!(out, "]\nend Extraction.RuntimeMemWriteByteTraceLayout")?;
    Ok(out)
}
