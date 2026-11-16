//! Additive source-only native values! catalogue and actual macro/handoff AST.
//! No PIL-index/native-offset shortcut, Rust compiler/C-ABI equivalence or
//! native-pointer authentication is asserted by this renderer. Expected rule
//! semantics and PIL/native comparisons belong to independent kernel proofs.

use std::collections::BTreeSet;
use std::fmt::Write;
use std::str::FromStr;

use anyhow::{bail, ensure, Context, Result};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;

const TARGETS: &[&str] = &[
    "MainAirValues", "MemAirValues", "BinaryAirValues", "MemAlignByteAirValues",
    "MemAlignReadByteAirValues", "MemAlignWriteByteAirValues",
    "MainAirGroupValues", "MemAirGroupValues", "BinaryAirGroupValues",
    "MemAlignByteAirGroupValues", "MemAlignReadByteAirGroupValues",
    "MemAlignWriteByteAirGroupValues",
];

struct Declaration {
    name: syn::Ident,
    generics: syn::Generics,
    fields: syn::FieldsNamed,
}

impl Parse for Declaration {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        Ok(Self { name: input.parse()?, generics: input.parse()?, fields: input.parse()? })
    }
}

enum Shape {
    F,
    ExtensionF,
    Array { element: Box<Shape>, length: u64, literal: String },
}

struct Fragment {
    name: String,
    source: &'static str,
    span: proc_macro2::Span,
    tokens: proc_macro2::TokenStream,
}

fn source_slice(source: &str, span: proc_macro2::Span) -> Result<&str> {
    source.get(span.byte_range()).context("Rust AST span is outside supplied source")
}

fn bare_f(generics: &syn::Generics) -> Result<()> {
    ensure!(generics.where_clause.is_none() && generics.params.len() == 1,
        "unsupported native declaration generics");
    ensure!(matches!(&generics.params[0], syn::GenericParam::Type(parameter)
        if parameter.ident == "F" && parameter.attrs.is_empty()
        && parameter.bounds.is_empty() && parameter.default.is_none()),
        "native declaration generic is not bare F");
    Ok(())
}

fn shape(ty: &syn::Type, source: &str) -> Result<Shape> {
    match ty {
        syn::Type::Path(path) if path.qself.is_none() && path.path.is_ident("F") => Ok(Shape::F),
        syn::Type::Path(path) if path.qself.is_none() && path.path.leading_colon.is_none()
            && path.path.segments.len() == 1 => {
            let segment = &path.path.segments[0];
            ensure!(segment.ident == "FieldExtension", "unsupported native value type");
            let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments else {
                bail!("FieldExtension must have its actual F argument");
            };
            ensure!(arguments.args.len() == 1 && arguments.colon2_token.is_none(),
                "unsupported FieldExtension argument shape");
            ensure!(matches!(&arguments.args[0], syn::GenericArgument::Type(syn::Type::Path(path))
                if path.qself.is_none() && path.path.is_ident("F")), "FieldExtension argument is not F");
            Ok(Shape::ExtensionF)
        }
        syn::Type::Array(array) => {
            let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(length), .. }) = &array.len else {
                bail!("native array length is not a supported literal");
            };
            let literal = source_slice(source, length.span())?;
            ensure!(length.suffix().is_empty() && literal.bytes().all(|byte| byte.is_ascii_digit()),
                "array length unsupported by actual values! decimal slot parser");
            Ok(Shape::Array {
                element: Box::new(shape(&array.elem, source)?),
                length: length.base10_parse().context("native array length exceeds u64")?,
                literal: literal.to_owned(),
            })
        }
        _ => bail!("unsupported native type at {:?}", ty.span().start()),
    }
}

fn lean_string(value: &str) -> Result<String> {
    let mut out = String::from("\"");
    for character in value.chars() {
        match character {
            '\\' => out.push_str("\\\\"), '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"), '\r' => out.push_str("\\r"), '\t' => out.push_str("\\t"),
            character if character.is_control() => bail!("unsupported source control character"),
            character => out.push(character),
        }
    }
    out.push('"');
    Ok(out)
}

fn render_shape(value: &Shape) -> Result<String> {
    match value {
        Shape::F => Ok(".f".to_owned()),
        Shape::ExtensionF => Ok(".extensionF".to_owned()),
        Shape::Array { element, length, literal } => Ok(format!(
            "(.array {} {length} {})", render_shape(element)?, lean_string(literal)?)),
    }
}

fn render_tokens(tokens: proc_macro2::TokenStream) -> Result<String> {
    let mut out = String::from("[");
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(ident) =>
                write!(out, "(.ident {}),", lean_string(&ident.to_string())?)?,
            proc_macro2::TokenTree::Literal(literal) =>
                write!(out, "(.literal {}),", lean_string(&literal.to_string())?)?,
            proc_macro2::TokenTree::Punct(punct) =>
                write!(out, "(.punct {} {}),", lean_string(&punct.as_char().to_string())?,
                    matches!(punct.spacing(), proc_macro2::Spacing::Joint))?,
            proc_macro2::TokenTree::Group(group) => {
                let delimiter = match group.delimiter() {
                    proc_macro2::Delimiter::Parenthesis => "parenthesis",
                    proc_macro2::Delimiter::Brace => "brace",
                    proc_macro2::Delimiter::Bracket => "bracket",
                    proc_macro2::Delimiter::None => "none",
                };
                write!(out, "(.group {} (Tokens.ofList {})),", lean_string(delimiter)?, render_tokens(group.stream())?)?;
            }
        }
    }
    out.push(']');
    Ok(out)
}

fn fragment(name: &str, source_name: &'static str, source: &str,
    span: proc_macro2::Span) -> Result<Fragment> {
    Ok(Fragment { name: name.to_owned(), source: source_name, span,
        tokens: proc_macro2::TokenStream::from_str(source_slice(source, span)?)
            .map_err(|error| anyhow::anyhow!("lexing actual AST fragment {name}: {error}"))? })
}

fn function<'a>(file: &'a syn::File, name: &str) -> Result<&'a syn::ItemFn> {
    let mut found = None;
    for item in &file.items {
        if let syn::Item::Fn(item) = item {
            if item.sig.ident == name {
                ensure!(found.replace(item).is_none(), "duplicate source function {name}");
            }
        }
    }
    found.with_context(|| format!("missing actual source function {name}"))
}

fn method<'a>(file: &'a syn::File, owner: &str, name: &str) -> Result<&'a syn::ImplItemFn> {
    let mut found = None;
    for item in &file.items {
        let syn::Item::Impl(item) = item else { continue };
        let syn::Type::Path(path) = item.self_ty.as_ref() else { continue };
        if !path.path.segments.last().is_some_and(|segment| segment.ident == owner) { continue }
        for member in &item.items {
            if let syn::ImplItem::Fn(member) = member {
                if member.sig.ident == name {
                    ensure!(found.replace(member).is_none(), "duplicate {owner}::{name}");
                }
            }
        }
    }
    found.with_context(|| format!("missing actual source method {owner}::{name}"))
}

fn binding<'a>(block: &'a syn::Block, name: &str) -> Result<&'a syn::Expr> {
    let mut found = None;
    for statement in &block.stmts {
        let syn::Stmt::Local(local) = statement else { continue };
        let pattern = match &local.pat {
            syn::Pat::Type(typed) => typed.pat.as_ref(),
            pattern => pattern,
        };
        if matches!(pattern, syn::Pat::Ident(pattern) if pattern.ident == name) {
            let expression = local.init.as_ref().context("source binding has no initializer")?.expr.as_ref();
            ensure!(found.replace(expression).is_none(), "duplicate source binding {name}");
        }
    }
    found.with_context(|| format!("missing actual source binding {name}"))
}

fn last_expression(block: &syn::Block) -> Result<&syn::Expr> {
    match block.stmts.last() {
        Some(syn::Stmt::Expr(expression, None)) => Ok(expression),
        _ => bail!("source body does not have supported final expression"),
    }
}

fn unblocked(expression: &syn::Expr) -> Result<&syn::Expr> {
    match expression {
        syn::Expr::Block(block) => last_expression(&block.block),
        _ => Ok(expression),
    }
}

fn call_argument(expression: &syn::Expr) -> Result<(&syn::Path, &syn::Expr)> {
    let syn::Expr::Call(call) = unblocked(expression)? else { bail!("source slot rule is not a call") };
    let syn::Expr::Path(path) = call.func.as_ref() else { bail!("source slot-rule callee is not a path") };
    ensure!(call.args.len() == 1, "source slot-rule call does not have one argument");
    Ok((&path.path, &call.args[0]))
}

struct ScalarRule {
    arm_index: usize,
    tag: String,
    guard_function: String,
    constructor: String,
    width: u64,
    pattern_span: proc_macro2::Span,
    guard_span: proc_macro2::Span,
}

fn scalar_rules(file: &syn::File) -> Result<Vec<ScalarRule>> {
    let function = function(file, "calculate_field_slots")?;
    let syn::Expr::Match(expression) = last_expression(&function.block)? else {
        bail!("actual calculate_field_slots is not the supported match")
    };
    let mut rules = Vec::new();
    for (arm_index, arm) in expression.arms.iter().enumerate() {
        let Some((_, guard)) = &arm.guard else { continue };
        let syn::Expr::Call(guard) = guard.as_ref() else { bail!("unsupported source scalar guard") };
        let syn::Expr::Path(guard_function) = guard.func.as_ref() else { bail!("unsupported scalar guard callee") };
        ensure!(guard.args.len() == 2, "unsupported source scalar guard arity");
        let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Str(tag), .. }) = &guard.args[1] else {
            bail!("source scalar guard has no literal type tag")
        };
        let (constructor, width) = call_argument(&arm.body)?;
        let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(width), .. }) = width else {
            bail!("source scalar width is not a literal")
        };
        rules.push(ScalarRule {
            arm_index, tag: tag.value(),
            guard_function: guard_function.path.segments.iter().map(|segment| segment.ident.to_string())
                .collect::<Vec<_>>().join("::"),
            constructor: constructor.segments.iter().map(|segment| segment.ident.to_string())
                .collect::<Vec<_>>().join("::"),
            width: width.base10_parse().context("source scalar width exceeds u64")?,
            pattern_span: arm.pat.span(), guard_span: guard.span(),
        });
    }
    ensure!(!rules.is_empty(), "no actual source scalar slot rules");
    Ok(rules)
}

fn array_body(file: &syn::File) -> Result<(usize, &syn::Pat, &syn::Block)> {
    let function = function(file, "calculate_field_slots")?;
    let syn::Expr::Match(expression) = last_expression(&function.block)? else {
        bail!("actual calculate_field_slots is not the supported match")
    };
    let mut found = None;
    for (index, arm) in expression.arms.iter().enumerate() {
        if matches!(&arm.pat, syn::Pat::TupleStruct(pattern)
            if pattern.path.segments.last().is_some_and(|segment| segment.ident == "Array")) {
            ensure!(arm.guard.is_none(), "unsupported guarded array slot rule");
            let syn::Expr::Block(block) = arm.body.as_ref() else {
                bail!("actual array slot rule is not a block")
            };
            ensure!(found.replace((index, &arm.pat, &block.block)).is_none(), "duplicate native array slot rule");
        }
    }
    found.context("missing native array slot rule")
}

fn quote_tokens(expression: &syn::Expr) -> Result<proc_macro2::TokenStream> {
    let syn::Expr::Macro(expression) = expression else { bail!("actual macro binding is not quote!") };
    ensure!(expression.mac.path.is_ident("quote"), "actual macro binding does not use quote!");
    Ok(expression.mac.tokens.clone())
}

struct QuotedFunction {
    header_start: proc_macro2::Span,
    header_end: proc_macro2::Span,
    body: proc_macro2::Group,
}

fn quoted_functions(tokens: proc_macro2::TokenStream, name: &str,
    found: &mut Vec<QuotedFunction>) {
    let tokens: Vec<_> = tokens.into_iter().collect();
    for (index, token) in tokens.iter().enumerate() {
        let name_index = index + 1 + usize::from(matches!(tokens.get(index + 1),
            Some(proc_macro2::TokenTree::Punct(punct)) if punct.as_char() == '#'));
        if matches!(token, proc_macro2::TokenTree::Ident(ident) if ident == "fn")
            && matches!(tokens.get(name_index), Some(proc_macro2::TokenTree::Ident(ident)) if ident == name) {
            if let Some((body_index, body)) = tokens.iter().enumerate().skip(name_index + 1)
                .find_map(|(body_index, token)| match token {
                    proc_macro2::TokenTree::Group(group)
                        if group.delimiter() == proc_macro2::Delimiter::Brace =>
                        Some((body_index, group.clone())),
                    _ => None,
                }) {
                let header_start = if index > 0
                    && matches!(&tokens[index - 1], proc_macro2::TokenTree::Ident(ident) if ident == "pub")
                    { index - 1 } else { index };
                found.push(QuotedFunction {
                    header_start: tokens[header_start].span(),
                    header_end: tokens[body_index - 1].span(),
                    body,
                });
            }
        }
        if let proc_macro2::TokenTree::Group(group) = token {
            quoted_functions(group.stream(), name, found);
        }
    }
}

fn quoted_function(tokens: proc_macro2::TokenStream, name: &str) -> Result<QuotedFunction> {
    let mut functions = Vec::new();
    quoted_functions(tokens, name, &mut functions);
    ensure!(functions.len() == 1, "expected exactly one actual quoted function {name}");
    Ok(functions.remove(0))
}

fn quoted_body(tokens: proc_macro2::TokenStream, name: &str) -> Result<proc_macro2::Group> {
    Ok(quoted_function(tokens, name)?.body)
}

fn quoted_signature(tokens: proc_macro2::TokenStream, name: &str) -> Result<proc_macro2::Span> {
    let function = quoted_function(tokens, name)?;
    function.header_start.join(function.header_end)
        .with_context(|| format!("joining actual quoted function {name} signature span"))
}

/// Caller selects actual immutable sources and records their independent hashes.
/// Source profile is b632 declarations + ff0e macro/common source, not 9ca=b632.
/// The normal CLI supplies the locked source snapshots and emits their profiles.
pub(crate) fn render(traces_source: &str, macro_source: &str,
    instance_source: &str, context_source: &str) -> Result<String> {
    let traces = syn::parse_file(traces_source).context("parsing actual native declarations")?;
    let macros = syn::parse_file(macro_source).context("parsing actual values! implementation")?;
    let instances = syn::parse_file(instance_source).context("parsing actual AirInstance implementation")?;
    let contexts = syn::parse_file(context_source).context("parsing actual ProofCtx implementation")?;
    let mut declarations = Vec::new();
    let mut seen = BTreeSet::new();
    let mut extension_alias = None;
    let mut values_index = 0;
    for (item_index, item) in traces.items.iter().enumerate() {
        if let syn::Item::Type(alias) = item {
            if alias.ident == "FieldExtension" {
                ensure!(extension_alias.is_none(), "duplicate FieldExtension alias");
                bare_f(&alias.generics)?;
                ensure!(alias.attrs.iter().all(|attribute|
                    attribute.path().is_ident("doc") || attribute.path().is_ident("allow")),
                    "unsupported native alias attributes");
                extension_alias = Some((item_index, alias, shape(&alias.ty, traces_source)?));
            }
        }
        let syn::Item::Macro(item) = item else { continue };
        if !item.mac.path.is_ident("values") { continue }
        let name = match item.mac.tokens.clone().into_iter().next() {
            Some(proc_macro2::TokenTree::Ident(name)) => name.to_string(),
            _ => bail!("actual values! invocation has no declaration identifier"),
        };
        if TARGETS.contains(&name.as_str()) {
            ensure!(seen.insert(name.clone()), "duplicate native declaration {name}");
            ensure!(item.attrs.iter().all(|attribute| attribute.path().is_ident("doc")), "unsupported values! attributes");
            let declaration: Declaration = syn::parse2(item.mac.tokens.clone())?;
            bare_f(&declaration.generics)?;
            declarations.push((item_index, values_index, item, declaration));
        }
        values_index += 1;
    }
    for target in TARGETS { ensure!(seen.contains(*target), "missing actual native declaration {target}"); }
    let (alias_index, alias, alias_shape) = extension_alias.context("missing FieldExtension alias")?;
    let values = function(&macros, "values_impl")?;
    let mut fragments = Vec::new();
    for name in ["total_size", "field_definitions", "row_struct", "values_struct"] {
        fragments.push(fragment(&format!("values_impl.{name}"), "macros/src/trace.rs", macro_source,
            binding(&values.block, name)?.span())?);
    }
    for name in ["calculate_field_slots", "is_ident"] {
        fragments.push(fragment(name, "macros/src/trace.rs", macro_source, function(&macros, name)?.block.span())?);
    }
    let (array_index, array_pattern, array) = array_body(&macros)?;
    fragments.push(fragment("array_rule.pattern", "macros/src/trace.rs", macro_source, array_pattern.span())?);
    for name in ["len", "elem_slots"] {
        fragments.push(fragment(&format!("array_rule.{name}"), "macros/src/trace.rs", macro_source,
            binding(array, name)?.span())?);
    }
    fragments.push(fragment("array_rule.result", "macros/src/trace.rs", macro_source,
        last_expression(array)?.span())?);
    let quoted_values = quote_tokens(binding(&values.block, "values_struct")?)?;
    for name in ["new", "from_vec_guard", "get_buffer"] {
        let body = quoted_body(quoted_values.clone(), name)?;
        fragments.push(Fragment { name: format!("values_impl.quoted.{name}"), source: "macros/src/trace.rs",
            span: body.span(), tokens: body.stream() });
    }
    for (owner, names) in [
        ("TraceInfo", &["with_air_values", "with_airgroup_values"][..]),
        ("FromTrace", &["with_air_values", "with_airgroup_values"][..]),
        ("AirInstance", &["new", "new_from_trace", "get_airvalues_ptr", "get_airgroup_values_ptr",
            "init_airvalues", "init_airgroup_values"][..]),
    ] {
        for name in names {
            fragments.push(fragment(&format!("{owner}.{name}"), "common/src/air_instance.rs", instance_source,
                method(&instances, owner, name)?.block.span())?);
        }
    }
    fragments.push(fragment("ProofCtx.get_air_instance_params", "common/src/proof_ctx.rs", context_source,
        method(&contexts, "ProofCtx", "get_air_instance_params")?.block.span())?);
    let scalar_rules = scalar_rules(&macros)?;
    for (index, rule) in scalar_rules.iter().enumerate() {
        fragments.push(fragment(&format!("scalar_rule.{index}.pattern"), "macros/src/trace.rs", macro_source,
            rule.pattern_span)?);
        fragments.push(fragment(&format!("scalar_rule.{index}.guard"), "macros/src/trace.rs", macro_source,
            rule.guard_span)?);
    }
    let slot_function = function(&macros, "calculate_field_slots")?;
    let syn::Expr::Match(slot_match) = last_expression(&slot_function.block)? else {
        bail!("actual slot function has unsupported scrutinee")
    };
    fragments.push(fragment("slot_rule.scrutinee", "macros/src/trace.rs", macro_source, slot_match.expr.span())?);
    let mut out = String::from(r#"import Mathlib

/-! Actual source AST and native declaration catalogue, not expected semantics.
Independent kernel consumers must pin macro rules and compare PIL/native shapes.
No Rust compiler/C-ABI/pointer authentication or group FromTrace transfer follows. -/
namespace Extraction.RuntimeNativeValuesLayout

inductive NativeType where
  | f
  | extensionF
  | array (element : NativeType) (length : Nat) (sourceLengthLiteral : String)
  deriving Repr, DecidableEq
mutual
  inductive Token where
    | ident (value : String)
    | literal (value : String)
    | punct (value : String) (joint : Bool)
    | group (delimiter : String) (children : Tokens)
    deriving Repr, DecidableEq
  inductive Tokens where
    | nil
    | cons (head : Token) (tail : Tokens)
    deriving Repr, DecidableEq
end
def Tokens.ofList : List Token → Tokens
  | [] => .nil
  | head :: tail => .cons head (Tokens.ofList tail)
def Tokens.toList : Tokens → List Token
  | .nil => []
  | .cons head tail => head :: Tokens.toList tail
structure Field where
  ordinal : Nat
  name : String
  nativeType : NativeType
  isPublic : Bool
  startByte : Nat
  endByte : Nat
  line : Nat
  column : Nat
  typeSource : String
  declarationSource : String
  deriving Repr, DecidableEq
structure Declaration where
  sourceItemIndex : Nat
  sourceValuesIndex : Nat
  name : String
  startByte : Nat
  endByte : Nat
  line : Nat
  column : Nat
  declarationSource : String
  fields : List Field
  deriving Repr, DecidableEq
structure SourceFragment where
  name : String
  sourceFile : String
  startByte : Nat
  endByte : Nat
  line : Nat
  column : Nat
  sourceText : String
  tokens : List Token
  deriving Repr, DecidableEq
structure ScalarRule where
  sourceArmIndex : Nat
  typeTag : String
  guardFunction : String
  resultConstructor : String
  width : Nat
  deriving Repr, DecidableEq

"#);
    writeln!(out, "def slotArmCount : Nat := {}", slot_match.arms.len())?;
    writeln!(out, "def arrayArmIndex : Nat := {array_index}")?;
    writeln!(out, "def extensionAliasItemIndex : Nat := {alias_index}")?;
    writeln!(out, "def extensionAlias : NativeType := {}", render_shape(&alias_shape)?)?;
    writeln!(out, "def extensionAliasSource : String := {}", lean_string(source_slice(traces_source, alias.span())?)?)?;
    writeln!(out, "\ndef declarations : List Declaration := [")?;
    for (item_index, values_index, item, declaration) in declarations {
        let span = item.span(); let bytes = span.byte_range(); let location = span.start();
        writeln!(out, "  ⟨{item_index}, {values_index}, {}, {}, {}, {}, {}, {}, [",
            lean_string(&declaration.name.to_string())?, bytes.start, bytes.end, location.line, location.column,
            lean_string(source_slice(traces_source, span)?)?)?;
        for (ordinal, field) in declaration.fields.named.iter().enumerate() {
            ensure!(field.attrs.iter().all(|attribute| attribute.path().is_ident("doc")), "unsupported native field attributes");
            let name = field.ident.as_ref().context("unnamed native field")?;
            let span = field.span(); let bytes = span.byte_range(); let location = span.start();
            writeln!(out, "    ⟨{ordinal}, {}, {}, {}, {}, {}, {}, {}, {}, {}⟩,",
                lean_string(&name.to_string())?, render_shape(&shape(&field.ty, traces_source)?)?,
                matches!(field.vis, syn::Visibility::Public(_)), bytes.start, bytes.end, location.line, location.column,
                lean_string(source_slice(traces_source, field.ty.span())?)?, lean_string(source_slice(traces_source, span)?)?)?;
        }
        writeln!(out, "  ]⟩,")?;
    }
    writeln!(out, "]\n\ndef scalarRules : List ScalarRule := [")?;
    for rule in scalar_rules {
        writeln!(out, "  ⟨{}, {}, {}, {}, {}⟩,", rule.arm_index, lean_string(&rule.tag)?,
            lean_string(&rule.guard_function)?, lean_string(&rule.constructor)?, rule.width)?;
    }
    writeln!(out, "]\n\ndef sourceFragments : List SourceFragment := [")?;
    for fragment in fragments {
        let source = match fragment.source {
            "macros/src/trace.rs" => macro_source,
            "common/src/air_instance.rs" => instance_source,
            "common/src/proof_ctx.rs" => context_source,
            _ => bail!("unknown source fragment owner"),
        };
        let bytes = fragment.span.byte_range(); let location = fragment.span.start();
        writeln!(out, "  ⟨{}, {}, {}, {}, {}, {}, {}, {}⟩,", lean_string(&fragment.name)?, lean_string(fragment.source)?,
            bytes.start, bytes.end, location.line, location.column, lean_string(source_slice(source, fragment.span)?)?,
            render_tokens(fragment.tokens)?)?;
    }
    writeln!(out, "]\nend Extraction.RuntimeNativeValuesLayout")?;
    Ok(out)
}

// Native trace profiles reuse the same parser and source-token representation.
#[path = "runtime_main_trace_layout.rs"]
pub(crate) mod main_trace;
