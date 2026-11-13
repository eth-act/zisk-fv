//! Producing extraction for the actual source runtime helpers.
//!
//! The row builders are NOT reimplemented here. Their complete bodies are
//! taken from the supplied source and continue to call zisk-core's real
//! ZiskInstBuilder methods. Only the instruction-map sink is projected to an
//! ordered emission history. Source insertion sites and wrapper-owned origins
//! are recorded at the sink, never supplied by the eventual theorem caller.
//!
//! The resulting Rust is an Aeneas INPUT, not a claim that Aeneas extraction or
//! the loader/physical-execution correspondence has already been proved.
use std::fmt::Write as _;
use anyhow::{anyhow, bail, Result};
use regex::Regex;

pub(crate) struct RuntimeSourceOutput {
    pub(crate) rust: String,
    pub(crate) lean: String,
}

/// Mask comments and quoted contents without changing byte offsets. Nested
/// comments and escaped quotes matter: builder logging contains Rust braces.
fn mask_with_strings(source: &str, hide_strings: bool) -> Result<String> {
    let bytes = source.as_bytes();
    let mut out = bytes.to_vec();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i..].starts_with(b"//") {
            let start = i;
            while i < bytes.len() && bytes[i] != b'\n' { i += 1; }
            out[start..i].fill(b' ');
        } else if bytes[i..].starts_with(b"/*") {
            let start = i;
            i += 2;
            let mut depth = 1;
            while depth > 0 {
                if i >= bytes.len() { bail!("unterminated Rust comment"); }
                if bytes[i..].starts_with(b"/*") { depth += 1; i += 2; }
                else if bytes[i..].starts_with(b"*/") { depth -= 1; i += 2; }
                else { i += 1; }
            }
            for c in &mut out[start..i] { if *c != b'\n' { *c = b' '; } }
        } else if bytes[i] == b'"' {
            let start = i;
            i += 1;
            loop {
                if i >= bytes.len() { bail!("unterminated Rust string"); }
                if bytes[i] == b'\\' { i += 2; }
                else if bytes[i] == b'"' { i += 1; break; }
                else { i += 1; }
            }
            if hide_strings {
                for c in &mut out[start..i] { if *c != b'\n' { *c = b' '; } }
            }
        } else { i += 1; }
    }
    Ok(String::from_utf8(out)?)
}

fn mask(source: &str) -> Result<String> { mask_with_strings(source,true) }

fn close(code: &str, start: usize, left: u8, right: u8) -> Result<usize> {
    let mut depth = 0;
    for (offset,c) in code.as_bytes()[start..].iter().copied().enumerate() {
        if c == left { depth += 1; }
        if c == right {
            depth -= 1;
            if depth == 0 { return Ok(start + offset); }
        }
    }
    bail!("unclosed source delimiter at byte {start}")
}

fn function<'a>(source: &'a str, code: &str, name: &str) -> Result<(&'a str, usize)> {
    let pattern = Regex::new(&format!(r"\bpub\s+(?:const\s+)?fn\s+{}\s*\(",regex::escape(name)))?;
    let matches = pattern.find_iter(code).collect::<Vec<_>>();
    if matches.len() != 1 { bail!("expected one source function {name}"); }
    let start = matches[0].start();
    let open = code[matches[0].end()..].find('{').ok_or_else(|| anyhow!("missing {name} body"))? + matches[0].end();
    let end = close(code,open,b'{',b'}')?;
    Ok((&source[start..=end],start))
}

struct Helper {
    name: &'static str,
    source: String,
    projected: String,
    insert_lines: Vec<usize>,
}

struct BuilderCall { method: String, arguments: Vec<String> }
struct RowSource { helper: String, site: usize, calls: Vec<BuilderCall>, insertion: Vec<String> }

fn arguments(source: &str, code: &str, open: usize) -> Result<Vec<String>> {
    let end = close(code,open,b'(',b')')?;
    let mut result = Vec::new();
    let mut start = open + 1;
    let mut depth = 0;
    for i in open+1..end {
        match code.as_bytes()[i] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b',' if depth == 0 => {
                result.push(tokens(source[start..i].trim())?.join(" "));
                start = i + 1;
            },
            _ => (),
        }
    }
    if !source[start..end].trim().is_empty() {
        result.push(tokens(source[start..end].trim())?.join(" "));
    }
    Ok(result)
}

fn row_sources(helper: &Helper) -> Result<Vec<RowSource>> {
    let source = &helper.source;
    let code = mask(source)?;
    let new = Regex::new(r"\bZiskInstBuilder\s*::\s*new\s*\(")?;
    let method = Regex::new(r"\bzib\s*\.\s*([A-Za-z_][A-Za-z_0-9]*)\s*\(")?;
    let insert = Regex::new(r"\brom\s*\.\s*insts\s*\.\s*insert\s*\(")?;
    let starts = new.find_iter(&code).collect::<Vec<_>>();
    let inserts = insert.find_iter(&code).collect::<Vec<_>>();
    if starts.len() != inserts.len() { bail!("source row construction/insertion mismatch in {}",helper.name); }
    let mut rows = Vec::new();
    for (site,(start,end)) in starts.iter().zip(&inserts).enumerate() {
        if start.end() >= end.start() || (site+1 < starts.len() && starts[site+1].start() < end.end()) {
            bail!("interleaved source row builders in {}",helper.name);
        }
        let mut calls = vec![BuilderCall { method: "new".into(), arguments: arguments(source,&code,start.end()-1)? }];
        for capture in method.captures_iter(&code[start.end()..end.start()]) {
            let call = capture.get(0).unwrap();
            calls.push(BuilderCall {
                method: capture[1].into(),
                arguments: arguments(source,&code,start.end()+call.end()-1)?,
            });
        }
        rows.push(RowSource {
            helper: helper.name.into(), site, calls,
            insertion: arguments(source,&code,end.end()-1)?,
        });
    }
    Ok(rows)
}

struct OpcodeSource { name: String, constructor: String, family: String, code: u64, input: u64, output: u64 }
fn opcode_sources(source: &str) -> Result<Vec<OpcodeSource>> {
    let code = mask(source)?;
    let invocation = Regex::new(r"\bdefine_ops\s*!\s*\{")?;
    let invocations = invocation.find_iter(&code).collect::<Vec<_>>();
    if invocations.len() != 1 { bail!("expected one actual define_ops invocation"); }
    let start = invocations[0].end();
    let end = close(&code,start-1,b'{',b'}')?;
    let entries = mask_with_strings(&source[start..end],false)?;
    let entry = Regex::new(r#"\(\s*([A-Za-z_][A-Za-z_0-9]*)\s*,\s*"([^"]+)"\s*,\s*([A-Za-z_][A-Za-z_0-9]*)\s*,\s*[^,]+\s*,\s*(0x[0-9a-fA-F]+|[0-9]+)\s*,\s*([0-9]+)\s*,\s*([0-9]+)\s*,"#)?;
    let mut result = Vec::new();
    for c in entry.captures_iter(&entries) {
        let code = if let Some(hex) = c[4].strip_prefix("0x") { u64::from_str_radix(hex,16)? } else { c[4].parse()? };
        result.push(OpcodeSource { name: c[2].into(), constructor: c[1].into(), family: c[3].into(),
            code, input: c[5].parse()?, output: c[6].parse()? });
    }
    if result.is_empty() { bail!("no actual opcode macro entries"); }
    Ok(result)
}

fn pubout_result(source: &str) -> Result<(usize,bool)> {
    let code = mask(source)?;
    let (operation,_) = function(source,&code,"op_pubout")?;
    let operation_code = mask(operation)?;
    let args_open = operation_code.find('(').ok_or_else(||anyhow!("missing pubout arguments"))?;
    let names = arguments(operation,&operation_code,args_open)?.into_iter()
        .map(|argument| argument.split_whitespace().next().map(str::to_owned)
            .ok_or_else(||anyhow!("missing PUBOUT argument name"))).collect::<Result<Vec<_>>>()?;
    let open = operation_code.find('{').ok_or_else(||anyhow!("missing pubout body"))?;
    let end = close(&operation_code,open,b'{',b'}')?;
    let body = tokens(&operation_code[open+1..end])?;
    if body.len() != 5 || body[0] != "(" || body[2] != "," || body[4] != ")" {
        bail!("PUBOUT operation is not a source argument/flag tuple");
    }
    let argument = names.iter().position(|name| name == &body[1])
        .ok_or_else(||anyhow!("PUBOUT result is not a source argument"))?;
    let flag = match body[3].as_str() { "false" => false, "true" => true,
        _ => bail!("PUBOUT flag is not a source Boolean literal") };
    Ok((argument,flag))
}

fn project_helper(source: &str, code: &str, name: &'static str) -> Result<Helper> {
    let (original,start) = function(source,code,name)?;
    let local = mask(original)?;
    let mut edits: Vec<(usize,usize,String)> = Vec::new();
    let header = Regex::new(r"\bZiskRom\b")?;
    let open = local.find('{').ok_or_else(|| anyhow!("missing helper body"))?;
    let types = header.find_iter(&local[..open]).collect::<Vec<_>>();
    if types.len()!=1 { bail!("{name} ROM carrier is not the source ZiskRom"); }
    edits.push((types[0].start(),types[0].end(),"RuntimeRom".into()));
    let public = local.find("pub ").ok_or_else(|| anyhow!("helper is not public"))?;
    edits.push((public,public+4,String::new()));
    // Preserve builder calls, logging-argument evaluation, checked arithmetic,
    // assertions, panic guards and panic formatting. Unsupported extraction
    // dependencies must remain visible; erasing them is not source closure.
    let insert=Regex::new(r"\brom\s*\.\s*insts\s*\.\s*insert\s*\(")?;
    let mut insert_lines=Vec::new();
    for (site,call) in insert.find_iter(&local).enumerate() {
        insert_lines.push(source[..start+call.start()].bytes().filter(|c| *c==b'\n').count()+1);
        edits.push((call.end(),call.end(),format!("{site}, ")));
    }
    if insert_lines.is_empty() { bail!("source helper {name} has no instruction insertion"); }
    edits.sort_by_key(|edit| edit.0);
    let mut previous=0;
    let mut projected=String::new();
    for (a,b,replacement) in edits {
        if a < previous { bail!("overlapping runtime source projections"); }
        projected.push_str(&original[previous..a]);
        projected.push_str(&replacement);
        previous=b;
    }
    projected.push_str(&original[previous..]);
    Ok(Helper { name, source: original.into(), projected, insert_lines })
}

#[derive(Clone,PartialEq,Eq)]
enum Scope { Payloads, Executable, ReadWrite, MergedReadOnly, PayloadIndex(usize) }
impl Scope {
    fn lean(&self) -> String {
        match self {
            Self::Payloads => ".payloads".into(), Self::Executable => ".executableSections".into(),
            Self::ReadWrite => ".readWriteSections".into(), Self::MergedReadOnly => ".mergedReadOnlySections".into(),
            Self::PayloadIndex(i) => format!("(.payloadIndex {i})"),
        }
    }
}
fn tokens(source: &str) -> Result<Vec<String>> {
    Ok(Regex::new(r#""(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]"#)?.find_iter(source).map(|m|m.as_str().into()).collect())
}
fn scope(header: &str) -> Result<Scope> {
    let t=tokens(header)?;
    let joined=t.join(" ");
    Ok(match joined.as_str() {
        "for ( i , payload ) in payloads . into_iter ( ) . enumerate ( )" => Scope::Payloads,
        "for section in & payload . exec" => Scope::Executable,
        "for section in & payload . rw" => Scope::ReadWrite,
        "for section in & merged_ro" => Scope::MergedReadOnly,
        _ if t.len()==5 && t[0]=="if" && t[1]=="i" && t[2]=="=" && t[3]=="=" => Scope::PayloadIndex(t[4].parse()?),
        _ => bail!("unrecognized loader control scope: {joined}"),
    })
}
struct ImageCall { scopes: Vec<Scope>, name: String, arguments: String, line: usize }

fn image_calls(source: &str) -> Result<Vec<ImageCall>> {
    let code=mask(source)?;
    let (body,start)=function(source,&code,"elf2rom")?;
    let local=mask(body)?;
    let open=local.find('{').ok_or_else(|| anyhow!("missing loader body"))?;
    let call=Regex::new(r"\b(add_end_and_lib|add_zisk_code|add_zisk_init_data|merge_adjacent_ro_sections|add_entry_exit_jmp|optimize_instruction_lookup|RoData\s*::\s*new)\s*\(")?;
    let mut result=Vec::new();
    for matched in call.captures_iter(&local) {
        let location=matched.get(0).unwrap();
        let mut scopes=Vec::new();
        let mut cursor=open+1;
        // Read actual nested blocks enclosing this call, in execution order.
        while cursor < location.start() {
            let suffix=&local[cursor..location.start()];
            let Some(relative)=suffix.find(['{',';','}']) else { break; };
            let delimiter=cursor+relative;
            match local.as_bytes()[delimiter] {
                b'{' => {
                    let end=close(&local,delimiter,b'{',b'}')?;
                    if end >= location.end() {
                        scopes.push(scope(local[cursor..delimiter].trim())?);
                        cursor=delimiter+1;
                    } else { cursor=end+1; }
                },
                _ => cursor=delimiter+1,
            }
        }
        let end=close(&local,location.end()-1,b'(',b')')?;
        result.push(ImageCall {
            scopes,
            name:matched[1].split_whitespace().collect::<String>(),
            arguments:tokens(&local[location.end()..end])?.join(" "),
            line:source[..start+location.start()].bytes().filter(|c|*c==b'\n').count()+1,
        });
    }
    if result.is_empty() { bail!("no actual source loader construction calls"); }
    Ok(result)
}

fn quoted(value: &str) -> String { format!("{:?}",value) }

fn private_constants(source: &str, code: &str, helpers: &[Helper]) -> Result<Vec<String>> {
    let constant = Regex::new(r"(?m)^const\s+([A-Z][A-Z0-9_]*)\s*:")?;
    let mut declarations = Vec::new();
    for capture in constant.captures_iter(code) {
        let start = capture.get(0).unwrap().start();
        let equals = code[capture.get(0).unwrap().end()..].find('=')
            .ok_or_else(|| anyhow!("missing source constant initializer"))?
            + capture.get(0).unwrap().end();
        let end = code[equals..].find(';')
            .ok_or_else(|| anyhow!("missing source constant terminator"))? + equals + 1;
        declarations.push((capture[1].to_owned(), source[start..end].to_owned()));
    }
    let mut selected = vec![false; declarations.len()];
    loop {
        let mut changed = false;
        for (i,(name,_)) in declarations.iter().enumerate() {
            if selected[i] { continue; }
            let identifier = Regex::new(&format!(r"\b{}\b",regex::escape(name)))?;
            if helpers.iter().any(|h| identifier.is_match(&h.projected))
                || declarations.iter().enumerate().any(|(j,(_,text))|
                    selected[j] && identifier.is_match(text)) {
                selected[i] = true;
                changed = true;
            }
        }
        if !changed { break; }
    }
    Ok(declarations.into_iter().zip(selected).filter_map(|((_,text),used)|
        used.then_some(text)).collect())
}

pub(crate) fn render(context_source: &str, elf2rom_source: &str,
    builder_source: &str, operations_source: &str) -> Result<RuntimeSourceOutput> {
    let code=mask(context_source)?;
    let helpers=["add_end_and_lib","add_zisk_init_data","add_entry_exit_jmp"].into_iter()
        .map(|name| project_helper(context_source,&code,name)).collect::<Result<Vec<_>>>()?;
    let calls=image_calls(elf2rom_source)?;
    let constants = private_constants(context_source, &code, &helpers)?;
    let rows = helpers.iter().map(row_sources).collect::<Result<Vec<_>>>()?
        .into_iter().flatten().collect::<Vec<_>>();
    let opcodes = opcode_sources(operations_source)?;
    let (pubout_argument,pubout_flag) = pubout_result(operations_source)?;
    let builder_code = mask(builder_source)?;
    let builder_methods = ["src_a","src_b","store","store_pc","op","src_a_reg",
        "src_b_reg","src_b_lastc","src_b_ind","store_reg","store_pc_reg","store_ind","op_zisk","end"]
        .into_iter().map(|name| Ok((name,function(builder_source,&builder_code,name)?.0)))
        .collect::<Result<Vec<_>>>()?;
    let mut rust=String::from("// Generated from actual source helper bodies. Compile with aeneas_extract.\nuse zisk_core::*;\n\n#[derive(Clone, Copy)]\npub enum RuntimeOrigin { EndAndLib, ReadWriteInitialization, ReadOnlyInitialization, EntryExit }\npub struct RuntimeEmission { pub origin: RuntimeOrigin, pub site: usize, pub ordinal: usize, pub address: u64, pub instruction: ZiskInst }\npub struct RuntimeRows { pub next: u64, pub emissions: Vec<RuntimeEmission> }\nstruct RuntimeSink { origin: RuntimeOrigin, emissions: Vec<RuntimeEmission> }\nimpl RuntimeSink {\n fn insert(&mut self, site: usize, address: u64, builder: ZiskInstBuilder) {\n  let ordinal = self.emissions.len();\n  self.emissions.push(RuntimeEmission { origin: self.origin, site, ordinal, address, instruction: builder.i });\n }\n}\nstruct RuntimeRom { next_init_inst_addr: u64, insts: RuntimeSink }\nimpl RuntimeRom {\n fn new(next: u64, origin: RuntimeOrigin) -> Self { Self { next_init_inst_addr: next, insts: RuntimeSink { origin, emissions: Vec::new() } } }\n fn finish(self) -> RuntimeRows { RuntimeRows { next: self.next_init_inst_addr, emissions: self.insts.emissions } }\n}\n\n");
    for constant in &constants { rust.push_str(constant); rust.push('\n'); }
    for helper in &helpers { rust.push_str(&helper.projected); rust.push_str("\n\n"); }
    rust.push_str("pub fn extract_runtime_end_and_lib() -> RuntimeRows {\n let mut rom = RuntimeRom::new(ROM_ENTRY, RuntimeOrigin::EndAndLib);\n add_end_and_lib(&mut rom); rom.finish()\n}\npub fn extract_runtime_read_write(start: u64, addr: u64, data: &[u8]) -> RuntimeRows {\n let mut rom = RuntimeRom::new(start, RuntimeOrigin::ReadWriteInitialization);\n add_zisk_init_data(&mut rom, addr, data, true); rom.finish()\n}\npub fn extract_runtime_read_only(start: u64, addr: u64, data: &[u8]) -> RuntimeRows {\n let mut rom = RuntimeRom::new(start, RuntimeOrigin::ReadOnlyInitialization);\n add_zisk_init_data(&mut rom, addr, data, true); rom.finish()\n}\npub fn extract_runtime_entry_exit(start: u64, entry: u64) -> RuntimeRows {\n let mut rom = RuntimeRom::new(start, RuntimeOrigin::EntryExit);\n add_entry_exit_jmp(&mut rom, entry); rom.finish()\n}\n");
    let mut lean=String::from("import Mathlib\n\nnamespace Extraction.RuntimeSource\n\ninductive Scope where\n | payloads | executableSections | readWriteSections | mergedReadOnlySections\n | payloadIndex : Nat → Scope\n deriving DecidableEq, Repr\nstructure ImageCall where\n scopes : List Scope\n name : String\n arguments : String\n sourceLine : Nat\n deriving DecidableEq, Repr\n\ndef imageCalls : List ImageCall := [\n");
    for c in &calls {
        writeln!(lean," ⟨[{}], {}, {}, {}⟩,",c.scopes.iter().map(Scope::lean).collect::<Vec<_>>().join(", "),quoted(&c.name),quoted(&c.arguments),c.line).unwrap();
    }
    lean.push_str("]\n\nstructure HelperSource where\n name : String\n source : String\n insertionLines : List Nat\n deriving DecidableEq, Repr\n\ndef helpers : List HelperSource := [\n");
    for h in &helpers {
        writeln!(lean," ⟨{}, {}, [{}]⟩,",quoted(h.name),quoted(&h.source),h.insert_lines.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")).unwrap();
    }
    lean.push_str("]\n\ndef privateConstants : List String := [\n");
    for constant in &constants { writeln!(lean," {},",quoted(constant)).unwrap(); }
    lean.push_str("]\n\nstructure BuilderCall where\n method : String\n arguments : List String\n deriving DecidableEq, Repr\nstructure RowSource where\n helper : String\n site : Nat\n calls : List BuilderCall\n insertion : List String\n deriving DecidableEq, Repr\n\ndef rowSources : List RowSource := [\n");
    for row in &rows {
        let calls = row.calls.iter().map(|c| format!("⟨{}, [{}]⟩",quoted(&c.method),
            c.arguments.iter().map(|a|quoted(a)).collect::<Vec<_>>().join(", "))).collect::<Vec<_>>().join(", ");
        writeln!(lean," ⟨{}, {}, [{}], [{}]⟩,",quoted(&row.helper),row.site,calls,
            row.insertion.iter().map(|a|quoted(a)).collect::<Vec<_>>().join(", ")).unwrap();
    }
    lean.push_str("]\n\nstructure OpcodeSource where\n name : String\n constructor : String\n family : String\n code : Nat\n inputSize : Nat\n outputSize : Nat\n deriving DecidableEq, Repr\n\ndef opcodes : List OpcodeSource := [\n");
    for op in &opcodes {
        writeln!(lean," ⟨{}, {}, {}, {}, {}, {}⟩,",quoted(&op.name),quoted(&op.constructor),
            quoted(&op.family),op.code,op.input,op.output).unwrap();
    }
    lean.push_str("]\n\ndef builderMethods : List (String × String) := [\n");
    for (name,body) in &builder_methods { writeln!(lean," ({}, {}),",quoted(name),quoted(body)).unwrap(); }
    writeln!(lean,"]\n\ndef puboutResultArgument : Nat := {pubout_argument}\ndef puboutResultFlag : Bool := {pubout_flag}\n\nend Extraction.RuntimeSource").unwrap();
    Ok(RuntimeSourceOutput {rust,lean})
}
