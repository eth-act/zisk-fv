//! Untrusted observations from actual pinned public producers, not a ROM model.
//! The image and trace come from independent calls; their correlation, source
//! provenance, execution, termination and acceptance are not proved here.
use fields::{Goldilocks, PrimeField64};
use serde::ser::{SerializeSeq, SerializeStruct, SerializeTuple};
use serde::{Serialize, Serializer};
use sm_rom::RomSM;
use std::error::Error;
use std::fmt::{self, Debug, Display};
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::Path;
use zisk_core::{zisk_ops::ZiskOp, Riscv2zisk, ZiskInst, ZiskRom, ROM_ENTRY, ROM_EXIT};
use zisk_pil::{RomRomTrace, RomRomTraceRow};

type Result<T, E = Box<dyn Error>> = std::result::Result<T, E>;

struct Decimal<T>(T);
impl<T: Display> Serialize for Decimal<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        serializer.collect_str(&self.0)
    }
}
struct DebugLabel<'a, T>(&'a T);
impl<T: Debug> Display for DebugLabel<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(self.0, f)
    }
}

struct Instruction<'a>(&'a ZiskInst);
impl Serialize for Instruction<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        // Exhaustive destructuring: no normal-profile source field is silently erased.
        let ZiskInst {
            paddr, store_pc, store_use_sp, store, store_offset, set_pc, is_precompiled,
            ind_width, end, a_src, a_use_sp_imm1, a_offset_imm0, b_src, b_use_sp_imm1,
            b_offset_imm0, jmp_offset1, jmp_offset2, is_external_op, op, func, op_str,
            op_type, verbose, m32, input_size, sorted_pc_list_index, riscv_inst,
        } = self.0;
        let mut s = serializer.serialize_struct("ActualZiskInst", 29)?;
        s.serialize_field("paddr", &Decimal(paddr))?;
        s.serialize_field("store_pc", store_pc)?;
        s.serialize_field("store_use_sp", store_use_sp)?;
        s.serialize_field("store", &Decimal(store))?;
        s.serialize_field("store_offset", &Decimal(store_offset))?;
        s.serialize_field("set_pc", set_pc)?;
        s.serialize_field("is_precompiled", is_precompiled)?;
        s.serialize_field("ind_width", &Decimal(ind_width))?;
        s.serialize_field("end", end)?;
        s.serialize_field("a_src", &Decimal(a_src))?;
        s.serialize_field("a_use_sp_imm1", &Decimal(a_use_sp_imm1))?;
        s.serialize_field("a_offset_imm0", &Decimal(a_offset_imm0))?;
        s.serialize_field("b_src", &Decimal(b_src))?;
        s.serialize_field("b_use_sp_imm1", &Decimal(b_use_sp_imm1))?;
        s.serialize_field("b_offset_imm0", &Decimal(b_offset_imm0))?;
        s.serialize_field("jmp_offset1", &Decimal(jmp_offset1))?;
        s.serialize_field("jmp_offset2", &Decimal(jmp_offset2))?;
        s.serialize_field("is_external_op", is_external_op)?;
        s.serialize_field("op", &Decimal(op))?;
        s.serialize_field("op_type_id", &Decimal(op_type.clone() as u32))?;
        s.serialize_field("m32", m32)?;
        s.serialize_field("input_size", &Decimal(input_size))?;
        s.serialize_field("sorted_pc_list_index", &Decimal(sorted_pc_list_index))?;
        // The address is diagnostic native data, NOT an interpretation of a function pointer.
        s.serialize_field("func_native_address", &Decimal(*func as usize))?;
        s.serialize_field("op_str", op_str)?;
        s.serialize_field("verbose", verbose)?;
        s.serialize_field("riscv_inst", riscv_inst)?;
        s.serialize_field("op_type_debug", &Decimal(DebugLabel(op_type)))?;
        s.serialize_field("actual_get_flags", &Decimal(self.0.get_flags()))?;
        s.end()
    }
}

#[derive(Serialize)]
struct ImageEntry<'a> {
    ordinal: Decimal<usize>,
    map_key: Decimal<u64>,
    instruction: Instruction<'a>,
}

struct Row<'a>(&'a [u64; 11]);
impl Serialize for Row<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        let mut row = serializer.serialize_tuple(11)?;
        for value in self.0 {
            row.serialize_element(&Decimal(value))?;
        }
        row.end()
    }
}

// Serialize the ACTUAL returned trace fields. Never reconstruct these from ZiskInst.
fn trace_fields(row: &RomRomTraceRow<Goldilocks>) -> [u64; 11] {
    [
        row.line.as_canonical_u64(), row.a_offset_imm0.as_canonical_u64(),
        row.a_imm1.as_canonical_u64(), row.b_offset_imm0.as_canonical_u64(),
        row.b_imm1.as_canonical_u64(), row.ind_width.as_canonical_u64(),
        row.op.as_canonical_u64(), row.store_offset.as_canonical_u64(),
        row.jmp_offset1.as_canonical_u64(), row.jmp_offset2.as_canonical_u64(),
        row.flags.as_canonical_u64(),
    ]
}

fn output(path: &Path, name: &str) -> Result<BufWriter<File>> {
    Ok(BufWriter::new(File::create(path.join(name))?))
}
fn json_line<T: Serialize>(writer: &mut BufWriter<File>, value: &T) -> Result<()> {
    serde_json::to_writer(&mut *writer, value)?;
    writer.write_all(b"\n")?;
    Ok(())
}

#[derive(Serialize)]
struct TailDeviation<'a> {
    row: Decimal<usize>,
    values: Row<'a>,
}

#[derive(Serialize)]
struct Site<'a> {
    offset: Decimal<u64>,
    candidate_key: Option<Decimal<u64>>,
    map_ordinal: Option<Decimal<usize>>,
    instruction: Option<Instruction<'a>>,
}
struct Sites<'a> {
    rom: &'a ZiskRom,
    candidate: Option<u64>,
    ordinals: &'a [Option<usize>; 16],
}
impl Serialize for Sites<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        let mut sites = serializer.serialize_seq(Some(16))?;
        for index in 0..16 {
            let offset = index as u64 * 4;
            let key = self.candidate.and_then(|h| h.checked_add(offset));
            let inst = key.and_then(|k| self.rom.insts.get(&k));
            sites.serialize_element(&Site {
                offset: Decimal(offset), candidate_key: key.map(Decimal),
                map_ordinal: self.ordinals[index].map(Decimal),
                instruction: inst.map(|i| Instruction(&i.i)),
            })?;
        }
        sites.end()
    }
}

struct HexBytes<'a>(&'a [u8]);
impl Display for HexBytes<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}
#[derive(Serialize)]
struct RoSection<'a> {
    from: Decimal<u64>,
    length: Decimal<usize>,
    data_hex: Decimal<HexBytes<'a>>,
}
struct RoData<'a>(&'a [zisk_core::RoData]);
impl Serialize for RoData<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        let mut sections = serializer.serialize_seq(Some(self.0.len()))?;
        for section in self.0 {
            sections.serialize_element(&RoSection {
                from: Decimal(section.from), length: Decimal(section.length),
                data_hex: Decimal(HexBytes(&section.data)),
            })?;
        }
        sections.end()
    }
}
struct PcList<'a>(&'a [u64]);
impl Serialize for PcList<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error> {
        let mut pcs = serializer.serialize_seq(Some(self.0.len()))?;
        for pc in self.0 {
            pcs.serialize_element(&Decimal(pc))?;
        }
        pcs.end()
    }
}

#[derive(Serialize)]
struct Observations<'a> {
    status: &'static str,
    image_and_trace_are_independent_actual_calls: bool,
    map_entries: Decimal<usize>,
    physical_rows: Decimal<usize>,
    columns: [&'static str; 11],
    field_modulus: &'static str,
    rows_scanned: Decimal<usize>,
    cells_scanned: Decimal<usize>,
    canonical_trace_byte_length: Decimal<usize>,
    tail_start: Decimal<usize>,
    tail_count: Decimal<usize>,
    nonzero_tail_entries: Decimal<usize>,
    static_pubout_sites: Decimal<usize>,
    next_init_inst_addr_final: Decimal<u64>,
    header_subtrahend: Decimal<u64>,
    header_subtraction_underflow: bool,
    header_candidate_only: Option<Decimal<u64>>,
    intended_header_sites_observed: Sites<'a>,
    rom_entry_constant: Decimal<u64>,
    rom_entry_lookup: Option<Instruction<'a>>,
    rom_exit_constant: Decimal<u64>,
    rom_exit_lookup: Option<Instruction<'a>>,
    min_program_pc: Decimal<u64>,
    max_program_pc: Decimal<u64>,
    max_bios_pc: Decimal<u64>,
    offset_rom_na_unstructions: Decimal<u64>,
    entry_lookup_cache_length: Decimal<usize>,
    program_lookup_cache_length: Decimal<usize>,
    nonaligned_lookup_cache_length: Decimal<usize>,
    sorted_pc_list: PcList<'a>,
    ro_data: RoData<'a>,
}

fn main() -> Result<()> {
    let mut args = std::env::args_os().skip(1);
    let elf_path = args.next().ok_or("missing ELF path")?;
    let output_path = args.next().ok_or("missing output directory")?;
    if args.next().is_some() {
        return Err("usage: finite-return-rom ELF OUTPUT_DIRECTORY".into());
    }
    let elf = fs::read(elf_path)?;
    let out = Path::new(&output_path);
    fs::create_dir_all(out)?;
    // Both calls execute upstream code. No private-function access or replacement serializer.
    let rom = Riscv2zisk::new(&elf).run()?;
    let mut trace = RomRomTrace::<Goldilocks>::new_zeroes();
    RomSM::compute_custom_trace_rom(&elf, &mut trace);
    let count = rom.insts.len();
    let total = trace.buffer.len();
    if count > total || total != RomRomTrace::<Goldilocks>::NUM_ROWS {
        return Err("actual image and physical trace dimensions do not fit".into());
    }
    let candidate = rom.next_init_inst_addr.checked_sub(0x40);
    let mut site_ordinals = [None; 16];
    let mut image = output(out, "image.jsonl")?;
    let mut pubouts = output(out, "pubout-sites.jsonl")?;
    let mut pubout_count = 0;
    for (ordinal, (key, builder)) in rom.insts.iter().enumerate() {
        let entry = ImageEntry { ordinal: Decimal(ordinal), map_key: Decimal(*key),
            instruction: Instruction(&builder.i) };
        json_line(&mut image, &entry)?;
        if builder.i.op == ZiskOp::PubOut.code() {
            json_line(&mut pubouts, &entry)?;
            pubout_count += 1;
        }
        if let Some(h) = candidate {
            if *key >= h && *key < rom.next_init_inst_addr && (*key - h) % 4 == 0 {
                site_ordinals[((*key - h) / 4) as usize] = Some(ordinal);
            }
        }
    }
    image.flush()?;
    pubouts.flush()?;
    let mut prefix = output(out, "trace-prefix.jsonl")?;
    let mut binary = output(out, "trace.u64le")?;
    let mut deviations = output(out, "tail-deviations.jsonl")?;
    let mut nonzero_tail = 0;
    for index in 0..total {
        let values = trace_fields(&trace[index]);
        let mut bytes = [0u8; 88];
        for (column, value) in values.iter().enumerate() {
            bytes[column * 8..(column + 1) * 8].copy_from_slice(&value.to_le_bytes());
        }
        binary.write_all(&bytes)?;
        if index < count {
            json_line(&mut prefix, &Row(&values))?;
        } else if values.iter().any(|value| *value != 0) {
            nonzero_tail += 1;
            json_line(&mut deviations, &TailDeviation { row: Decimal(index), values: Row(&values) })?;
        }
    }
    prefix.flush()?;
    binary.flush()?;
    deviations.flush()?;
    let observations = Observations {
        status: "UNTRUSTED_NATIVE_CAPTURE_NOT_A_CERTIFICATE",
        image_and_trace_are_independent_actual_calls: true,
        map_entries: Decimal(count), physical_rows: Decimal(total),
        columns: ["line", "a_offset_imm0", "a_imm1", "b_offset_imm0", "b_imm1", "ind_width",
            "op", "store_offset", "jmp_offset1", "jmp_offset2", "flags"],
        field_modulus: "18446744069414584321",
        rows_scanned: Decimal(total), cells_scanned: Decimal(total * 11),
        canonical_trace_byte_length: Decimal(total * 88), tail_start: Decimal(count),
        tail_count: Decimal(total - count), nonzero_tail_entries: Decimal(nonzero_tail),
        static_pubout_sites: Decimal(pubout_count),
        next_init_inst_addr_final: Decimal(rom.next_init_inst_addr), header_subtrahend: Decimal(0x40),
        header_subtraction_underflow: candidate.is_none(), header_candidate_only: candidate.map(Decimal),
        intended_header_sites_observed: Sites { rom: &rom, candidate, ordinals: &site_ordinals },
        rom_entry_constant: Decimal(ROM_ENTRY),
        rom_entry_lookup: rom.insts.get(&ROM_ENTRY).map(|i| Instruction(&i.i)),
        rom_exit_constant: Decimal(ROM_EXIT),
        rom_exit_lookup: rom.insts.get(&ROM_EXIT).map(|i| Instruction(&i.i)),
        min_program_pc: Decimal(rom.min_program_pc), max_program_pc: Decimal(rom.max_program_pc),
        max_bios_pc: Decimal(rom.max_bios_pc), offset_rom_na_unstructions: Decimal(rom.offset_rom_na_unstructions),
        entry_lookup_cache_length: Decimal(rom.rom_entry_instructions.len()),
        program_lookup_cache_length: Decimal(rom.rom_instructions.len()),
        nonaligned_lookup_cache_length: Decimal(rom.rom_na_instructions.len()),
        sorted_pc_list: PcList(&rom.sorted_pc_list), ro_data: RoData(&rom.ro_data),
    };
    let mut metadata = output(out, "observations.json")?;
    json_line(&mut metadata, &observations)?;
    metadata.flush()?;
    Ok(())
}
