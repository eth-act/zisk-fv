#!/usr/bin/env python3
"""Capture real 9ca ROM producers, without modifying upstream or proof interfaces.

Requires private source/cache workspace and explicit immutable tool locations.
The output is UNTRUSTED data, not an acceptance or source-provenance certificate.
Both native calls use identical ELF bytes but their correlation is not proved.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import tarfile
import tomllib

PIN = "9ca88b5b182fd7d534343181354f5319528c82d2"
COLUMNS = ["line", "a_offset_imm0", "a_imm1", "b_offset_imm0", "b_imm1", "ind_width",
           "op", "store_offset", "jmp_offset1", "jmp_offset2", "flags"]


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def elf_metadata(path):
    data = path.read_bytes()
    if data[:7] != b"\x7fELF\x02\x01\x01":
        raise ValueError("Expected actual ELF64 little-endian version1 input")
    h = struct.unpack_from("<HHIQQQIHHHHHH", data, 16)
    if h[1] != 243:
        raise ValueError("ELF machine is not RISC-V")
    sections = [struct.unpack_from("<IIQQQQIIQQ", data, h[5] + i * h[10])
                for i in range(h[11])]
    names_section = sections[h[12]]
    names = data[names_section[4]:names_section[4] + names_section[5]]
    result = []
    for s in sections:
        end = names.index(0, s[0])
        name = names[s[0]:end].decode()
        entry = dict(zip(["type", "flags", "address", "file_offset", "size", "link", "info",
                          "alignment", "entry_size"], map(str, s[1:])))
        entry["name"] = name
        if s[1] != 8:
            payload = data[s[4]:s[4] + s[5]]
            if len(payload) != s[5]:
                raise ValueError("Truncated actual ELF section")
            entry["sha256"] = hashlib.sha256(payload).hexdigest()
            if name == ".text":
                entry["bytes_hex"] = payload.hex()
        result.append(entry)
    phdrs = []
    for i in range(h[9]):
        p = struct.unpack_from("<IIQQQQQQ", data, h[4] + i * h[8])
        phdrs.append(dict(zip(["type", "flags", "offset", "vaddr", "paddr", "filesz", "memsz", "align"], map(str, p))))
    return {"entry": str(h[3]), "machine": str(h[1]), "flags": str(h[6]),
            "sections": result, "program_headers": phdrs}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zisk-git", required=True, type=Path)
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--cross-cc", required=True, type=Path, help="Pinned Nix cross-compiler package")
    parser.add_argument("--libclang", required=True, type=Path, help="Pinned libclang21 library directory")
    parser.add_argument("--rust-toolchain", required=True, type=Path, help="Immutable native Rust toolchain directory")
    parser.add_argument("--llvm-openmp", type=Path, help="Real LLVM libomp using its official libiomp5 compatibility name")
    parser.add_argument("--continue-native", action="store_true", help="Continue an initial link failure using identical driver/ELF")
    parser.add_argument("--finalize-only", action="store_true", help="Finalize existing captured data; never compile or run the producer")
    args = parser.parse_args()
    same_inputs = args.continue_native or args.finalize_only
    tool = Path(__file__).resolve().parent
    workspace = args.workspace.resolve()
    source = workspace / "source"
    cargo_home = workspace / "cargo-home"
    output = args.output.resolve()
    workspace.mkdir(parents=True, exist_ok=True)
    if not cargo_home.is_dir():
        raise ValueError("Seed a PRIVATE cargo-home with cp -a --reflink=never first; never use global caches")
    if output.exists():
        if not args.finalize_only and (not args.continue_native or any(output.iterdir())):
            raise ValueError("Refusing to replace an existing fixture; use a new output path")
    else:
        output.mkdir(parents=True)
    commands = json.loads((workspace / "commands.json").read_text()) if same_inputs else []
    initial_failure = None
    if args.finalize_only:
        success = json.loads((workspace / "native-result.json").read_text())
        if success["exit_code"] != 0 or success["native_log_sha256"] != sha(workspace / "native-producer.log"):
            raise ValueError("Metadata finalization requires the recorded successful native result")
        failed_log = workspace / "native-producer-initial.log"
        if failed_log.exists():
            initial_failure = {"file": failed_log.name, "sha256": sha(failed_log),
                               "classification": "native linker setup failure; not a source/data/proof kill"}
    elif args.continue_native:
        failed_log = workspace / "native-producer-initial.log"
        if failed_log.exists():
            raise ValueError("The initial continuation was already attempted; preserve its outcome")
        (workspace / "native-producer.log").rename(failed_log)
        initial_failure = {"file": failed_log.name, "sha256": sha(failed_log),
                           "classification": "native linker setup failure; not a source/data/proof kill"}
        for command in commands:
            if command["log"] == "native-producer.log":
                command["log"] = failed_log.name
    env = os.environ.copy()
    shims = workspace / "tool-shims"
    shims.mkdir(exist_ok=True)
    # proofman invokes make -j explicitly. The final -j2 overrides its unbounded flag.
    (shims / "make").write_text("#!/usr/bin/env bash\nexec /usr/bin/make \"$@\" -j2\n")
    (shims / "make").chmod(0o755)
    for name in ["gcc", "as", "ar", "ld"]:
        destination = shims / f"riscv64-unknown-elf-{name}"
        if destination.is_symlink():
            destination.unlink()
        destination.symlink_to(args.cross_cc / "bin" / f"riscv64-none-elf-{name}")
    env.update(CARGO_HOME=str(cargo_home), CARGO_TARGET_DIR=str(workspace / "target"),
               CARGO_BUILD_JOBS="2", MAKEFLAGS="-j2", CMAKE_BUILD_PARALLEL_LEVEL="2",
               NUM_JOBS="2", RAYON_NUM_THREADS="2", OMP_NUM_THREADS="2", LIBCLANG_PATH=str(args.libclang),
               RUSTC=str(args.rust_toolchain / "bin/rustc"))
    env["PATH"] = ":".join(map(str, [shims, args.cross_cc / "bin", args.rust_toolchain / "bin"])) + ":" + env["PATH"]
    openmp = None
    if args.llvm_openmp is not None:
        actual_runtime = args.llvm_openmp.resolve(strict=True)
        runtime_dir = workspace / "openmp-runtime"
        runtime_dir.mkdir(exist_ok=True)
        alias = runtime_dir / "libiomp5.so"
        if alias.is_symlink():
            alias.unlink()
        alias.symlink_to(actual_runtime)
        env["LIBRARY_PATH"] = str(runtime_dir) + (":" + env["LIBRARY_PATH"] if env.get("LIBRARY_PATH") else "")
        openmp = {"actual_library": str(actual_runtime), "sha256": sha(actual_runtime),
                  "private_compatibility_alias": str(alias),
                  "alias_contract": "https://github.com/llvm/llvm-project/blob/main/openmp/runtime/src/CMakeLists.txt"}

    def run(command, name, cwd=None, capture=False):
        command = list(map(str, command))
        commands.append({"argv": command, "cwd": str(cwd or workspace), "log": name})
        (workspace / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        with (workspace / name).open("w") as log:
            result = subprocess.run(command, cwd=cwd or workspace, env=env, stdout=subprocess.PIPE if capture else log,
                                    stderr=subprocess.STDOUT if capture else log, check=True, text=capture)
        if capture:
            (workspace / name).write_text(result.stdout)
            return result.stdout.strip()

    archive = workspace / "source.tar"
    if not same_inputs:
        if run(["git", "-C", args.zisk_git, "rev-parse", "HEAD"], "source-head.log", capture=True) != PIN:
            raise ValueError("Source git HEAD must be the distinct pinned 9ca source, not the PIL pin")
        run(["git", "-C", args.zisk_git, "archive", "--format=tar", f"--output={archive}", PIN], "source-archive.log")
    with tarfile.open(archive) as tar:
        if source.exists():
            # Verify every archived regular input, not just the function we call.
            for member in tar.getmembers():
                if member.isfile():
                    actual = source / member.name
                    with tar.extractfile(member) as original:
                        expected = hashlib.file_digest(original, "sha256").hexdigest()
                    if sha(actual) != expected:
                        raise ValueError(f"Private source differs from exact pin: {member.name}")
                elif member.issym() and os.readlink(source / member.name) != member.linkname:
                    raise ValueError(f"Private source symlink differs: {member.name}")
        else:
            source.mkdir()
            tar.extractall(source, filter="data")
    float_path = source / "lib-float/c/lib/ziskfloat.elf"
    float_before = sha(float_path)
    source_lock_before = sha(source / "Cargo.lock")
    driver = workspace / "driver"
    if same_inputs:
        if (driver / "src/main.rs").read_bytes() != (tool / "main.rs").read_bytes():
            raise ValueError("Continuation may not change the compiled Rust caller")
    else:
        if driver.exists():
            raise ValueError("Refusing to overwrite an existing native driver workspace")
        (driver / "src").mkdir(parents=True)
        shutil.copyfile(tool / "main.rs", driver / "src/main.rs")
    lock = tomllib.loads((source / "Cargo.lock").read_text())

    def version(name):
        candidates = [p["version"] for p in lock["package"] if p["name"] == name]
        if len(candidates) != 1:
            raise ValueError(f"Expected exactly one pinned {name} version")
        return candidates[0]

    fields = tomllib.loads((source / "Cargo.toml").read_text())["workspace"]["dependencies"]["fields"]
    manifest = f'''[package]
name = "finite-return-rom-capture"
version = "0.1.0"
edition = "2021"

[dependencies]
sm-rom = {{ path = {json.dumps(str(source / "state-machines/rom"))} }}
zisk-core = {{ path = {json.dumps(str(source / "core"))} }}
zisk-pil = {{ path = {json.dumps(str(source / "pil"))} }}
fields = {{ git = {json.dumps(fields["git"])}, tag = {json.dumps(fields["tag"])} }}
serde = {{ version = "={version('serde')}", features = ["derive"] }}
serde_json = {{ version = "={version('serde_json')}" }}
'''
    if same_inputs:
        if (driver / "Cargo.toml").read_text() != manifest:
            raise ValueError("Continuation may not change the compiled caller dependencies")
    else:
        (driver / "Cargo.toml").write_text(manifest)
        # Seed the actual upstream versions; Cargo only adds this external caller package.
        shutil.copyfile(source / "Cargo.lock", driver / "Cargo.lock")
    caller_lock_before = sha(driver / "Cargo.lock")
    gcc = args.cross_cc / "bin/riscv64-none-elf-gcc"
    gcc_version = run([gcc, "--version"], "gcc-version.log", capture=True)
    linker = Path(run([gcc, "-print-prog-name=ld"], "linker-path.log", capture=True))
    linker_version = run([linker, "--version"], "linker-version.log", capture=True) if linker.is_absolute() else None
    compiler_configuration = run([gcc, "-v"], "gcc-configuration.log", capture=True)
    wrapper_add_flags = args.cross_cc / "nix-support/add-flags.sh"
    wrapper_flag_source = wrapper_add_flags.read_text()
    wrapper_source = gcc.read_text()
    rustc = args.rust_toolchain / "bin/rustc"
    cargo = args.rust_toolchain / "bin/cargo"
    rust_version = run([rustc, "-Vv"], "rustc-version.log", capture=True)
    cargo_version = run([cargo, "--version"], "cargo-version.log", capture=True)
    elf = workspace / "guest.elf"
    if same_inputs:
        previous_elf = json.loads((workspace / "guest-metadata.json").read_text())
        if sha(elf) != previous_elf["sha256"]:
            raise ValueError("Continuation may not change the already compiled guest ELF")
    else:
        run([gcc, "-march=rv64im", "-mabi=lp64", "-mno-relax", "-nostdlib", "-nostartfiles", "-static",
             "-Wl,--no-relax", "-Wl,--build-id=none", f"-Wl,-T,{tool / 'guest.ld'}", tool / "guest.S", "-o", elf],
            "guest-compile.log")
    elf_info = elf_metadata(elf)
    (workspace / "guest-metadata.json").write_text(json.dumps({"sha256": sha(elf), **elf_info}, indent=2) + "\n")
    if openmp is not None:
        dynamic = run(["readelf", "-d", actual_runtime], "openmp-dynamic.log", capture=True)
        symbols = run(["nm", "-D", "--defined-only", actual_runtime], "openmp-exports.log", capture=True)
        openmp["soname_evidence"] = [line.strip() for line in dynamic.splitlines() if "(SONAME)" in line]
        openmp["required_abi_exports_observed"] = {
            name: any(line.split()[-1].split("@")[0] == name for line in symbols.splitlines() if line.split())
            for name in ["__kmpc_fork_call", "omp_get_num_threads", "GOMP_parallel"]}
        if not all(openmp["required_abi_exports_observed"].values()):
            raise ValueError("The supplied real runtime lacks the expected LLVM OpenMP ABI")
    raw = workspace / "raw"
    if not args.finalize_only:
        # Actual producer execution, separate from recoverable metadata finalization.
        run([cargo, "run", "--offline", "--manifest-path", driver / "Cargo.toml", "--", elf, raw], "native-producer.log")
        (workspace / "native-result.json").write_text(json.dumps({
            "exit_code": 0, "native_log_sha256": sha(workspace / "native-producer.log"),
            "driver_source_sha256": sha(driver / "src/main.rs"), "elf_sha256": sha(elf),
        }, indent=2) + "\n")
    if args.continue_native and sha(driver / "Cargo.lock") != caller_lock_before:
        raise ValueError("Environment-only continuation changed caller dependency resolution")
    if sha(float_path) != float_before or sha(source / "Cargo.lock") != source_lock_before:
        raise ValueError("A build changed the pinned embedded float or source lock; no fixture accepted")
    observations = json.loads((raw / "observations.json").read_text())
    total = int(observations["physical_rows"])
    if observations["columns"] != COLUMNS or total != 4194304:
        raise ValueError("Actual source trace dimensions/order differ; no silent narrowing")
    if (raw / "trace.u64le").stat().st_size != total * 11 * 8:
        raise ValueError("Actual full trace byte length is incomplete")
    # Independent serialization check: prefix JSON must match the actual binary rows exactly.
    rows = 0
    with (raw / "trace-prefix.jsonl").open() as prefix, (raw / "trace.u64le").open("rb") as binary:
        for line in prefix:
            values = json.loads(line)
            if len(values) != 11 or any(not isinstance(v, str) for v in values):
                raise ValueError("Trace prefix does not preserve exact decimal-string fields")
            if tuple(map(int, values)) != struct.unpack("<11Q", binary.read(88)):
                raise ValueError("Independent trace projections disagree")
            rows += 1
    if rows != int(observations["map_entries"]):
        raise ValueError("Trace prefix does not preserve every final image ordinal")
    files = {}
    for name in ["image.jsonl", "trace-prefix.jsonl", "trace.u64le", "tail-deviations.jsonl"]:
        actual = raw / name
        destination = output / (name + ".gz")
        if not args.finalize_only:
            with actual.open("rb") as incoming, destination.open("wb") as backing:
                with gzip.GzipFile(filename="", fileobj=backing, mode="wb", mtime=0) as compressed:
                    shutil.copyfileobj(incoming, compressed)
        files[name] = {"file": destination.name, "raw_bytes": str(actual.stat().st_size),
                       "raw_sha256": sha(actual), "gzip_sha256": sha(destination)}
    for name in ["observations.json", "pubout-sites.jsonl"]:
        if not args.finalize_only:
            shutil.copyfile(raw / name, output / name)
        files[name] = {"file": name, "raw_sha256": sha(output / name)}
    if not args.finalize_only:
        shutil.copyfile(elf, output / "guest.elf")
        shutil.copyfile(driver / "Cargo.lock", output / "caller.Cargo.lock")
    source_files = ["core/src/elf2rom.rs", "core/src/riscv2zisk.rs", "core/src/riscv2zisk_context.rs",
                    "core/src/zisk_inst.rs", "core/src/zisk_inst_builder.rs", "core/src/zisk_rom.rs",
                    "state-machines/rom/src/rom.rs", "state-machines/rom/Cargo.toml",
                    "pil/src/pil_helpers/traces.rs", "Cargo.toml", "Cargo.lock", "lib-float/c/lib/ziskfloat.elf"]
    record = {
        "status": "UNTRUSTED_NATIVE_CAPTURE_NOT_A_CERTIFICATE", "source_revision": PIN,
        "source_archive_sha256": sha(archive), "source_files_sha256": {p: sha(source / p) for p in source_files},
        "native_profile": "ordinary default features; no aeneas_extract, no source pruning",
        "trace_producer": "sm_rom::RomSM::compute_custom_trace_rom::<fields::Goldilocks>",
        "image_producer": "zisk_core::Riscv2zisk::new(same_elf_bytes).run()",
        "independent_calls_correlation_proved": False, "native_pointer_addresses_diagnostic_and_process_dependent": True,
        "not_proved": ["Root/Accepted", "whole-image authentication", "ELF compiler faithfulness",
                       "source provenance partition", "kernel universal ROM erasure", "9ca equals b632",
                       "full trace constructibility", "execution or loop termination", "32 dynamic PubOut executions"],
        "elf": {"file": "guest.elf", "sha256": sha(elf), **elf_info},
        "caller_lock_sha256": sha(driver / "Cargo.lock"), "source_lock_sha256": source_lock_before,
        "tools": {"cross_cc_package": str(args.cross_cc), "gcc_sha256": sha(gcc), "gcc_version": gcc_version,
                  "compiler_reported_linker_name": str(linker),
                  "exact_invoked_linker_path_observed": False,
                  "compiler_reported_absolute_linker_sha256": sha(linker) if linker.is_absolute() else None,
                  "compiler_reported_absolute_linker_version": linker_version,
                  "relative_linker_caveat": "No exec trace was captured; a relative name is not resolved using caller PATH",
                  "gcc_configuration": compiler_configuration,
                  "compiler_wrapper_add_flags_sha256": sha(wrapper_add_flags),
                  "compiler_declared_bintools_search_assignments": [
                      line for line in wrapper_flag_source.splitlines() if line.startswith("path_backup=")],
                  "compiler_declared_bintools_source_lines": [
                      line.strip() for line in wrapper_source.splitlines() if "source " in line and "binutils-wrapper" in line],
                  "rust_toolchain": str(args.rust_toolchain), "rustc_sha256": sha(rustc), "rustc_version": rust_version,
                  "cargo_sha256": sha(cargo), "cargo_version": cargo_version, "libclang": str(args.libclang),
                  "llvm_openmp": openmp},
        "environment": {k: env[k] for k in ["CARGO_BUILD_JOBS", "MAKEFLAGS", "CMAKE_BUILD_PARALLEL_LEVEL",
                        "NUM_JOBS", "RAYON_NUM_THREADS", "OMP_NUM_THREADS", "LIBCLANG_PATH", "RUSTC"]},
        "library_path": env.get("LIBRARY_PATH"),
        "tool_sources_sha256": {name: sha(tool / name) for name in ["main.rs", "capture.py", "guest.S", "guest.ld"]},
        "commands": commands, "files": files,
        "native_log_sha256": sha(workspace / "native-producer.log"),
        "initial_native_link_failure": initial_failure,
        "source_citations": {"complete_image": "core/src/elf2rom.rs:16-68",
                             "actual_public_trace": "state-machines/rom/src/rom.rs:274-297",
                             "actual_private_trace": "state-machines/rom/src/rom.rs:204-267",
                             "observational_header_candidate": "core/src/riscv2zisk_context.rs:2654-2899"},
    }
    (output / "manifest.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"output": str(output), "map_entries": observations["map_entries"],
                      "physical_rows": observations["physical_rows"], "rows_scanned": observations["rows_scanned"],
                      "cells_scanned": observations["cells_scanned"], "header_candidate_only": observations["header_candidate_only"],
                      "static_pubout_sites": observations["static_pubout_sites"],
                      "nonzero_tail_entries": observations["nonzero_tail_entries"]}, indent=2))


if __name__ == "__main__":
    main()
