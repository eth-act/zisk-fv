#!/usr/bin/env python3
"""Reproduce and classify the adversarial mutation corpus.

Full mode uses only the flake's pinned production derivations.  Boundary mode
classifies already-produced artifacts and is intended for quick development.
Neither mode accepts an arbitrary build command as evidence of a kill.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
NIX_FLAGS = ["--extra-experimental-features", "nix-command flakes"]
DIRECT_SOURCE_AIRS = {"ArithTable", "MemAlignRom"}

sys.path.insert(0, str(HERE))
import semdiff  # noqa: E402


class CorpusError(Exception):
    pass


@dataclasses.dataclass(frozen=True)
class Round:
    number: int
    air: str
    operator: str
    historical_class: str
    expected_outcome: str
    path: str
    line: int
    before: str
    after: str
    expected_artifacts: tuple[str, ...]


def load_corpus() -> tuple[dict[str, Any], list[Round]]:
    raw = json.loads((HERE / "corpus.json").read_text(encoding="utf-8"))
    if raw.get("schema") != 1:
        raise CorpusError(f"unsupported corpus schema {raw.get('schema')!r}")
    rounds = [Round(*row[:-1], tuple(row[-1])) for row in raw["rounds"]]
    numbers = [item.number for item in rounds]
    if numbers != list(range(1, 53)):
        raise CorpusError(f"corpus must contain rounds 1..52 once; got {numbers}")
    valid_outcomes = {"invalid", "equivalent", "compiler", "extractor",
                      "fidelity", "proof", "infrastructure"}
    for item in rounds:
        if item.expected_outcome not in valid_outcomes:
            raise CorpusError(f"round {item.number}: invalid expected outcome")
        p = Path(item.path)
        if p.is_absolute() or ".." in p.parts or not item.path.startswith("zisk/"):
            raise CorpusError(f"round {item.number}: unsafe source path {item.path!r}")
    return raw["identity"], rounds


def round_by_number(number: int) -> Round:
    _, rounds = load_corpus()
    return rounds[number - 1]


def diagnostic_patterns(item: Round) -> tuple[str, ...]:
    data = json.loads((HERE / "diagnostics.json").read_text(encoding="utf-8"))
    return tuple(data.get(str(item.number), ()))


def expected_detection_layer(item: Round) -> str:
    """Post-hardening expectation, separate from the historical verdict."""
    if item.historical_class == "INVALID":
        return "invalid"
    if item.historical_class == "REJECTED":
        return "compiler"
    if item.historical_class == "SYNTACTIC":
        return "equivalent"
    if item.historical_class == "EQUIVALENT" and item.number != 50:
        return "equivalent"
    if item.number == 27:
        return "fidelity"  # recorded scope boundary, not a promised weld
    return "proof"


def first_diagnostic(log: Path) -> str | None:
    for line in log.read_text(encoding="utf-8", errors="replace").splitlines():
        if "error:" in line.lower() or "error[" in line.lower():
            return line.strip()
    return None


def apply_mutation(source_root: Path, item: Round) -> Path:
    """Apply one anchored edit, rejecting drift or an already-mutated tree."""
    source_root = source_root.resolve()
    relative = Path(*Path(item.path).parts[1:])
    target = source_root / relative
    if not target.is_file() or target.is_symlink():
        raise CorpusError(f"round {item.number}: target is not a regular file: {target}")
    resolved = target.resolve()
    if source_root not in resolved.parents:
        raise CorpusError(f"round {item.number}: target escapes source copy: {target}")
    lines = target.read_text(encoding="utf-8").splitlines(keepends=True)
    if not 1 <= item.line <= len(lines):
        raise CorpusError(f"round {item.number}: recorded line {item.line} absent")
    old = lines[item.line - 1]
    body = old.rstrip("\r\n")
    if body.strip() != item.before.strip():
        raise CorpusError(
            f"round {item.number}: source precondition rejected at {item.path}:{item.line}\n"
            f"expected stripped line {item.before!r}\nfound {body!r}")
    # Preserve only the source line's indentation. The fixture owns all other
    # text, including spacing following a newly inserted comment marker.
    indent = body[:len(body) - len(body.lstrip())]
    newline = old[len(body):]
    lines[item.line - 1] = indent + item.after.lstrip() + newline
    target.chmod(target.stat().st_mode | stat.S_IWUSR)
    target.write_text("".join(lines), encoding="utf-8")
    return target


def make_tree_writable(root: Path) -> None:
    for directory, dirs, files in os.walk(root):
        path = Path(directory)
        path.chmod(path.stat().st_mode | stat.S_IWUSR | stat.S_IXUSR)
        for name in dirs:
            child = path / name
            if not child.is_symlink():
                child.chmod(child.stat().st_mode | stat.S_IWUSR | stat.S_IXUSR)
        for name in files:
            child = path / name
            if not child.is_symlink():
                child.chmod(child.stat().st_mode | stat.S_IWUSR)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def artifact_manifest(directory: Path) -> dict[str, str]:
    if not directory.is_dir():
        raise CorpusError(f"artifact directory absent: {directory}")
    return {str(p.relative_to(directory)): sha256(p)
            for p in sorted(directory.rglob("*")) if p.is_file()}


def artifact_delta(base: Path, mutant: Path) -> list[str]:
    left, right = artifact_manifest(base), artifact_manifest(mutant)
    return sorted(k for k in set(left) | set(right) if left.get(k) != right.get(k))


def lean_artifact_dir(path: Path) -> Path:
    return path / "Extraction" if (path / "Extraction").is_dir() else path


def extraction_manifest(path: Path) -> dict[str, str]:
    lean = lean_artifact_dir(path)
    container = path if lean != path else (path.parent if path.name == "Extraction" else path)
    result = {p.name: sha256(p) for p in lean.glob("*.lean") if p.is_file()}
    for name in ("MemAirFacts.md", "MemAlignRom.tsv"):
        candidate = container / name
        if candidate.is_file():
            result[name] = sha256(candidate)
    return result


def extraction_delta(base: Path, mutant: Path) -> list[str]:
    left, right = extraction_manifest(base), extraction_manifest(mutant)
    return sorted(k for k in set(left) | set(right) if left.get(k) != right.get(k))


def identity(path: Path) -> dict[str, Any]:
    if path.is_dir():
        manifest = artifact_manifest(path)
        encoded = json.dumps(manifest, sort_keys=True).encode()
        return {"path": str(path), "files": len(manifest),
                "sha256": hashlib.sha256(encoded).hexdigest()}
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path)}


@dataclasses.dataclass
class CommandResult:
    argv: list[str]
    cwd: str
    exit_code: int | None
    seconds: float
    timed_out: bool
    log: str


def run_command(argv: list[str], cwd: Path, timeout: int, log: Path) -> CommandResult:
    started = time.monotonic()
    timed_out = False
    exit_code: int | None
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w", encoding="utf-8") as stream:
        stream.write("argv: " + json.dumps(argv) + "\n")
        stream.write("cwd: " + str(cwd) + "\n\n")
        stream.flush()
        try:
            proc = subprocess.run(argv, cwd=cwd, stdout=stream,
                                  stderr=subprocess.STDOUT, timeout=timeout)
            exit_code = proc.returncode
        except subprocess.TimeoutExpired:
            timed_out, exit_code = True, None
            stream.write(f"\nTIMEOUT after {timeout}s\n")
    return CommandResult(argv, str(cwd), exit_code, time.monotonic() - started,
                         timed_out, str(log))


def classify(item: Round, semantic: dict[str, Any] | None, changed: list[str],
             roundtrip: CommandResult | None, baseline_proof: CommandResult | None,
             mutant_proof: CommandResult | None, compile_result: CommandResult | None = None
             ) -> tuple[str, str]:
    if compile_result and (compile_result.timed_out or compile_result.exit_code not in (0, 1)):
        return "infrastructure", "source compilation did not complete normally"
    if compile_result and compile_result.exit_code == 1:
        return "compiler", "mutated source was rejected by the pinned compiler"
    if roundtrip and (roundtrip.timed_out or roundtrip.exit_code == 2):
        return "infrastructure", "round-trip gate timed out or lacked artifacts"
    if semantic is None:
        return "infrastructure", "canonical pilout comparison did not complete"
    if semantic["equal"] and not changed:
        outcome = "invalid" if item.historical_class == "INVALID" else "equivalent"
        return outcome, "no canonical circuit or generated-artifact delta"
    if roundtrip and roundtrip.exit_code != 0:
        return "extractor", "mutant extraction failed its independent round-trip gate"
    if not changed:
        return "extractor", "canonical source circuit changed but generated artifacts did not"
    if baseline_proof is None or mutant_proof is None:
        return "infrastructure", "proof controls were not run"
    if baseline_proof.timed_out or baseline_proof.exit_code != 0:
        return "infrastructure", "baseline proof control was not green"
    if mutant_proof.timed_out:
        return "infrastructure", "mutant proof timed out; timeouts are not kills"
    if mutant_proof.exit_code == 0:
        return "fidelity", "mutated artifacts passed the proof build"
    if mutant_proof.exit_code == 1:
        diagnostic = first_diagnostic(Path(mutant_proof.log))
        patterns = diagnostic_patterns(item)
        if not diagnostic or not patterns or not any(p in diagnostic for p in patterns):
            return "infrastructure", (
                "mutant proof failed, but its first diagnostic did not match the "
                "fixture's expected proof boundary")
        return "proof", "green baseline and isolated mutant artifacts made the proof build fail"
    return "infrastructure", "mutant proof ended with an infrastructure exit"


def classify_equivalent_control(mutant_proof: CommandResult, outcome: str,
                                reason: str) -> tuple[str, str, dict[str, bool]]:
    """Apply the SYNTACTIC-control policy without hiding command failures."""
    proof_green = not mutant_proof.timed_out and mutant_proof.exit_code == 0
    false_positive = outcome == "proof"
    control = {"semantically_equivalent": True,
               "proof_green": proof_green,
               "proof_false_positive": false_positive}
    if proof_green:
        return "equivalent", "equivalent circuit preserved proof success", control
    if false_positive:
        return ("equivalent",
                "equivalent circuit triggered the recorded proof-boundary false positive",
                control)
    # A timeout, signal, abnormal exit, or unrelated diagnostic remains the
    # infrastructure result assigned by classify().
    return outcome, reason, control


def boundary(args: argparse.Namespace) -> dict[str, Any]:
    item = round_by_number(args.round)
    semantic = semdiff.compare(args.baseline_pilout, args.mutant_pilout)
    changed = extraction_delta(args.baseline_extraction, args.mutant_extraction)
    work = Path(tempfile.mkdtemp(prefix="zisk-boundary-"))
    baseline_gate = run_command(
        [sys.executable, str(args.repo / "tools/pilout-roundtrip/check.py"),
         "--pilout", str(args.baseline_pilout), "--extraction",
         str(lean_artifact_dir(args.baseline_extraction)), "--quiet"], args.repo, args.check_timeout,
        work / "baseline-roundtrip.log")
    mutant_gate = run_command(
        [sys.executable, str(args.repo / "tools/pilout-roundtrip/check.py"),
         "--pilout", str(args.mutant_pilout), "--extraction",
         str(lean_artifact_dir(args.mutant_extraction)), "--quiet"], args.repo, args.check_timeout,
        work / "mutant-roundtrip.log")
    result = {
        "round": item.number,
        "mode": "boundary",
        "expected_outcome": item.expected_outcome,
        "inputs": {
            "baseline_pilout": identity(args.baseline_pilout),
            "mutant_pilout": identity(args.mutant_pilout),
            "baseline_extraction": identity(args.baseline_extraction),
            "mutant_extraction": identity(args.mutant_extraction),
        },
        "semantic_diff": semantic,
        "artifact_delta": changed,
        "commands": [dataclasses.asdict(baseline_gate), dataclasses.asdict(mutant_gate)],
    }
    # Boundary mode intentionally stops before proof classification. It still
    # distinguishes invalid/equivalent/extractor at the artifact boundary.
    if baseline_gate.timed_out or baseline_gate.exit_code != 0:
        outcome, reason = "infrastructure", "baseline round-trip control was not green"
    elif mutant_gate.timed_out or mutant_gate.exit_code == 2:
        outcome, reason = "infrastructure", "mutant round-trip lacked artifacts or timed out"
    elif mutant_gate.exit_code != 0:
        outcome, reason = "extractor", "mutant extraction failed its independent round-trip gate"
    elif semantic["equal"] and not changed:
        outcome = "invalid" if item.historical_class == "INVALID" else "equivalent"
        reason = "no canonical circuit or generated-artifact delta"
    elif not changed:
        outcome, reason = "extractor", "canonical circuit delta was not extracted"
    else:
        outcome, reason = "fidelity", "artifact delta reached the proof boundary (proof not run)"
    complete = outcome in {"invalid", "equivalent", "extractor"}
    result.update(outcome=outcome, reason=reason, complete=complete)
    return result


def nix(*args: str) -> list[str]:
    return ["nix", *NIX_FLAGS, *args]


def nix_output_path(repo: Path, attr: str, override: Path | None, timeout: int,
                    log: Path, override_revision: str | None = None
                    ) -> tuple[Path | None, CommandResult]:
    argv = nix("build", "--no-write-lock-file", "--no-link", "--print-out-paths")
    if override is not None:
        # zisk-pilout uses zisk-src.rev in its version. A path override has no
        # rev unless it is supplied explicitly; retain the locked production
        # revision as metadata while Nix hashes the mutated source contents.
        suffix = f"?rev={override_revision}" if override_revision else ""
        argv += ["--override-input", "zisk-src", f"path:{override}{suffix}"]
    argv.append(f".#${attr}".replace("#$", "#"))
    result = run_command(argv, repo, timeout, log)
    if result.exit_code != 0:
        return None, result
    lines = Path(result.log).read_text(encoding="utf-8").splitlines()
    candidates = [Path(line.strip()) for line in lines if line.startswith("/nix/store/")]
    return (candidates[-1] if candidates else None), result


def resolve_pinned_zisk(repo: Path, timeout: int, log: Path) -> tuple[Path | None, CommandResult]:
    expression = f'(builtins.getFlake "path:{repo.resolve()}").inputs.zisk-src.outPath'
    result = run_command(nix("eval", "--no-write-lock-file", "--impure", "--raw",
                             "--expr", expression),
                         repo, timeout, log)
    if result.exit_code != 0:
        return None, result
    contents = log.read_text(encoding="utf-8")
    candidates = [token for token in contents.split() if token.startswith("/nix/store/")]
    return (Path(candidates[-1]) if candidates else None), result


def nix_direct_extraction(repo: Path, source: Path, pilout: Path, timeout: int,
                          log: Path) -> tuple[Path | None, CommandResult]:
    """Run the production extraction with an unchanged baseline pilout.

    ArithTable and MemAlignRom are read directly from source and do not change
    the compiled pilout. This expression invokes the same checked-in derivation
    while avoiding a causally unrelated ZisK workspace rebuild.
    """
    expression = f'''let
      fv = builtins.getFlake "path:{repo.resolve()}";
      system = builtins.currentSystem;
      pkgs = import fv.inputs.nixpkgs {{ inherit system; }};
    in pkgs.callPackage {repo.resolve() / "nix/extracted-lean.nix"} {{
      zisk-src = {source.resolve()};
      zisk-pilout = {pilout.resolve()};
      pil-extract = fv.packages.${{system}}.pil-extract;
      pil2-compiler = fv.packages.${{system}}.pil2-compiler;
      pil2-proofman-src = fv.inputs.pil2-proofman-src;
    }}'''
    result = run_command(nix("build", "--no-write-lock-file", "--impure", "--no-link",
                             "--print-out-paths", "--expr", expression), repo, timeout, log)
    if result.exit_code != 0:
        return None, result
    candidates = [Path(token) for token in log.read_text().split()
                  if token.startswith("/nix/store/")]
    return (candidates[-1] if candidates else None), result


def compile_mutation_source(repo: Path, source: Path, output: Path, timeout: int,
                            log: Path) -> CommandResult:
    return run_command(
        nix("run", "--no-write-lock-file", ".#compile-mutation", "--",
            str(source.resolve()), str(output.resolve())), repo, timeout, log)


def locked_zisk_revision(repo: Path) -> str:
    lock = json.loads((repo / "flake.lock").read_text(encoding="utf-8"))
    node_name = lock["nodes"]["root"]["inputs"]["zisk-src"]
    return lock["nodes"][node_name]["locked"]["rev"]


def repository_identity(repo: Path) -> dict[str, Any]:
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                          check=True, text=True, capture_output=True).stdout.strip()
    status = subprocess.run(["git", "status", "--porcelain"], cwd=repo,
                            check=True, text=True, capture_output=True).stdout.splitlines()
    dirty = [line[3:] for line in status if len(line) > 3]
    proof_prefixes = (
        "ZiskFv/", "ZiskFv.lean", "trust/", "tools/", "nix/", "scripts/", ".github/",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain", "flake.nix", "flake.lock")
    relevant = [path for path in dirty if path.startswith(proof_prefixes)]
    if relevant:
        raise CorpusError(f"proof-relevant repository files are dirty: {relevant}")
    tracked_raw = subprocess.run(["git", "ls-files", "-z"], cwd=repo, check=True,
                                 capture_output=True).stdout
    tracked = [p.decode() for p in tracked_raw.split(b"\0") if p]
    proof_files = sorted(path for path in tracked if path.startswith(proof_prefixes))
    digest = hashlib.sha256()
    for relative in proof_files:
        digest.update(relative.encode() + b"\0")
        digest.update((repo / relative).read_bytes())
        digest.update(b"\0")
    return {"head": head, "dirty_paths": dirty, "proof_relevant_dirty": relevant,
            "proof_file_count": len(proof_files), "proof_source_sha256": digest.hexdigest()}


def frozen_repository_key(value: dict[str, Any]) -> tuple[Any, ...]:
    return (value["head"], value["proof_source_sha256"],
            tuple(value["proof_relevant_dirty"]))


def require_frozen_repository(repo: Path, expected: dict[str, Any]) -> None:
    current = repository_identity(repo)
    if frozen_repository_key(current) != frozen_repository_key(expected):
        raise CorpusError(
            f"proof repository changed during mutation suite: expected "
            f"{frozen_repository_key(expected)}, got {frozen_repository_key(current)}")


def copy_proof_tree(repo: Path, destination: Path, pilout: Path,
                    extraction: Path) -> None:
    shutil.copytree(repo, destination, symlinks=True,
                    ignore=shutil.ignore_patterns(
                        ".git", ".lake", "build", "target", "tmp", "__pycache__",
                        "result", "result-*", "mutation-results", ".zisk-fv-mutation-work"))
    (destination / "build").mkdir()
    original_build = repo / "build"
    for entry in original_build.iterdir():
        if entry.name in {"zisk.pilout", "extraction"}:
            continue
        target = destination / "build" / entry.name
        resolved = entry.resolve()
        if entry.is_symlink() and str(resolved).startswith("/nix/store/"):
            os.symlink(resolved, target, target_is_directory=resolved.is_dir())
        elif entry.is_dir():
            copy_tree_cow(entry, target)
        else:
            shutil.copy2(entry, target, follow_symlinks=False)
    shutil.copy2(pilout, destination / "build" / "zisk.pilout")
    shutil.copytree(lean_artifact_dir(extraction),
                    destination / "build" / "extraction" / "Extraction")
    container = extraction if (extraction / "Extraction").is_dir() else extraction.parent
    for name in ("MemAirFacts.md", "MemAlignRom.tsv"):
        sidecar = container / name
        if sidecar.is_file():
            shutil.copy2(sidecar, destination / "build" / "extraction" / name)
    # Lake needs the generated library declaration, which belongs to populate
    # rather than the extraction derivation.
    src_lakefile = original_build / "extraction" / "lakefile.toml"
    if src_lakefile.is_file():
        shutil.copy2(src_lakefile, destination / "build" / "extraction" / "lakefile.toml")
    src_root = original_build / "extraction" / "Extraction.lean"
    if src_root.is_file():
        shutil.copy2(src_root, destination / "build" / "extraction" / "Extraction.lean")


def copy_tree_cow(source: Path, destination: Path) -> None:
    """Private copy, using reflinks where the filesystem supports them."""
    proc = subprocess.run(
        ["cp", "-a", "--reflink=auto", str(source), str(destination)],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if proc.returncode != 0:
        raise CorpusError(f"failed to copy mutable build input {source}: {proc.stdout.strip()}")


def install_proof_artifacts(repo: Path, proof_tree: Path, pilout: Path,
                            extraction: Path) -> None:
    """Replace all generated inputs in the suite-local proof workspace."""
    build = proof_tree / "build"
    target_extraction = build / "extraction"
    if target_extraction.exists():
        shutil.rmtree(target_extraction)
    shutil.copy2(pilout, build / "zisk.pilout")
    shutil.copytree(lean_artifact_dir(extraction), target_extraction / "Extraction")
    container = extraction if (extraction / "Extraction").is_dir() else extraction.parent
    for name in ("MemAirFacts.md", "MemAlignRom.tsv"):
        sidecar = container / name
        if sidecar.is_file():
            shutil.copy2(sidecar, target_extraction / name)
    original = repo / "build" / "extraction"
    for name in ("lakefile.toml", "Extraction.lean"):
        scaffold = original / name
        if scaffold.is_file():
            shutil.copy2(scaffold, target_extraction / name)


def archive_logs(result: dict[str, Any], logs: Path, archive: Path) -> None:
    archive.mkdir(parents=True, exist_ok=True)
    archived_logs = archive / "logs"
    if archived_logs.exists():
        raise CorpusError(f"result archive already exists: {archived_logs}")
    shutil.copytree(logs, archived_logs)
    for command in result.get("commands", []):
        original = Path(command["log"])
        if original.parent != logs and original.is_file():
            target = archived_logs / original.name
            if not target.exists():
                shutil.copy2(original, target)
        if original.is_file() or (archived_logs / original.name).is_file():
            command["log"] = str(Path("logs") / original.name)
    result["logs"] = "logs"
    result["workspace"] = None
    result["workspace_retained"] = False


def full(args: argparse.Namespace) -> dict[str, Any]:
    item = round_by_number(args.round)
    identity_record, _ = load_corpus()
    work_root = args.work_root or (args.repo.resolve().parent / ".zisk-fv-mutation-work")
    work_root.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix=f"zisk-mutation-{item.number:02d}-",
                                dir=work_root))
    logs = work / "logs"
    logs.mkdir()
    result: dict[str, Any] = {"round": item.number, "mode": "full",
                              "historical_outcome": item.expected_outcome,
                              "expected_detection_layer": expected_detection_layer(item),
                              "workspace": str(work), "commands": []}
    try:
        current_repository = repository_identity(args.repo)
        frozen_repository = getattr(args, "_frozen_repository", current_repository)
        args._frozen_repository = frozen_repository
        require_frozen_repository(args.repo, frozen_repository)
        result["repository"] = frozen_repository
        locked_rev = locked_zisk_revision(args.repo)
        if not locked_rev.startswith(identity_record["zisk_revision"]):
            raise CorpusError(
                f"pinned ZisK revision {locked_rev} differs from corpus identity "
                f"{identity_record['zisk_revision']}; version upgrades are not permitted")
        if args.zisk_source is None:
            source, source_command = resolve_pinned_zisk(
                args.repo, args.compile_timeout, logs / "resolve-zisk-source.log")
            result["commands"].append(dataclasses.asdict(source_command))
            if source is None:
                result.update(outcome="infrastructure", reason="could not resolve pinned ZisK source")
                return result
        else:
            source = args.zisk_source.resolve()
        source_copy = work / "zisk-source"
        shutil.copytree(source, source_copy, symlinks=False)
        make_tree_writable(source_copy)
        before_identity = identity(source)
        apply_mutation(source_copy, item)
        result["source"] = {"pinned": before_identity, "copy": str(source_copy),
                            "recorded_revision": identity_record["zisk_revision"],
                            "locked_revision": locked_rev}

        base_pilout = args.baseline_pilout
        base_extract = args.baseline_extraction
        if base_pilout is None or base_extract is None:
            base_pilout, cmd = nix_output_path(args.repo, "zisk-pilout", None,
                                               args.compile_timeout, logs / "baseline-pilout.log")
            result["commands"].append(dataclasses.asdict(cmd))
            base_extract, cmd2 = nix_output_path(args.repo, "extracted-lean", None,
                                                 args.compile_timeout, logs / "baseline-extraction.log")
            result["commands"].append(dataclasses.asdict(cmd2))
            if base_pilout is None or base_extract is None:
                result.update(outcome="infrastructure", reason="baseline production build failed")
                return result
        else:
            production_pilout, base_cmd = nix_output_path(
                args.repo, "zisk-pilout", None, args.compile_timeout,
                logs / "baseline-production-pilout.log")
            production_extract, extract_cmd = nix_output_path(
                args.repo, "extracted-lean", None, args.compile_timeout,
                logs / "baseline-production-extraction.log")
            result["commands"] += [dataclasses.asdict(base_cmd), dataclasses.asdict(extract_cmd)]
            if production_pilout is None or production_extract is None:
                result.update(outcome="infrastructure",
                              reason="could not reproduce supplied baseline", complete=False)
                return result
            if (not semdiff.compare(Path(base_pilout), production_pilout)["equal"]
                    or extraction_delta(Path(base_extract), production_extract)):
                result.update(outcome="infrastructure",
                              reason="supplied baseline differs from the pinned production pipeline",
                              complete=False)
                return result

        if item.air not in DIRECT_SOURCE_AIRS:
            compiler_baseline = getattr(args, "_compiler_baseline", None)
            if compiler_baseline is None:
                if args.baseline_compiler_pilout is not None:
                    baseline_compiled = args.baseline_compiler_pilout.resolve()
                    baseline_compile_cmd = CommandResult(
                        ["precompiled-mutation-baseline", str(baseline_compiled)],
                        str(args.repo), 0, 0.0, False,
                        str(logs / "baseline-compiler-control.log"))
                    Path(baseline_compile_cmd.log).write_text(
                        "Externally supplied mutation-compiler baseline; canonical equality checked.\n")
                else:
                    state = getattr(args, "_suite_state", work)
                    baseline_compiled = state / "baseline-compiler.pilout"
                    baseline_compile_cmd = compile_mutation_source(
                        args.repo, source, baseline_compiled, args.compile_timeout,
                        logs / "baseline-compiler-control.log")
                result["commands"].append(dataclasses.asdict(baseline_compile_cmd))
                if (baseline_compile_cmd.exit_code != 0 or baseline_compile_cmd.timed_out
                        or not baseline_compiled.is_file()
                        or not semdiff.compare(Path(base_pilout), baseline_compiled)["equal"]):
                    result.update(outcome="infrastructure",
                                  reason="mutation compiler baseline control did not reproduce the pinned circuit",
                                  complete=False)
                    return result
                compiler_baseline = (baseline_compiled, baseline_compile_cmd)
                args._compiler_baseline = compiler_baseline
            result["mutation_compiler_baseline"] = identity(compiler_baseline[0])

        if item.air in DIRECT_SOURCE_AIRS:
            mutant_pilout = Path(base_pilout)
            compile_result = CommandResult(
                ["production-pilout-reused", item.air], str(args.repo), 0, 0.0, False,
                str(logs / "mutant-pilout-not-rebuilt.log"))
            Path(compile_result.log).write_text(
                f"{item.air} is extracted directly from source; baseline pilout reused.\n")
        else:
            mutant_pilout = work / "mutant.pilout"
            compile_result = compile_mutation_source(
                args.repo, source_copy, mutant_pilout, args.compile_timeout,
                logs / "mutant-pilout.log")
            # A compiler may leave a partial output behind when it fails or is
            # killed. Never pass that file to extraction or count it as a kill.
            if (compile_result.timed_out or compile_result.exit_code != 0
                    or not mutant_pilout.is_file()):
                mutant_pilout = None
        result["commands"].append(dataclasses.asdict(compile_result))
        if mutant_pilout is None:
            log_text = Path(compile_result.log).read_text(encoding="utf-8", errors="replace")
            source_named = Path(item.path).name in log_text
            expected_rejection = (item.historical_class == "REJECTED" and source_named
                                  and compile_result.exit_code == 1
                                  and not compile_result.timed_out)
            outcome = "compiler" if expected_rejection else "infrastructure"
            reason = ("pinned compiler rejected the recorded invalid source edit"
                      if expected_rejection else
                      "source build failed without the expected compiler diagnostic")
            result.update(outcome=outcome, reason=reason, complete=expected_rejection)
            return result
        mutant_extract, extract_result = nix_direct_extraction(
            args.repo, source_copy, Path(mutant_pilout), args.compile_timeout,
            logs / "mutant-extraction.log")
        result["commands"].append(dataclasses.asdict(extract_result))
        if mutant_extract is None:
            result.update(outcome="extractor" if extract_result.exit_code == 1 else "infrastructure",
                          reason="production extraction did not complete")
            return result

        semantic = semdiff.compare(Path(base_pilout), mutant_pilout)
        changed = extraction_delta(Path(base_extract), mutant_extract)
        changed_stems = {Path(name).stem for name in changed}
        missing_historical = sorted(set(item.expected_artifacts) - changed_stems)
        result["inputs"] = {"baseline_pilout": identity(Path(base_pilout)),
                            "mutant_pilout": identity(mutant_pilout),
                            "baseline_extraction": identity(Path(base_extract)),
                            "mutant_extraction": identity(mutant_extract)}
        result["semantic_diff"], result["artifact_delta"] = semantic, changed
        result["historical_artifact_expectation"] = {
            "expected": list(item.expected_artifacts),
            "missing": missing_historical,
        }

        roundtrip = run_command(
            [sys.executable, str(args.repo / "tools/pilout-roundtrip/check.py"),
             "--pilout", str(mutant_pilout), "--extraction",
             str(lean_artifact_dir(mutant_extract)), "--quiet"],
            args.repo, args.check_timeout, logs / "roundtrip.log")
        result["commands"].append(dataclasses.asdict(roundtrip))

        baseline_roundtrip = run_command(
            [sys.executable, str(args.repo / "tools/pilout-roundtrip/check.py"),
             "--pilout", str(base_pilout), "--extraction",
             str(lean_artifact_dir(Path(base_extract))), "--quiet"],
            args.repo, args.check_timeout, logs / "baseline-roundtrip.log")
        result["commands"].append(dataclasses.asdict(baseline_roundtrip))
        if baseline_roundtrip.timed_out or baseline_roundtrip.exit_code != 0:
            result.update(outcome="infrastructure",
                          reason="baseline round-trip control was not green", complete=False)
            return result

        if missing_historical:
            result.update(outcome="extractor",
                          reason="mutant extraction lost historically observed artifacts",
                          complete=True)
            return result

        if (semantic["equal"] and not changed) or roundtrip.exit_code != 0:
            outcome, reason = classify(item, semantic, changed, roundtrip, None, None)
            result.update(outcome=outcome, reason=reason, complete=True)
            return result
        if args.skip_proof:
            result.update(outcome="infrastructure",
                          reason="proof controls explicitly skipped", complete=False)
            return result

        state = getattr(args, "_suite_state", work)
        proof_tree = state / "proof-work"
        if not proof_tree.exists():
            copy_proof_tree(args.repo, proof_tree, Path(base_pilout), Path(base_extract))
            seed_cache = args.repo / ".lake"
            if seed_cache.is_dir():
                copy_tree_cow(seed_cache, proof_tree / ".lake")
        proof_argv = nix("develop", "--no-write-lock-file", str(args.repo.resolve()),
                         "-c", "lake", "build", "--log-level=warning")
        require_frozen_repository(args.repo, frozen_repository)
        install_proof_artifacts(args.repo, proof_tree, Path(base_pilout), Path(base_extract))
        baseline_proof = run_command(proof_argv, proof_tree, args.proof_timeout,
                                     logs / "baseline-proof.log")
        if baseline_proof.timed_out or baseline_proof.exit_code != 0:
            result["commands"].append(dataclasses.asdict(baseline_proof))
            result.update(outcome="infrastructure", reason="baseline proof control was not green",
                          complete=False)
            return result
        install_proof_artifacts(args.repo, proof_tree, mutant_pilout, mutant_extract)
        require_frozen_repository(args.repo, frozen_repository)
        mutant_proof = run_command(proof_argv, proof_tree, args.proof_timeout,
                                   logs / "mutant-proof.log")
        result["commands"] += [dataclasses.asdict(baseline_proof),
                               dataclasses.asdict(mutant_proof)]
        outcome, reason = classify(item, semantic, changed, roundtrip,
                                   baseline_proof, mutant_proof, compile_result)
        diagnostic = first_diagnostic(Path(mutant_proof.log)) if mutant_proof.exit_code else None
        result["proof_diagnostic"] = diagnostic
        if semantic["equal"] and item.historical_class == "SYNTACTIC":
            outcome, reason, result["control"] = classify_equivalent_control(
                mutant_proof, outcome, reason)
        result.update(outcome=outcome, reason=reason,
                      complete=outcome != "infrastructure")
        return result
    except (CorpusError, OSError, ValueError, subprocess.SubprocessError) as exc:
        result.update(outcome="infrastructure", reason=str(exc), complete=False)
        return result
    finally:
        frozen = getattr(args, "_frozen_repository", None)
        if frozen is not None:
            try:
                require_frozen_repository(args.repo, frozen)
            except (CorpusError, OSError, subprocess.SubprocessError) as exc:
                result.update(outcome="infrastructure", reason=str(exc), complete=False)
        archive = getattr(args, "_archive_dir", None)
        if archive is not None:
            try:
                archive_logs(result, logs, archive)
            except (CorpusError, OSError) as exc:
                result.update(outcome="infrastructure", reason=str(exc), complete=False)
        if getattr(args, "_force_cleanup", False) or (args.cleanup and result.get("complete")):
            shutil.rmtree(work, ignore_errors=True)


def write_result(result: dict[str, Any], destination: Path | None) -> None:
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if destination:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(text, encoding="utf-8")
    print(text, end="")


def parser() -> argparse.ArgumentParser:
    out = argparse.ArgumentParser()
    sub = out.add_subparsers(dest="command", required=True)
    listing = sub.add_parser("list")
    listing.add_argument("--json", action="store_true")
    apply = sub.add_parser("apply")
    apply.add_argument("--round", type=int, required=True, choices=range(1, 53))
    apply.add_argument("--source", type=Path, required=True)
    b = sub.add_parser("boundary")
    b.add_argument("--round", type=int, required=True, choices=range(1, 53))
    b.add_argument("--baseline-pilout", type=Path, required=True)
    b.add_argument("--mutant-pilout", type=Path, required=True)
    b.add_argument("--baseline-extraction", type=Path, required=True)
    b.add_argument("--mutant-extraction", type=Path, required=True)
    b.add_argument("--repo", type=Path, default=REPO)
    b.add_argument("--check-timeout", type=int, default=300)
    b.add_argument("--output", type=Path)
    def full_options(f: argparse.ArgumentParser, include_round: bool = True) -> None:
        if include_round:
            f.add_argument("--round", type=int, required=True, choices=range(1, 53))
        f.add_argument("--repo", type=Path, default=REPO)
        f.add_argument("--zisk-source", type=Path,
                   help="pinned source tree; defaults to the flake input store path")
        f.add_argument("--baseline-pilout", type=Path)
        f.add_argument("--baseline-extraction", type=Path)
        f.add_argument("--baseline-compiler-pilout", type=Path,
                       help="cached unmutated compile-mutation output; canonical equality is required")
        f.add_argument("--work-root", type=Path)
        f.add_argument("--compile-timeout", type=int, default=3600)
        f.add_argument("--check-timeout", type=int, default=300)
        f.add_argument("--proof-timeout", type=int, default=1800)
        f.add_argument("--skip-proof", action="store_true")
        f.add_argument("--cleanup", action="store_true",
                   help="remove a completed workspace (log paths then become archival metadata only)")
        f.add_argument("--output", type=Path)
    f = sub.add_parser("full")
    full_options(f)
    suite = sub.add_parser("suite")
    full_options(suite, include_round=False)
    suite.add_argument("--profile", choices=("boundary", "full"), required=True)
    suite.add_argument("--round", action="append", type=int, choices=range(1, 53),
                       help="override the profile's round set; repeatable")
    suite.add_argument("--results-dir", type=Path, required=True)
    return out


def main(argv: list[str]) -> int:
    args = parser().parse_args(argv)
    if args.command == "list":
        identity_record, rounds = load_corpus()
        if args.json:
            print(json.dumps({"identity": identity_record,
                              "rounds": [dataclasses.asdict(r) for r in rounds]}, indent=2))
        else:
            for r in rounds:
                print(f"{r.number:02d} {r.air:18} {r.operator:17} "
                      f"historical={r.historical_class:9} expected={r.expected_outcome}")
        return 0
    if args.command == "apply":
        target = apply_mutation(args.source, round_by_number(args.round))
        print(target)
        return 0
    if args.command == "suite":
        rounds = (args.round if args.round else
                  [5, 7, 32, 38, 50] if args.profile == "boundary" else list(range(1, 53)))
        args.results_dir.mkdir(parents=True, exist_ok=True)
        results = []
        work_root = args.work_root or (args.repo.resolve().parent / ".zisk-fv-mutation-work")
        work_root.mkdir(parents=True, exist_ok=True)
        suite_state = Path(tempfile.mkdtemp(prefix="zisk-mutation-suite-", dir=work_root))
        args._frozen_repository = repository_identity(args.repo)
        try:
            for number in rounds:
                per_round = argparse.Namespace(**vars(args))
                per_round.command = "full"
                per_round.round = number
                per_round.output = None
                per_round._suite_state = suite_state
                per_round._archive_dir = args.results_dir / f"round-{number:02d}"
                per_round._force_cleanup = True
                value = full(per_round)
                if hasattr(per_round, "_compiler_baseline"):
                    args._compiler_baseline = per_round._compiler_baseline
                (per_round._archive_dir / "result.json").write_text(
                    json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
                results.append(value)
        finally:
            shutil.rmtree(suite_state, ignore_errors=True)
        aggregate = {
            "profile": args.profile,
            "rounds": rounds,
            "counts": {name: sum(r.get("outcome") == name for r in results)
                       for name in ("invalid", "equivalent", "compiler", "extractor",
                                    "fidelity", "proof", "infrastructure")},
            "complete": all(r.get("complete") for r in results),
            "infrastructure_rounds": [r.get("round") for r in results
                                      if r.get("outcome") == "infrastructure"],
        }
        def meets_expected(value: dict[str, Any]) -> bool:
            expected = value.get("expected_detection_layer")
            if expected == "equivalent":
                return (value.get("outcome") == "equivalent"
                        and value.get("control", {}).get("proof_false_positive") is not True)
            return value.get("outcome") == expected
        aggregate["unexpected_rounds"] = [r.get("round") for r in results
                                          if not meets_expected(r)]
        (args.results_dir / "summary.json").write_text(
            json.dumps(aggregate, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(json.dumps(aggregate, indent=2, sort_keys=True))
        return 0 if (aggregate["complete"] and not aggregate["infrastructure_rounds"]
                     and not aggregate["unexpected_rounds"]) else 1
    try:
        result = boundary(args) if args.command == "boundary" else full(args)
    except (CorpusError, OSError, ValueError) as exc:
        result = {"outcome": "infrastructure", "reason": str(exc), "complete": False}
    write_result(result, args.output)
    return 0 if result.get("complete") and result.get("outcome") != "infrastructure" else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
