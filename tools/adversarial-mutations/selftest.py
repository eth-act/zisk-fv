#!/usr/bin/env python3
"""Fast, standard-library-only self-tests for corpus mechanics."""

from __future__ import annotations

import ast
import shutil
import sys
import tempfile
from collections import Counter
from pathlib import Path
from unittest import mock
from contextlib import ExitStack

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import runner  # noqa: E402
import semdiff  # noqa: E402
import sites  # noqa: E402


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def test_corpus() -> None:
    identity, rounds = runner.load_corpus()
    check(identity["zisk_revision"] == "b632745", "unexpected pinned identity")
    # Keep the published sweep's historical counts separate from new fixtures.
    historical = [r for r in rounds if r.historical_class != "NEW"]
    check(len(historical) == 52, "historical round count")
    check(sum(r.historical_class == "VALID" for r in historical) == 35, "valid count")
    check(sum(r.expected_outcome == "proof" for r in historical) == 24, "caught count")
    check(sum(r.expected_outcome == "fidelity" for r in historical) == 11, "missed count")
    check(len(rounds) == 53, "round count")
    check(runner.expected_detection_layer(runner.round_by_number(53)) == "fidelity_gate",
          "byte-table fixture detection layer")
    check(runner.expected_detection_layer(runner.round_by_number(27)) == "proof",
          "round 27 is caught after Main c41 is tied")
    check(runner.expected_detection_layer(runner.round_by_number(50)) == "fidelity_gate",
          "production ROM target")


def synthetic_source(root: Path, item: runner.Round, line: str | None = None) -> Path:
    target = root / Path(*Path(item.path).parts[1:])
    target.parent.mkdir(parents=True)
    rows = ["padding\n"] * (item.line - 1)
    rows.append("    " + (item.before if line is None else line) + "\n")
    target.write_text("".join(rows), encoding="utf-8")
    return target


def test_isolation_and_precondition() -> None:
    item = runner.round_by_number(1)
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp) / "base"
        copy = Path(tmp) / "copy"
        original = synthetic_source(base, item).read_bytes()
        shutil.copytree(base, copy)
        synthetic_source_path(copy, item).chmod(0o444)
        runner.make_tree_writable(copy)
        changed = runner.apply_mutation(copy, item)
        check(synthetic_source_path(base, item).read_bytes() == original,
              "source tree was mutated in place")
        check(changed.read_text().splitlines()[item.line - 1].strip() == item.after,
              "fixture edit was not applied")
        try:
            runner.apply_mutation(copy, item)
        except runner.CorpusError as exc:
            check("precondition rejected" in str(exc), "wrong repeat-edit error")
        else:
            raise AssertionError("already-mutated source accepted")
        bad = Path(tmp) / "bad"
        synthetic_source(bad, item, "drift")
        try:
            runner.apply_mutation(bad, item)
        except runner.CorpusError as exc:
            check("precondition rejected" in str(exc), "wrong drift error")
        else:
            raise AssertionError("drifted precondition accepted")


def synthetic_source_path(root: Path, item: runner.Round) -> Path:
    return root / Path(*Path(item.path).parts[1:])


def command(exit_code: int | None = 0, timed_out: bool = False) -> runner.CommandResult:
    return runner.CommandResult(["test"], "/tmp", exit_code, 0.0, timed_out, "/tmp/test.log")


def test_classification() -> None:
    valid = runner.round_by_number(1)
    equal = {"equal": True}
    different = {"equal": False}
    check(runner.classify(runner.round_by_number(2), equal, [], None, None, None)[0]
          == "invalid", "invalid classification")
    check(runner.classify(runner.round_by_number(6), equal, [], None, None, None)[0]
          == "equivalent", "equivalent classification")
    check(runner.classify(valid, different, ["Main.lean"], command(1), None, None)[0]
          == "extractor", "extractor classification")
    with tempfile.TemporaryDirectory() as tmp:
        log = Path(tmp) / "proof.log"
        log.write_text("error: ZiskFv/AirsClean/MainMirrorWeld.lean:1: mismatch\n")
        failed = command(1)
        failed.log = str(log)
        check(runner.classify(valid, different, ["Main.lean"], command(), command(), failed)[0]
              == "proof", "proof classification")
        log.write_text(
            "error: ZiskFv/AirsClean/MainMirrorWeld.lean:1: "
            "(deterministic) timeout at whnf, maximum number of heartbeats reached\n")
        check(runner.classify(valid, different, ["Main.lean"], command(), command(), failed)[0]
              == "infrastructure", "Lean heartbeat timeout counted as a proof kill")
    check(runner.classify(valid, different, ["Main.lean"], command(), command(), command())[0]
          == "fidelity", "fidelity classification")
    check(runner.classify(valid, different, ["Main.lean"], command(), command(),
                          command(None, True))[0] == "infrastructure", "timeout classification")
    check(runner.classify(valid, different, ["Main.lean"], command(), command(1),
                          command(1))[0] == "infrastructure", "baseline control classification")
    with tempfile.TemporaryDirectory() as tmp:
        log = Path(tmp) / "gate.log"
        rejected = command(1)
        rejected.log = str(log)
        log.write_text("byte-table mismatch: BinaryTable: block op=10 differs\n")
        check(runner.classify_fidelity_gate(command(), rejected)[0] == "fidelity_gate",
              "actual byte-table rejection not detected")
        check(runner.classify_fidelity_gate(command(), command())[0] == "fidelity",
              "successful proof/gate mislabeled as a caught mutation")
        for baseline, mutant in ((command(1), rejected),
                                 (command(), command(None, True)),
                                 (command(), command(2))):
            check(runner.classify_fidelity_gate(baseline, mutant)[0] == "infrastructure",
                  "failed baseline or timeout counted as fidelity detection")
        log.write_text("missing export\n")
        check(runner.classify_fidelity_gate(command(), rejected)[0] == "infrastructure",
              "unrelated gate error counted as fidelity detection")
        check(runner.classify_fidelity_gate(
            command(), rejected, "MemAlignRom mismatch:")[0] == "infrastructure",
              "unrelated ROM gate error counted as fidelity detection")
        log.write_text("MemAlignRom mismatch: physical row 3 differs\n")
        check(runner.classify_fidelity_gate(
            command(), rejected, "MemAlignRom mismatch:")[0] == "fidelity_gate",
              "actual ROM mismatch not detected")
        check(runner.classify_fidelity_gate(command(), rejected)[0] == "infrastructure",
              "wrong named gate counted as byte-table detection")
    check(not runner.meets_expected({"proof_skipped": True, "outcome": "fidelity",
                                     "expected_detection_layer": "fidelity_gate"}),
          "skipped proof/gate claimed the byte-table detection requirement")

    outcome, _, control = runner.classify_equivalent_control(
        command(), "fidelity", "mutant proof passed")
    check(outcome == "equivalent" and control["proof_green"],
          "green equivalent control classification")
    for failed in (command(None, True), command(2), command(-15)):
        outcome, _, control = runner.classify_equivalent_control(
            failed, "infrastructure", "abnormal proof command")
        check(outcome == "infrastructure" and not control["proof_green"]
              and not control["proof_false_positive"],
              "equivalent control hid an infrastructure failure")
    outcome, _, control = runner.classify_equivalent_control(
        command(1), "infrastructure", "unrelated diagnostic")
    check(outcome == "infrastructure" and not control["proof_false_positive"],
          "unrelated equivalent-control failure counted as a false positive")
    outcome, _, control = runner.classify_equivalent_control(
        command(1), "proof", "matched proof boundary")
    check(outcome == "equivalent" and control["proof_false_positive"],
          "matched equivalent-control false positive was lost")


def test_artifact_and_semantic_baselines() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        a, b = Path(tmp) / "a", Path(tmp) / "b"
        a.mkdir(); b.mkdir()
        (a / "x").write_text("same")
        (b / "x").write_text("same")
        check(runner.artifact_delta(a, b) == [], "identical artifacts differ")
        (b / "x").write_text("changed")
        check(runner.artifact_delta(a, b) == ["x"], "artifact delta absent")
    pilout = runner.REPO / "build/zisk.pilout"
    if pilout.is_file():
        comparison = semdiff.compare(pilout, pilout)
        check(comparison["equal"], "pilout self-comparison")
        check(comparison["airs"] and all(not item["changed"]
              for item in comparison["airs"].values()), "per-AIR changed-index baseline")
    else:
        print("SKIP pilout semantic baseline: build/zisk.pilout absent")


def test_site_operators() -> None:
    source = runner.REPO / "zisk"
    values = sites.enumerate_sites(str(source))
    counts = Counter(value["op"] for value in values)
    check(counts["BUS_ID_SWAP"] == 44, "bus-id site count")
    check(counts["SELECTOR_ARG"] == 29, "selector-argument site count")
    check(counts["MULTIPLICITY"] == 2, "multiplicity site count")
    check(counts["AIRVAL"] == 23, "air-value site count")
    check(not any("bits(" in value["old"] for value in values
                  if value["op"] == "CONST_PERTURB"),
          "bits declaration admitted as a constrained constant mutation")


def test_round_zero_control() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        left, right = root / "left", root / "right"
        left.mkdir(); right.mkdir()
        (left / "Same.lean").write_text("same")
        (right / "Same.lean").write_text("same")
        with mock.patch.object(runner.semdiff, "compare", return_value={"equal": True}):
            value = runner.round_zero_summary(root / "base", root / "compiled", left, right)
        check(value["passed"] and value["extraction_byte_delta"] == [],
              "byte-identical round zero rejected")
        (right / "Same.lean").write_text("changed")
        with mock.patch.object(runner.semdiff, "compare", return_value={"equal": True}):
            value = runner.round_zero_summary(root / "base", root / "compiled", left, right)
        check(not value["passed"] and value["extraction_byte_delta"] == ["Same.lean"],
              "round-zero extraction drift accepted")
    check(runner.meets_expected({"proof_skipped": True, "outcome": "fidelity",
                                 "expected_detection_layer": "proof"}),
          "explicitly skipped proof rejected at the artifact boundary")
    check(not runner.meets_expected({"proof_skipped": True, "outcome": "proof",
                                     "expected_detection_layer": "proof"}),
          "proof-skipped result claimed a proof detection")


def test_log_archive() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        logs = root / "work-logs"
        logs.mkdir()
        local = logs / "local.log"
        external = root / "baseline.log"
        local.write_text("local")
        external.write_text("baseline")
        result = {"commands": [{"log": str(local)}, {"log": str(external)}],
                  "workspace": str(root)}
        archive = root / "archive"
        runner.archive_logs(result, logs, archive)
        check(result["commands"] == [{"log": "logs/local.log"},
                                     {"log": "logs/baseline.log"}],
              "archived log paths are not portable")
        check((archive / "logs/baseline.log").read_text() == "baseline",
              "external baseline log was not archived")


def test_private_dependency_copy() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source, destination = root / "source", root / "destination"
        (source / ".lake").mkdir(parents=True)
        original = source / ".lake/cache"
        original.write_text("baseline")
        runner.copy_tree_cow(source, destination)
        (destination / ".lake/cache").write_text("mutant")
        check(original.read_text() == "baseline", "dependency cache write escaped private copy")


def test_readonly_artifact_restore() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        repo = root / "repo"
        proof = root / "proof"
        extraction = root / "nix-extraction"
        (repo / "build/extraction").mkdir(parents=True)
        (repo / "build/extraction/lakefile.toml").write_text("package Extraction\n")
        (proof / "build/extraction/Extraction/nested").mkdir(parents=True)
        (proof / "build/extraction/Extraction/nested/old.lean").write_text("old")
        (proof / "build/zisk.pilout").write_text("old")
        (extraction / "Extraction/nested").mkdir(parents=True)
        (extraction / "Extraction/nested/New.lean").write_text("new")
        (extraction / "ByteTables").mkdir()
        (extraction / "ByteTables/BinaryTable.json").write_text("digest")
        pilout = root / "new.pilout"
        pilout.write_text("new")
        for tree in (proof / "build/extraction", extraction, extraction / "Extraction",
                     extraction / "Extraction/nested"):
            tree.chmod(0o555)
        (proof / "build/zisk.pilout").chmod(0o444)
        (extraction / "Extraction/nested/New.lean").chmod(0o444)
        runner.install_proof_artifacts(repo, proof, pilout, extraction)
        check((proof / "build/extraction/Extraction/nested/New.lean").read_text() == "new",
              "read-only extraction was not restored")
        check((proof / "build/zisk.pilout").read_text() == "new",
              "read-only pilout was not replaced")
        check((proof / "build/extraction/ByteTables/BinaryTable.json").read_text() == "digest",
              "byte-table fidelity input was not installed")
        flat = root / "flat-output"
        flat.mkdir()
        (flat / "New.lean").write_text("new")
        shutil.copytree(extraction / "ByteTables", flat / "ByteTables")
        runner.install_proof_artifacts(repo, proof, pilout, flat)
        check((proof / "build/extraction/ByteTables/BinaryTable.json").read_text() == "digest",
              "flat Nix byte-table input was not installed")
        (flat / "ByteTables/BinaryTable.json").write_text("mutated")
        check("ByteTables/BinaryTable.json" in runner.extraction_delta(extraction, flat),
              "flat Nix byte-table mutation was not monitored")


def test_component_and_byte_table_manifest() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        baseline, mutant = root / "baseline", root / "mutant"
        component = Path("Components/BinaryAdd/Constraints.lean")
        table = Path("ByteTables/BinaryTable.json")
        for tree in (baseline, mutant):
            for relative in (component, table):
                target = tree / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("same")
        check(set(runner.extraction_manifest(baseline)) == {str(component), str(table)},
              "integrated manifest dropped a nested component or byte table")
        (mutant / component).write_text("changed")
        check(runner.extraction_delta(baseline, mutant) == [str(component)],
              "component-only mutation disappeared from recursive accounting")
        (mutant / table).write_text("changed")
        check(runner.extraction_delta(baseline, mutant) == [str(table), str(component)],
              "component and byte-table deltas did not coexist")


def test_byte_table_gate_order() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        calls = []

        def gate(argv, cwd, timeout, log):
            calls.append(argv[-1])
            log.write_text("byte-table mismatch: BinaryTable: block op=10 differs\n"
                           if len(calls) == 2 else "byte tables match\n")
            value = command(1 if len(calls) == 2 else 0)
            value.log = str(log)
            return value

        result = {"commands": []}
        with mock.patch.object(runner, "run_command", side_effect=gate):
            outcome, _ = runner.table_fidelity_controls(
                root, root / "clean", root / "mutant", 900, root, result)
        check(calls == [str(root / "clean/ByteTables"), str(root / "mutant/ByteTables")],
              "mutant fidelity gate ran before its clean control")
        check(outcome == "fidelity_gate" and result["proof_status"] == "not_run"
              and "proof_skipped" not in result,
              "actual fidelity detection misrepresented a proof result")
        with mock.patch.object(runner, "run_command", return_value=command(1)):
            result = {"commands": []}
            outcome, _ = runner.table_fidelity_controls(
                root, root / "clean", root / "mutant", 900, root, result)
        check(outcome == "infrastructure" and len(result["commands"]) == 1,
              "failed clean gate admitted a mutant detection")
        calls.clear()
        def rom_gate(argv, cwd, timeout, log):
            calls.append(argv)
            log.write_text("MemAlignRom mismatch: physical row 3 differs\n"
                           if len(calls) == 2 else "MemAlignRom matches\n")
            value = command(1 if len(calls) == 2 else 0)
            value.log = str(log)
            return value
        result = {"commands": []}
        with mock.patch.object(runner, "run_command", side_effect=rom_gate):
            outcome, _ = runner.table_fidelity_controls(
                root, root / "clean", root / "mutant", 900, root, result, "MemAlignRom")
        check([argv[-1] for argv in calls] ==
              [str(root / "clean/MemAlignRom.tsv"), str(root / "mutant/MemAlignRom.tsv")],
              "ROM controls did not use clean then mutant production rows")
        check(all(argv[-2] == "--export-tsv" for argv in calls)
              and outcome == "fidelity_gate" and result["proof_status"] == "not_run"
              and result["fidelity_gate"]["name"] == "MemAlignRom",
              "ROM fidelity detection did not run the named gate")
    # Freeze the early gate's ordering relative to the existing full-proof path.
    tree = ast.parse((HERE / "runner.py").read_text())
    full = next(node for node in tree.body if isinstance(node, ast.FunctionDef)
                and node.name == "full")
    gate_line = next(node.lineno for node in ast.walk(full)
                     if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                     and node.func.id == "table_fidelity_controls")
    proof_line = next(node.lineno for node in ast.walk(full)
                      if isinstance(node, ast.Assign)
                      and any(isinstance(target, ast.Name) and target.id == "baseline_proof"
                              for target in node.targets))
    check(gate_line < proof_line, "fidelity gate regressed behind the full proof build")


def test_relative_repo_evidence_archive() -> None:
    corpus = runner.load_corpus()
    for repo_path in (".", str(runner.REPO)):
        with tempfile.TemporaryDirectory(dir=runner.REPO) as tmp:
            root = Path(tmp)
            def completed(args):
                check(args.repo == runner.REPO, "command boundary did not normalize --repo")
                args._archive_dir.mkdir(parents=True)
                return {"round": 50, "outcome": "fidelity_gate", "complete": True,
                        "expected_detection_layer": "fidelity_gate", "proof_status": "not_run"}
            with ExitStack() as patches:
                patches.enter_context(mock.patch.object(runner, "HERE", root))
                patches.enter_context(mock.patch.object(runner, "load_corpus", return_value=corpus))
                patches.enter_context(mock.patch.object(runner, "full", side_effect=completed))
                patches.enter_context(mock.patch.object(runner, "repository_identity", return_value={}))
                patches.enter_context(mock.patch.object(
                    runner.subprocess, "run", return_value=mock.Mock(stdout="a" * 40)))
                status = runner.main([
                    "suite", "--repo", repo_path, "--zisk-source", str(root),
                    "--profile", "regression", "--round", "50",
                    "--work-root", str(root / "work"), "--results-dir", str(root / "results"),
                    "--commit-evidence", "aaaaaaaa"])
            check(status == 0 and (root / "results/summary.json").is_file(),
                  "repository path broke completed evidence archival")


def main() -> int:
    tests = [test_corpus, test_isolation_and_precondition, test_classification,
             test_artifact_and_semantic_baselines, test_site_operators,
             test_round_zero_control, test_log_archive,
             test_private_dependency_copy, test_readonly_artifact_restore,
             test_byte_table_gate_order, test_component_and_byte_table_manifest,
             test_relative_repo_evidence_archive]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
