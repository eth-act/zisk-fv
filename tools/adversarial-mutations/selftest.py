#!/usr/bin/env python3
"""Fast, standard-library-only self-tests for corpus mechanics."""

from __future__ import annotations

import shutil
import sys
import tempfile
from collections import Counter
from pathlib import Path
from unittest import mock

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
    check(len(rounds) == 52, "round count")
    check(sum(r.historical_class == "VALID" for r in rounds) == 35, "valid count")
    check(sum(r.expected_outcome == "proof" for r in rounds) == 24, "caught count")
    check(sum(r.expected_outcome == "fidelity" for r in rounds) == 11, "missed count")
    check(runner.expected_detection_layer(runner.round_by_number(27)) == "proof",
          "round 27 is caught after Main c41 is tied")
    check(runner.expected_detection_layer(runner.round_by_number(50)) == "proof",
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


def main() -> int:
    tests = [test_corpus, test_isolation_and_precondition, test_classification,
             test_artifact_and_semantic_baselines, test_site_operators,
             test_round_zero_control, test_log_archive,
             test_private_dependency_copy, test_readonly_artifact_restore]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
