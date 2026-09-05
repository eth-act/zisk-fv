#!/usr/bin/env python3
"""Fast, standard-library-only self-tests for corpus mechanics."""

from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import runner  # noqa: E402
import semdiff  # noqa: E402


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
    check(runner.expected_detection_layer(runner.round_by_number(27)) == "fidelity",
          "recorded scope boundary")
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
    check(runner.classify(valid, different, ["Main.lean"], command(), command(), command())[0]
          == "fidelity", "fidelity classification")
    check(runner.classify(valid, different, ["Main.lean"], command(), command(),
                          command(None, True))[0] == "infrastructure", "timeout classification")
    check(runner.classify(valid, different, ["Main.lean"], command(), command(1),
                          command(1))[0] == "infrastructure", "baseline control classification")


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
        check(semdiff.compare(pilout, pilout)["equal"], "pilout self-comparison")
    else:
        print("SKIP pilout semantic baseline: build/zisk.pilout absent")


def main() -> int:
    tests = [test_corpus, test_isolation_and_precondition, test_classification,
             test_artifact_and_semantic_baselines]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
