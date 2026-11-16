#!/usr/bin/env python3
"""Exercise only the real filesystem-preservation helper, never native capture.

Synthetic launch records are explicitly not native-invocation evidence. The
published historical fixture is read/hash-checked only, not re-finalized or
rewritten. No producer, compiler, cache, source archive or tool probe is run.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    fixture = directory / "fixtures/minimal-return"

    def fixture_hashes():
        return {str(path.relative_to(fixture)): digest(path.read_bytes())
                for path in sorted(fixture.rglob("*")) if path.is_file()}

    before = fixture_hashes()
    spec = importlib.util.spec_from_file_location("capture_provenance_check", directory / "capture.py")
    capture = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capture)
    results = []
    with tempfile.TemporaryDirectory(prefix="finite-return-continuation-") as temporary:
        root = Path(temporary)
        original_source = b"# synthetic initial snapshot; never executed\n"
        initial_record = {
            "status": "SYNTHETIC_FILESYSTEM_REGRESSION_NOT_NATIVE_EXECUTION",
            "native_orchestrator_sha256": digest(original_source),
            "native_orchestrator_snapshot_file": "native-orchestrator.py",
            "native_process_environment": {"status": "UNOBSERVED", "values": None},
            "native_invocation": {"argv": ["synthetic-not-executed"]},
            "finalizer_source_sha256": digest(b"distinct synthetic finalizer, not native source"),
        }
        good = root / "matching-snapshot"
        good.mkdir()
        (good / "native-orchestrator.py").write_bytes(original_source)
        (good / "native-launch-evidence.json").write_text(json.dumps(initial_record) + "\n")
        capture.preserve_initial_native_evidence(good)
        # Reproduce the later launch overwriting the original pathname without
        # invoking any process. The initial JSON must still resolve OLD bytes.
        (good / "native-orchestrator.py").write_bytes(b"# synthetic later snapshot; never executed\n")
        (good / "native-launch-evidence.json").write_text('{"status":"synthetic later launch"}\n')
        preserved = json.loads((good / "native-launch-evidence-initial.json").read_text())
        expected = {**initial_record, "native_orchestrator_snapshot_file": "native-orchestrator-initial.py"}
        assert preserved == expected, "Only the initial snapshot pathname may change"
        assert digest((good / preserved["native_orchestrator_snapshot_file"]).read_bytes()) == preserved["native_orchestrator_sha256"]
        assert preserved["native_orchestrator_sha256"] != digest((good / "native-orchestrator.py").read_bytes())
        results.append({"case": "initial-link-survives-later-path-overwrite", "passed": True})

        bad = root / "mismatching-snapshot"
        bad.mkdir()
        bad_record = {**initial_record, "native_orchestrator_sha256": digest(b"different source")}
        bad_json = json.dumps(bad_record) + "\n"
        (bad / "native-orchestrator.py").write_bytes(original_source)
        (bad / "native-launch-evidence.json").write_text(bad_json)
        try:
            capture.preserve_initial_native_evidence(bad)
        except ValueError as error:
            assert "does not match its recorded hash" in str(error)
        else:
            raise AssertionError("A mismatching snapshot must not authorize a provenance-link rewrite")
        assert (bad / "native-launch-evidence-initial.json").read_text() == bad_json
        assert (bad / "native-orchestrator-initial.py").read_bytes() == original_source
        results.append({"case": "hash-mismatch-rejected-before-evidence-rewrite", "passed": True})

        legacy = root / "historical-unobserved"
        legacy.mkdir()
        historical_bytes = (fixture / "native-launch-evidence.json").read_bytes()
        (legacy / "native-launch-evidence.json").write_bytes(historical_bytes)
        capture.preserve_initial_native_evidence(legacy)
        assert (legacy / "native-launch-evidence-initial.json").read_bytes() == historical_bytes
        historical = json.loads(historical_bytes)
        assert historical["native_orchestrator_sha256"] is None
        assert historical["native_orchestrator_snapshot_file"] is None
        assert historical["native_process_environment"] == {"status": "UNOBSERVED", "values": None}
        assert not (legacy / "native-orchestrator-initial.py").exists()
        results.append({"case": "actual-historical-null-provenance-not-invented", "passed": True})

    after = fixture_hashes()
    assert before == after, "Historical native/finalizer fixture bytes changed"
    report = {
        "native_execution": False,
        "refinalization_or_archive_regeneration": False,
        "cases": results,
        "actual_fixture_files_preserved_byte_for_byte": before,
        "future_capture_source_sha256": digest((directory / "capture.py").read_bytes()),
        "historical_provenance_scope": "Existing ac09 launch and finalizer records remain unchanged; new code is not relabeled as their invocation",
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases_passed": len(results), "historical_files_unchanged": len(before),
                      "native_execution": False, "report": str(args.report)}))


if __name__ == "__main__":
    main()
