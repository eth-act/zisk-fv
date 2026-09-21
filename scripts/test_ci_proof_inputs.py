#!/usr/bin/env python3
import unittest
from unittest.mock import patch

from ci_proof_inputs import aggregate_ok, changed_paths, classify


class ProofInputsTests(unittest.TestCase):
    def test_gate_implementations_and_policy_are_inputs(self):
        for path in ["tools/pilout-roundtrip/poly.py", "tools/mirror-roundtrip/acceptance.py",
                     "tools/virtual-tables/check.py", "trust/weld-airs.toml",
                     "trust/trusted-base.md", "scripts/ci_proof_inputs.py",
                     ".github/workflows/proofs.yml", "ZiskFv/Soundness.lean", "lean-toolchain"]:
            with self.subTest(path=path):
                self.assertTrue(classify([path], "pull_request")["run_proofs"])

    def test_docs_skip_but_scheduled_proof_runs_do_not(self):
        self.assertFalse(classify(["README.md"], "push")["run_proofs"])
        for event in ["schedule", "workflow_dispatch"]:
            self.assertTrue(classify([], event)["run_proofs"])

    def test_pr_compares_base_to_actual_tested_merge(self):
        with patch("ci_proof_inputs.subprocess.check_output", return_value=b"a b.lean\0") as run:
            self.assertEqual(changed_paths("pull_request", {"pull_request": {
                "base": {"sha": "a" * 40}}}, "b" * 40), ["a b.lean"])
            self.assertEqual(run.call_args.args[0],
                             ["git", "diff", "--name-only", "-z", "a" * 40, "b" * 40, "--"])

    def test_initial_push_lists_all_files(self):
        with patch("ci_proof_inputs.subprocess.check_output", return_value=b"flake.lock\0") as run:
            changed_paths("push", {"before": "0" * 40}, "b" * 40)
            self.assertEqual(run.call_args.args[0][1], "ls-tree")

    def test_unknown_event_and_invalid_commit_fail(self):
        with self.assertRaises(ValueError):
            changed_paths("unknown", {}, "b" * 40)
        with self.assertRaises(ValueError):
            changed_paths("push", {"before": "--help"}, "b" * 40)

    def test_aggregate_rejects_missing_failed_cancelled_and_skipped_required_jobs(self):
        needs = {name: {"result": "success"} for name in [
            "proof-inputs", "fast-checks", "pick-runner", "lake-build",
            "aeneas-extraction-diff", "aeneas-production-extraction"]}
        needs["proof-inputs"]["outputs"] = {"run_proofs": "true"}
        self.assertTrue(aggregate_ok(needs))
        for name in needs:
            for result in ["failure", "cancelled", "skipped"]:
                with self.subTest(name=name, result=result):
                    altered = {**needs, name: {**needs[name], "result": result}}
                    self.assertFalse(aggregate_ok(altered))
            self.assertFalse(aggregate_ok({key: value for key, value in needs.items() if key != name}))

    def test_aggregate_allows_only_intentional_skips(self):
        needs = {name: {"result": "skipped"} for name in [
            "pick-runner", "lake-build", "aeneas-extraction-diff", "aeneas-production-extraction"]}
        needs.update({"proof-inputs": {"result": "success", "outputs": {"run_proofs": "false"}},
                      "fast-checks": {"result": "success"}})
        self.assertTrue(aggregate_ok(needs))
        needs["lake-build"]["result"] = "cancelled"
        self.assertFalse(aggregate_ok(needs))


if __name__ == "__main__":
    unittest.main()
