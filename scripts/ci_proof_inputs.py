#!/usr/bin/env python3
"""Classify proof inputs without workflow-level path filters hiding required checks."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess


def classify(paths: list[str], event: str) -> dict:
    force = event in {"schedule", "workflow_dispatch"}
    proof_roots = ("tools/", "scripts/", "nix/", "trust/", ".github/", "zisk/")
    proof_files = {
        "flake.nix", "flake.lock", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "zisk", ".gitmodules", ".gitignore", ".rgignore", "AGENTS.md",
    }
    release_roots = ("tools/pil-extract/", "tools/virtual-tables/", "tools/adversarial-mutations/")
    release_files = {
        "flake.lock", "flake.nix", "zisk", ".gitmodules", "nix/zisk-pilout.nix",
        "nix/pil2-compiler.nix", "nix/extracted-lean.nix", "nix/pil-extract.nix",
    }
    matched = sorted({path for path in paths if path.endswith(".lean")
                      or path in proof_files or path.startswith(proof_roots)})
    release = sorted({path for path in paths if path in release_files
                      or path.startswith(release_roots) or path.startswith("zisk/")})
    return {"run_proofs": force or bool(matched), "run_mutations": force or bool(release),
            "matched": matched, "release_inputs": release,
            "reason": "scheduled/manual validation" if force else
                "proof inputs changed" if matched else "no proof inputs changed"}


def changed_paths(event: str, payload: dict, head: str) -> list[str]:
    if event in {"schedule", "workflow_dispatch"}:
        return []
    if event == "pull_request":
        base = payload["pull_request"]["base"]["sha"]
    elif event == "merge_group":
        base = payload["merge_group"]["base_sha"]
    elif event == "push":
        base = payload["before"]
    else:
        raise ValueError(f"unsupported event: {event}")
    if not all(re.fullmatch(r"[0-9a-f]{40}", ref) for ref in (head, base)):
        raise ValueError("expected full Git commit IDs")
    if base == "0" * 40:
        command = ["git", "ls-tree", "-r", "--name-only", "-z", head]
    else:
        command = ["git", "diff", "--name-only", "-z", base, head, "--"]
    return [path for path in subprocess.check_output(command).decode().split("\0") if path]


def aggregate_ok(needs: dict) -> bool:
    if needs.get("proof-inputs", {}).get("result") != "success":
        return False
    if needs.get("fast-checks", {}).get("result") != "success":
        return False
    outputs = needs["proof-inputs"].get("outputs", {})
    if outputs.get("run_proofs") not in {"true", "false"}:
        return False
    required = outputs["run_proofs"] == "true"
    for job in ("pick-runner", "lake-build", "aeneas-extraction-diff", "aeneas-production-extraction"):
        if needs.get(job, {}).get("result") != ("success" if required else "skipped"):
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--aggregate", action="store_true")
    args = parser.parse_args()
    if args.aggregate:
        if not aggregate_ok(json.loads(os.environ["PROOF_JOB_RESULTS"])):
            raise SystemExit("required proof jobs did not complete successfully")
        print("required proof checks passed")
        return
    event = os.environ["GITHUB_EVENT_NAME"]
    payload = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    result = classify(changed_paths(event, payload, os.environ["GITHUB_SHA"]), event)
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        for key in ("run_proofs", "run_mutations"):
            output.write(f"{key}={str(result[key]).lower()}\n")
        output.write(f"reason={result['reason']}\n")
    print(json.dumps(result, indent=2))
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(summary, "a") as output:
            output.write("Proof input classification:\n\n```json\n")
            output.write(json.dumps(result, indent=2) + "\n```\n")


if __name__ == "__main__":
    main()
