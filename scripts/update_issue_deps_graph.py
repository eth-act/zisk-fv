#!/usr/bin/env python3
"""Render or update the canonical GitHub issue dependency graph.

The graph is generated from GitHub issue metadata only:

* node classes come from issue labels/state
* dependency edges come from structured blockedBy/blocking relationships
* parent/sub-issue data is rendered as a separate list, not dependency edges

The generated Mermaid graph is meant to live in one canonical GitHub issue body,
so updating it does not create commits or trigger push/PR CI.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import sys
import textwrap
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from typing import Any


DEFAULT_OWNER = "eth-act"
DEFAULT_REPO = "zisk-fv"
DEFAULT_TITLE = "Issue dependency graph"
GRAPHQL_URL = "https://api.github.com/graphql"
REST_URL = "https://api.github.com"


@dataclass
class Issue:
    number: int
    title: str
    state: str
    url: str
    labels: set[str] = field(default_factory=set)
    blocked_by: set[int] = field(default_factory=set)
    blocking: set[int] = field(default_factory=set)
    parent: int | None = None
    sub_issues: set[int] = field(default_factory=set)


class GitHubClient:
    def __init__(self, token: str | None) -> None:
        self.token = token

    def _headers(self) -> dict[str, str]:
        headers = {
            "Accept": "application/vnd.github+json",
            "Content-Type": "application/json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "zisk-fv-issue-deps-graph",
        }
        if self.token:
            headers["Authorization"] = f"Bearer {self.token}"
        return headers

    def graphql(self, query: str, variables: dict[str, Any]) -> dict[str, Any]:
        payload = json.dumps({"query": query, "variables": variables}).encode()
        req = urllib.request.Request(
            GRAPHQL_URL, data=payload, headers=self._headers(), method="POST"
        )
        try:
            with urllib.request.urlopen(req) as resp:
                data = json.loads(resp.read().decode())
        except urllib.error.HTTPError as err:
            body = err.read().decode(errors="replace")
            raise RuntimeError(f"GitHub GraphQL request failed: {err.code}: {body}") from err
        if data.get("errors"):
            raise RuntimeError(f"GitHub GraphQL errors: {json.dumps(data['errors'])}")
        return data["data"]

    def rest(self, method: str, path: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
        data = None if payload is None else json.dumps(payload).encode()
        req = urllib.request.Request(
            f"{REST_URL}{path}", data=data, headers=self._headers(), method=method
        )
        try:
            with urllib.request.urlopen(req) as resp:
                if resp.status == 204:
                    return {}
                return json.loads(resp.read().decode())
        except urllib.error.HTTPError as err:
            body = err.read().decode(errors="replace")
            raise RuntimeError(f"GitHub REST request failed: {method} {path}: {err.code}: {body}") from err


ISSUES_QUERY = """
query($owner: String!, $repo: String!, $after: String) {
  repository(owner: $owner, name: $repo) {
    issues(first: 100, after: $after, states: [OPEN, CLOSED], orderBy: {field: CREATED_AT, direction: ASC}) {
      nodes {
        number
        title
        state
        url
        labels(first: 50) { nodes { name } }
        blockedBy(first: 100) {
          nodes { number }
        }
        blocking(first: 100) {
          nodes { number }
        }
        parent { number }
        subIssues(first: 100) {
          nodes { number }
        }
      }
      pageInfo { hasNextPage endCursor }
    }
  }
}
"""


def labels_of(raw: dict[str, Any] | None) -> set[str]:
    if not raw:
        return set()
    return {node["name"] for node in raw.get("nodes", [])}


def merge_issue(issues: dict[int, Issue], raw: dict[str, Any]) -> Issue:
    number = int(raw["number"])
    issue = issues.get(number)
    if issue is None:
        issue = Issue(
            number=number,
            title=raw["title"],
            state=raw["state"],
            url=raw["url"],
            labels=labels_of(raw.get("labels")),
        )
        issues[number] = issue
    else:
        issue.title = raw["title"]
        issue.state = raw["state"]
        issue.url = raw["url"]
        issue.labels |= labels_of(raw.get("labels"))
    return issue


def fetch_issues(client: GitHubClient, owner: str, repo: str) -> dict[int, Issue]:
    issues: dict[int, Issue] = {}
    after = None
    while True:
        data = client.graphql(ISSUES_QUERY, {"owner": owner, "repo": repo, "after": after})
        conn = data["repository"]["issues"]
        for raw in conn["nodes"]:
            issue = merge_issue(issues, raw)

            for blocker_raw in raw["blockedBy"]["nodes"]:
                issue.blocked_by.add(int(blocker_raw["number"]))

            for blocked_raw in raw["blocking"]["nodes"]:
                blocked_number = int(blocked_raw["number"])
                issue.blocking.add(blocked_number)
                if blocked_number in issues:
                    issues[blocked_number].blocked_by.add(issue.number)

            if raw.get("parent"):
                parent_number = int(raw["parent"]["number"])
                issue.parent = parent_number
                if parent_number in issues:
                    issues[parent_number].sub_issues.add(issue.number)

            for sub_raw in raw["subIssues"]["nodes"]:
                sub_number = int(sub_raw["number"])
                issue.sub_issues.add(sub_number)
                if sub_number in issues:
                    issues[sub_number].parent = issue.number

        page_info = conn["pageInfo"]
        if not page_info["hasNextPage"]:
            return issues
        after = page_info["endCursor"]


def classify(issue: Issue) -> str:
    if issue.state == "CLOSED":
        return "done"
    has_soundness = "soundness" in issue.labels
    has_completeness = "completeness" in issue.labels
    if has_soundness and has_completeness:
        return "both"
    if has_soundness:
        return "soundness"
    if has_completeness:
        return "completeness"
    return "neither"


def short_title(title: str, width: int = 56) -> str:
    one_line = " ".join(title.split())
    return textwrap.shorten(one_line, width=width, placeholder="...")


def mermaid_label(issue: Issue) -> str:
    title = html.escape(short_title(issue.title), quote=True)
    return f"#{issue.number}<br/>{title}"


def render_mermaid(issues: dict[int, Issue], graph_issue_number: int | None) -> tuple[str, list[tuple[int, int]], set[int]]:
    edges: set[tuple[int, int]] = set()
    for issue in issues.values():
        if graph_issue_number and issue.number == graph_issue_number:
            continue
        for blocker in issue.blocked_by:
            if graph_issue_number and blocker == graph_issue_number:
                continue
            edges.add((issue.number, blocker))
        for blocked in issue.blocking:
            if graph_issue_number and blocked == graph_issue_number:
                continue
            edges.add((blocked, issue.number))

    included = {
        issue.number
        for issue in issues.values()
        if issue.state == "OPEN" and issue.number != graph_issue_number
    }
    for blocked, blocker in edges:
        included.add(blocked)
        included.add(blocker)

    lines = [
        "```mermaid",
        "%%{init: {'themeVariables': { 'fontSize': '18px' }}}%%",
        "flowchart TD",
        "    classDef soundness fill:#3b82f6,stroke:#1d4ed8,color:#fff,font-weight:bold",
        "    classDef completeness fill:#9ca3af,stroke:#6b7280,color:#fff,font-weight:bold",
        "    classDef both fill:#ef4444,stroke:#b91c1c,color:#fff,font-weight:bold",
        "    classDef neither fill:#22c55e,stroke:#16a34a,color:#fff,font-weight:bold",
        "    classDef done fill:#000000,stroke:#000000,color:#fff,font-weight:bold",
        "",
    ]

    for number in sorted(included):
        issue = issues[number]
        lines.append(f'    I{number}["{mermaid_label(issue)}"]:::{classify(issue)}')

    if edges:
        lines.append("")
        by_blocked: dict[int, list[int]] = {}
        for blocked, blocker in sorted(edges):
            if blocked in included and blocker in included:
                by_blocked.setdefault(blocked, []).append(blocker)
        for blocked in sorted(by_blocked):
            blockers = " & ".join(f"I{n}" for n in sorted(set(by_blocked[blocked])))
            lines.append(f"    I{blocked} --> {blockers}")

    lines.append("```")
    return "\n".join(lines), sorted(edges), included


def render_subissues(issues: dict[int, Issue], included: set[int], graph_issue_number: int | None) -> str:
    rows: list[str] = []
    for number in sorted(included):
        if graph_issue_number and number == graph_issue_number:
            continue
        subs = sorted(
            sub
            for sub in issues[number].sub_issues
            if sub in issues and sub != graph_issue_number
        )
        if subs:
            rendered = ", ".join(f"#{sub}" for sub in subs)
            rows.append(f"- #{number} has sub-issues {rendered}.")
    if not rows:
        return "No included issues currently have structured sub-issues."
    return "\n".join(rows)


def render_issue_table(issues: dict[int, Issue], included: set[int]) -> str:
    rows = ["| Issue | State | Labels | Title |", "| --- | --- | --- | --- |"]
    for number in sorted(included):
        issue = issues[number]
        labels = ", ".join(sorted(issue.labels)) or "-"
        title = html.escape(issue.title)
        rows.append(f"| [#{number}]({issue.url}) | {issue.state.lower()} | {labels} | {title} |")
    return "\n".join(rows)


def render_body(
    owner: str,
    repo: str,
    issues: dict[int, Issue],
    graph_issue_number: int | None,
) -> str:
    mermaid, edges, included = render_mermaid(issues, graph_issue_number)
    body = f"""<!-- generated by scripts/update_issue_deps_graph.py; do not edit manually -->
# Issue Dependency Graph

This issue body is the canonical visual dependency graph for `{owner}/{repo}`.
It is generated from GitHub issue metadata, not from hand-maintained prose:

- node colors come from issue state plus the `soundness` / `completeness` labels
- solid arrows come from structured `blockedBy` / `blocking` issue relationships
- `A --> B` means issue `A` is blocked by issue `B`
- parent/sub-issue relationships are listed below, not drawn as dependency edges

{mermaid}

## Structured Sub-Issues

{render_subissues(issues, included, graph_issue_number)}

## Included Issues

{render_issue_table(issues, included)}

## Generation

- Included nodes: {len(included)}
- Dependency edges: {len(edges)}
- Regenerate with: `python3 scripts/update_issue_deps_graph.py --owner {owner} --repo {repo} --issue-title "{DEFAULT_TITLE}" --update`
"""
    return body.rstrip() + "\n"


def find_graph_issue(issues: dict[int, Issue], title: str) -> Issue | None:
    matches = [issue for issue in issues.values() if issue.title == title]
    if not matches:
        return None
    open_matches = [issue for issue in matches if issue.state == "OPEN"]
    return sorted(open_matches or matches, key=lambda issue: issue.number)[0]


def get_issue_body(client: GitHubClient, owner: str, repo: str, number: int) -> str:
    issue = client.rest("GET", f"/repos/{owner}/{repo}/issues/{number}")
    return issue.get("body") or ""


def create_issue(client: GitHubClient, owner: str, repo: str, title: str, body: str) -> int:
    issue = client.rest(
        "POST",
        f"/repos/{owner}/{repo}/issues",
        {"title": title, "body": body, "labels": ["documentation"]},
    )
    return int(issue["number"])


def update_issue(client: GitHubClient, owner: str, repo: str, number: int, body: str) -> None:
    client.rest("PATCH", f"/repos/{owner}/{repo}/issues/{number}", {"body": body})


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--owner", default=os.environ.get("GITHUB_REPOSITORY_OWNER", DEFAULT_OWNER))
    parser.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", f"{DEFAULT_OWNER}/{DEFAULT_REPO}").split("/")[-1])
    parser.add_argument("--issue-title", default=DEFAULT_TITLE)
    parser.add_argument("--token", default=os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN"))
    parser.add_argument("--output", help="Write generated Markdown to this file instead of stdout.")
    parser.add_argument("--update", action="store_true", help="Create/update the canonical GitHub issue body.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    client = GitHubClient(args.token)
    issues = fetch_issues(client, args.owner, args.repo)
    graph_issue = find_graph_issue(issues, args.issue_title)
    graph_number = graph_issue.number if graph_issue else None
    body = render_body(args.owner, args.repo, issues, graph_number)

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(body)
    elif not args.update:
        sys.stdout.write(body)

    if not args.update:
        return 0
    if not args.token:
        raise RuntimeError("--update requires GH_TOKEN or GITHUB_TOKEN")

    if graph_number is None:
        graph_number = create_issue(client, args.owner, args.repo, args.issue_title, body)
        # Regenerate once so the newly created container issue excludes itself.
        issues = fetch_issues(client, args.owner, args.repo)
        body = render_body(args.owner, args.repo, issues, graph_number)

    current = get_issue_body(client, args.owner, args.repo, graph_number)
    if current == body:
        print(f"Issue #{graph_number} is already up to date.")
        return 0
    update_issue(client, args.owner, args.repo, graph_number, body)
    print(f"Updated issue #{graph_number}: https://github.com/{args.owner}/{args.repo}/issues/{graph_number}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
