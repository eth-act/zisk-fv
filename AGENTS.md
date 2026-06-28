# Issue Dependency Graph Maintenance

Use these rules when maintaining `issue_deps.md` or GitHub issue dependencies.
GitHub's structured issue relationships are the source of truth; issue prose is
only evidence to audit, not a graph input by itself.

When creating an issue, decide whether it has a strict prerequisite before
leaving the task. If it does, set the GitHub `blockedBy` relationship immediately
after creation and regenerate `issue_deps.md` in the same change.

## GitHub Issue Structure

- Use `blockedBy` only for strict build prerequisites: `A` is blocked by `B`
  when `A` cannot be implemented, proved, or verified until `B` is done.
- Use parent/sub-issue relationships only for grouping, umbrella issues, and
  progress tracking. Do not turn hierarchy into dependency edges unless the same
  pair also has a real `blockedBy` relationship.
- Keep closed blockers only when they are true completed prerequisites. Remove
  stale closed blockers that no longer explain a build/proof dependency.
- If a real blocker exists but is unnamed, create a focused issue for it first,
  then link it as the blocker. Avoid encoding unnamed work only in graph text.
- Before changing relationships, query node IDs and current links. Do not run
  mutations speculatively.

```bash
gh api graphql -f owner='eth-act' -f repo='zisk-fv' -F issue=61 -f query='
query($owner:String!, $repo:String!, $issue:Int!) {
  repository(owner:$owner, name:$repo) {
    issue(number:$issue) {
      id number title state
      labels(first:20) { nodes { name } }
      blockedBy(first:50) { nodes { id number title state } }
      blocking(first:50) { nodes { id number title state } }
      parent { id number title state }
      subIssues(first:50) { nodes { id number title state } }
    }
  }
}'
```

Mutation examples, after replacing IDs with values from a read-only query:

```bash
gh api graphql -f blocked='ISSUE_NODE_ID' -f blocker='BLOCKER_NODE_ID' -f query='
mutation($blocked:ID!, $blocker:ID!) {
  addBlockedBy(input:{issueId:$blocked, blockingIssueId:$blocker}) {
    issue { number }
    blockingIssue { number }
  }
}'

gh api graphql -f blocked='ISSUE_NODE_ID' -f blocker='BLOCKER_NODE_ID' -f query='
mutation($blocked:ID!, $blocker:ID!) {
  removeBlockedBy(input:{issueId:$blocked, blockingIssueId:$blocker}) {
    issue { number }
    blockingIssue { number }
  }
}'
```

## Mermaid / Markdown Graph

- Regenerate `issue_deps.md` from GitHub structured `blockedBy`, `blocking`,
  parent, and `subIssues` data. Do not hand-invent dependency edges in Markdown.
- Preserve the edge meaning: `A --> B` means issue `A` is blocked by issue `B`.
- Include every open issue, plus closed issues that are real prerequisite nodes
  for included issues. Omit unrelated closed issues.
- Keep node titles, labels, state classes, and the legend current. Label classes
  should reflect GitHub labels (`soundness`, `completeness`, both, neither);
  closed prerequisite nodes should use the closed/done class.
- List parent/sub-issue relationships separately from the Mermaid dependency
  graph unless they also have structured blocker edges.
- After editing, verify both Markdown hygiene and Mermaid rendering:

```bash
git diff --check
mmdc -i issue_deps.md -o /tmp/issue_deps.svg
```
