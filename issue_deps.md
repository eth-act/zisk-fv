# Issue Dependency Graph

This graph includes all GitHub issues open as of 2026-06-28, plus closed issues
that appear in GitHub's structured issue-dependency data. Node colors come from
GitHub labels: `soundness`, `completeness`, both labels, no relevant label, and
closed/done.

Solid arrows are built from GitHub's structured `blockedBy` / `blocking`
relationships only: `A --> B` means issue `A` is blocked by issue `B`.
Sub-issues are listed separately below because GitHub tracks them as hierarchy,
not dependency edges.

```mermaid
%%{init: {'themeVariables': { 'fontSize': '18px' }}}%%
flowchart TD
    classDef soundness fill:#3b82f6,stroke:#1d4ed8,color:#fff,font-weight:bold
    classDef completeness fill:#9ca3af,stroke:#6b7280,color:#fff,font-weight:bold
    classDef both fill:#ef4444,stroke:#b91c1c,color:#fff,font-weight:bold
    classDef neither fill:#22c55e,stroke:#16a34a,color:#fff,font-weight:bold
    classDef iou font-weight:bold
    classDef done fill:#000000,stroke:#000000,color:#fff,font-weight:bold

    subgraph Root["Soundness / root_soundness"]
        I61["#61<br/>root_soundness rowData gap"]:::soundness
        I74["#74<br/>instantiate on a real trace"]:::soundness
        I159["#159<br/>ROM image binding"]:::soundness
        I111["#111<br/>Aeneas bridge in-build"]:::done
        I151["#151<br/>row-local defect predicate"]:::soundness
        I141["#141<br/>derive placement/control"]:::soundness
        I100["#100<br/>Main PC handshake"]:::done
        I101["#101<br/>Binary-EQ aggregation"]:::soundness
        I115["#115<br/>remove RowTraceCoherence floor"]:::soundness
        I119["#119<br/>store RMW byte residual"]:::soundness
        I144["#144<br/>AcceptedZiskTrace numInstructions"]:::soundness
    end

    subgraph Decode["Decode / extraction / completeness"]
        I154["#154<br/>completeness meta"]:::completeness
        I162["#162<br/>prove raw decoder"]:::both
        I158["#158<br/>sync Aeneas toolchain"]:::both
        I108["#108<br/>extract table/witness data"]:::completeness
        I114["#114<br/>Arith boundary gap closed"]:::done
        I75["#75<br/>eliminate native_decide"]:::both
        I77["#77<br/>Sail-Lean differential tests"]:::both
        I78["#78<br/>external kernel re-check"]:::both
    end

    subgraph Cleanup["Cleanup / maintenance"]
        I116["#116<br/>delete _claimed_dead layer"]:::neither
        I117["#117<br/>find-unused private decls"]:::neither
        I118["#118<br/>project dead-code sweep"]:::neither
        I127["#127<br/>split BinaryExtensionPackedCorrect"]:::neither
        I128["#128<br/>split Bridge/Binary"]:::neither
        I165["#165<br/>CI Aeneas cache optimization"]:::neither
    end

    I74 --> I115 & I114 & I101 & I100 & I111
    I115 --> I100
    I118 --> I117
```

## GitHub Sub-Issues

These structured GitHub relationships are hierarchy/progress tracking, not
`blockedBy` dependencies, so they are not drawn as solid dependency arrows above.

- #61 has sub-issues #74, #100, #101, #111, #115, #141, and #151.
- #115 has sub-issue #119.
- #114 has sub-issue #108. This looks stale as a dependency relation because #114
  is closed while #108 remains open.

No current issue in the queried set has structured `trackedIssues` /
`trackedInIssues` relationships.

## Proposed Dependency Updates

These are not in the graph above unless they are added to GitHub's structured
relationships.

- Add #159 as a sub-issue of #61. Its body explicitly says "Child of #61."
- Add completeness-meta links from #154 to #108, #74, #77, #75, #78, and #162
  as either `blockedBy` dependencies or sub-issues, depending on whether #154 is
  meant to be a completion gate or a tracker. #111 is already closed and can stay
  as historical context in the issue body.
- Add #162 `blockedBy` #158. #162 says it reuses the in-build Aeneas import from
  #158, and #158 is still open.
- Add or identify a live blocker for #151's Arith range-table fidelity work. #151
  says it is blocked on that work, while the older related #114 is already closed.
