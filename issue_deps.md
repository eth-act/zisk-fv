# Issue Dependency Graph

This graph includes all GitHub issues open as of 2026-06-28, plus closed issues
that are explicit predecessors or already-done nodes in the dependency map. Node
colors come from GitHub labels: `soundness`, `completeness`, both labels, no
relevant label, and closed/done.

Arrows preserve the issue-map convention from the seed diagram: `A --> B` means
that `A` is downstream of, decomposed into, or intentionally tracked through `B`.
This is not GitHub's formal blocker metadata, and the graph is not intended to
be a strict DAG.

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
        I76["#76<br/>load memory premise reduced"]:::done
        I103["#103<br/>Mem seam capability banked"]:::done
        I114["#114<br/>Arith boundary gap closed"]:::done
        I144["#144<br/>AcceptedZiskTrace numInstructions"]:::soundness
    end

    subgraph Decode["Decode / extraction / completeness"]
        I154["#154<br/>completeness meta"]:::completeness
        I162["#162<br/>prove raw decoder"]:::both
        I158["#158<br/>sync Aeneas toolchain"]:::both
        I108["#108<br/>extract table/witness data"]:::completeness
        I109["#109<br/>extraction uniformity subsumed"]:::done
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

    I61 --> I74
    I61 --> I141 & I159 & I115 & I119 & I100 & I101 & I151 & I111

    I74 --> I151 & I115 & I111 & I141
    I141 --> I100 & I101
    I101 --> I100

    I115 --> I119
    I115 --> I76 & I103
    I119 --> I76 & I103
    I151 --> I114

    I159 --> I111 & I108
    I154 --> I111 & I108 & I74 & I77 & I75 & I78 & I162
    I162 --> I158 & I75 & I159
    I111 --> I158
    I108 --> I158
    I109 --> I114 & I108
    I78 --> I75

    I118 --> I117
    I116 --> I117
```
