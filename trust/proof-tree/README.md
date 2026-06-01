# zisk-fv proof tree visualizer

This is a local inspection tool for trust reviews. It renders a single-page D3
graph of the constant graph reachable from the global theorem
`ZiskFv.Compliance.zisk_riscv_compliant_program_bus` down to the axiom leaves
of the trust ledger. It is not part of CI; the machine-checked trust gates live
under [`../scripts/`](../scripts/).

## Run

```bash
trust/proof-tree/serve.sh
# → http://0.0.0.0:4042
```

Drag to pan, scroll to zoom. Hover a node for its full name + depth-from-root.
Click a node to copy its name to clipboard. Use the buttons to reset the view,
toggle all node labels (off by default — only the root + axiom leaves are
labeled, to keep the view readable), or kick the force-simulation.

## Color legend

- **green** — root (`zisk_riscv_compliant_program_bus`)
- **blue** — project const (theorem, def, lemma)
- **red** — axiom leaf (trust-ledger entry)

External references (mathlib, Sail, Lean core) are not shown — only the
internal `ZiskFv.*` structure plus its axiom leaves.

## Regenerate `edges.tsv`

```bash
nix develop --command lake exe trust-gate print-tree-edges \
  ZiskFv.Compliance.zisk_riscv_compliant_program_bus \
  > trust/proof-tree/edges.tsv
```

The TSV is gitignored (~1.4 MB).
