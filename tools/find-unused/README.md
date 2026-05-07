# find-unused

Systematic dead-code detector for `ZiskFv.Equivalence.*`.

Walks the elaborated Lean environment, computes the transitive forward
closure of constants reachable from the 63 canonical `equiv_<OP>`
roots, and prints any declaration under `ZiskFv.Equivalence.*` outside
that closure.

Catches what textual `grep` misses: simp-set members, instance fields,
type-class resolution, anonymous lemmas referenced through `_root_`
forms.

## Run

```sh
nix develop --command lake env lean tools/find-unused/FindUnused.lean
```

Output format: header lines starting with `#` (totals), followed by
the dead constant names (one per line, sorted).

## What counts as a "root"

A declaration `ZiskFv.Equivalence.<File>.equiv_<OP>` where `<OP>` is
all-uppercase + digits with no underscore-suffix. There are 63 such
canonicals — one per RV64IM opcode.
