# ZiskFv Lean inputs

This repository is the Git-distribution snapshot of the generated Sail RV64D
Lean specification and the patched Aeneas Lean runtime used by
[`eth-act/zisk-fv`](https://github.com/eth-act/zisk-fv). It exists so Lake
consumers, including Aristotle, can fetch the inputs by immutable Git revision.

Do not edit this snapshot by hand. Its source of truth is the Nix derivations
in `zisk-fv`; regenerate it with:

```bash
cd /path/to/zisk-fv
nix run .#sync-aristotle-inputs -- write /path/to/zisk-fv-lean-inputs
```

The root `lakefile.toml` is the package interface. `leanrv/` and `aeneas/` are
source trees, not independently resolved Lake packages.
