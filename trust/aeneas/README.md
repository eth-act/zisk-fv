# Tracked Aeneas Extraction

`ProductionM2.lean` is the canonical checked-in copy of the Aeneas-generated
Lean extraction for the production-backed ZisK RV64IM lowering surface.

Regenerate it from the pinned flake inputs with:

```bash
AENEAS_UPDATE_TRACKED=1 nix run .#aeneas-production-extract
```

CI runs:

```bash
nix run .#aeneas-production-extract-check-tracked
```

That command regenerates `build/aeneas-production-extraction/Lean/ProductionM2.lean`
and fails unless it is byte-identical to this tracked copy. Temporary LLBC files
and generated harness modules such as `GeneratedChecks.lean` remain untracked
under `build/`.

Both extraction recipes pass the pinned translator's `-sequential` option.
Its default Domainslib pool follows the host's recommended domain count,
which CPU quotas and `LEAN_NUM_THREADS` do not bound. This changes scheduling,
not extraction semantics or trust; the existing fresh-output and Lean checks
remain enabled. The ROM recipe also honors the caller's `CARGO_BUILD_JOBS`.

The additive `ProductionM2/RomFlags.lean` module extracts the existing
`ZiskInst::get_flags` method directly from the same 9ca88b5 source under the
`aeneas_extract` profile, in a separate namespace. It does not alter
`ProductionM2.lean` or claim extraction of `RomSM::compute_trace_rom`.

Regenerate only this module from a checkout of that source revision:

```bash
ZISK_ROM_SOURCE=/path/to/zisk scripts/aeneas-rom-flags-extract.sh --update
```

Run in the existing Nix development shell for the Cargo/cross-compiler tools.
The recipe copies the actual tracked source into its private build directory;
it adds no Rust wrapper or replacement function. Its provenance manifest
records the exact source contents, root span, profile, LLBC and generated hash.
`ZiskFv.Compliance.RomProducerFlags` relates the returned flag word to
`Main.packFlags`; the separate eleven-slot ROM serializer remains a distinct
producer obligation.

`nix run .#aeneas-rom-flags-extract-check-tracked` regenerates and compares
this new snapshot; the ordinary test entry point also runs that check before
Lake. Its namespace isolation renames only the additive Lean enum identifier
`zisk_inst.ZiskOperationType` to `zisk_inst.RomFlagsOperationType`, avoiding a
global discriminant-instance collision in the pinned Aeneas runtime. The
recipe checks all 20 qualified occurrences, preserves the actual method body
byte-for-byte, and records both raw and alpha-isolated output hashes.

The complete, unfiltered type-and-value axiom audit for both additive modules
(including constructor, private and compiler declarations) is reproducible with
`lake env lean tools/check-rom-producer-axioms.lean`. It cross-checks every
root against `Lean.collectAxioms` and writes the union and full dependency
paths to `build/rom-flags-all-roots-raw.json`; it applies no axiom allowlist.
