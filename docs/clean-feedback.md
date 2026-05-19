# Clean — feedback log

A running list of concrete pain points, missing features, and improvement
requests for the [Clean](https://github.com/Verified-zkEVM/clean) Lean
DSL, observed while integrating Clean's design ideas into zisk-fv.

The intent is to maintain this as a working draft. Promote items to
upstream GitHub issues when they have a concrete reproduction and a
crisp ask.

Format per entry:

```
### <Short title>

**Observed:** Where in zisk-fv we hit the issue (file:line).
**Reproduction:** A minimal repro (synthetic file, or a link to the
                    specific zisk-fv source).
**Ask:** What we'd like from Clean upstream — a feature, a clarification
         in docs, a tactic, etc.
**Severity:** blocker / friction / nice-to-have
**Workaround used:** What we did instead.
```

---

## Seed entries (from earlier spike work)

These are observations from the prior `clean-transpiler-spike` exploration;
they will gain concrete reproductions as we encounter them again during
the staged integration phases.

### `deriving ProvableStruct` macro limit on wide rows

**Observed:** Spike's `ZiskFvClean/Generated/Main.lean` (38 stage-1 columns).
**Reproduction:** Synthetic flat `structure (F : Type) where x_1 : F; ...; x_38 : F deriving ProvableStruct` blows up the macro with
`Application type mismatch: List TypeMap vs List ProvableStruct.WithProvableType`.
**Ask:** Either raise the field-count limit, or document the supported
workaround (nested sub-structs) as the canonical pattern for wide rows.
A `deriving NestedProvableStruct` macro that auto-groups fields would
also work.
**Severity:** friction (blocks 38-column rows; works at ≤15)
**Workaround used:** Hand-write a slim row with just the columns the
spike's ADD slice needs.

### State-effect modeling vs `bus_effect`

**Observed:** Spike's `ZiskFvClean/Equivalence/Add.lean` — couldn't model
zisk-fv's `bus_effect` cleanly in Clean's channel framework.
**Reproduction:** A side-by-side comparison file showing the same opcode
(e.g., LD with `state.mem` updates) under zisk-fv's `bus_effect` model
and under `Air.Flat.Vm.SoundVmChannel`. The latter is heavier; not
obviously a translation target.
**Ask:** Design guidance (or a worked example) for opcodes whose RHS is
a state effect on a HashMap-like state, not a channel message. Clean's
`Air.Flat.Vm` is closest but the shape mismatches.
**Severity:** friction (real for any zkVM with state effects)
**Workaround used:** Kept `bus_effect` as-is; didn't try to port to Clean.

### sail-lean toolchain compatibility

**Observed:** `nix/sail-lean-tree.nix` patches in spike `edef6e4` — the
generated `Sail/Sail.lean` uses pre-`String.Slice` API and required
~6 mechanical sed substitutions.
**Reproduction:** Build `sail-lean-tree` from sail-riscv master against
Lean v4.28.0 without the patches; observe the `String.drop`/`take`/
`dropWhile` type mismatches.
**Ask:** Either Clean publishes per-Lean-version compatibility shims
for the standard sail-lean primitives, or documents which sail-riscv
revs are compatible with which Clean revs.
**Severity:** friction (recurs on every Lean bump)
**Workaround used:** Vendored sed patches in `nix/sail-lean-tree.nix`'s
`installPhase`.

### Witness vs row-input distinction in auto-emitters

**Observed:** Spike's `ZiskFvClean/Generated/BinaryAdd.lean` — cout_0,
cout_1 emitted as row inputs rather than `← witness ...` calls; broke
completeness recovery from `Spec` alone.
**Reproduction:** Any AIR with "auxiliary" columns derivable from primary
columns (carry bits, sign bits, range chunks). The PIL2 protobuf
doesn't distinguish primary from derived; an auto-emitter has no
metadata source.
**Ask:** Documentation or convention for PIL-to-Clean (or any
external-AIR-source-to-Clean) translators on how to detect/annotate
derived columns. Or: a Clean tactic that infers the witness/input split
from constraint shape.
**Severity:** nice-to-have (workarounds exist)
**Workaround used:** Pin cout values in `Assumptions` instead; closes
completeness but adds an Assumption clause.

### `circuit_proof_start` + project-local simp lemmas

**Observed:** Spike's `ZiskFvClean/BinaryAdd/Soundness.lean` —
`circuit_proof_start [carry_chain_lo_nat, …]` interaction with
project-local `@[circuit_norm]`-tagged lemmas is undocumented.
**Reproduction:** Author a downstream library with its own
`@[circuit_norm]` lemmas and invoke `circuit_proof_start` with a
mixed lemma list.
**Ask:** Docs or examples for downstream users with project-local simp
sets. In particular, when does the lemma argument shadow vs extend
`circuit_norm`?
**Severity:** nice-to-have
**Workaround used:** Trial and error; lemma argument was tried first.

### `StaticLookupChannel.guarantees_iff` authoring boilerplate

**Observed:** Anticipated for the byte-range / arith-table / MemAlignRom
adoption in Phase 5 of the integration plan.
**Reproduction:** Authoring `BytesTable : StaticLookupChannel (F p) field`
requires writing `guarantees_iff` by hand. The pattern is mechanical
("table membership ↔ value range"). For ZisK's 5+ static tables (byte,
arith, MemAlignRom, BinaryTable, BinaryExtensionTable), this adds up.
**Ask:** A tactic or macro `deriving guarantees_iff` (or
`auto_guarantees_iff`) that derives the proof from a `List.mem` /
`Vector.mem` enumeration.
**Severity:** nice-to-have
**Workaround used:** TBD; will encounter in Phase 5.

---

## New entries (encountered during integration phases)

(Phases 1-6 will append concrete entries here with file:line in zisk-fv
and minimal reproductions.)
