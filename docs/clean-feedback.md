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

### Range-bus consolidation hits a participation-map wall

**Observed:** Phase 2 of the integration plan. Tried to consolidate
`main_columns_in_range`, `binary_columns_in_range`, and
`binary_add_columns_in_range` into one bus-level
`range_bus_lookup_sound` axiom.

**Reproduction:** The three per-AIR axioms each state "for any row,
this AIR's annotated columns satisfy their declared bit ranges."
The conjunct structure differs per AIR (Main has 9 fields with widths
{32, 8, 4}; Binary has 24 fields all width 8; BinaryAdd has 10
fields with widths {32, 16, 1}).

For consolidation, two approaches:

A. **Single conjunctive axiom over all participants.** Stated as
   `axiom range_bus_lookup_sound (m bin badd : ...) (r : ℕ) :
   <all-conjuncts>`. Each per-AIR theorem extracts its conjuncts.
   PROBLEM: every per-AIR consumer must now supply Binary +
   BinaryAdd validators too, even when they only care about Main.
   This is an invasive shape change to 21+ downstream files.

B. **Abstract via `RangeBusParticipant` structure.** A list of
   `(column-accessor, bit-width)` pairs forms a "participant
   record"; the axiom asserts "for any participant, every entry
   gets the bound." PROBLEM: this is too abstract — the axiom
   doesn't constrain what counts as a "participant," so the trust
   content moves to per-AIR `def`s that assert participation. Those
   defs are unverifiable against PIL (without further machinery),
   so the trust delta is zero, just renamed.

**Conclusion:** The range-bus axioms are honestly already at the
right granularity. The "consolidation win" I estimated (5-15 axioms)
in the integration plan was over-optimistic for this bus.

**Ask:** Clean's `StaticLookupChannel` pattern works for ROM-style
*tables* (fixed enumerations like the byte table 0..255), not for
*per-AIR declared widths*. Documentation or guidance for the latter
pattern would help.

**Severity:** finding, not a Clean bug. Affects the integration
plan's Phase 2 scope.

**Workaround used:** Skip the range-bus consolidation; focus
consolidation effort on classes where structural symmetry is real
(OpBus, MemBus emission bundles, lookup-table soundness axioms).

### Where consolidation IS structurally clean

After the range-bus finding, here's where the trust ledger actually
has consolidatable structure:

- **OpBus permutation axioms.** `op_bus_perm_sound_BinaryAdd`,
  `op_bus_perm_sound_Binary`, `op_bus_perm_sound_BinaryExtension`
  have identical shape (just different provider AIRs). Can be
  unified into one axiom taking a `provider` parameter, with the
  three per-AIR results becoming theorems. Trust content honest —
  this matches the cryptographic claim ("the operation bus's
  permutation argument is sound for any provider"). Net: 3 → 1.

- **Memory-bus emission bundles.** The 7 `main_*_emission_bundle`
  axioms package structural facts the channel `Message` would
  carry. Each one packs ~10 conjuncts about specific lane/ptr/rd
  routing. Genuine consolidation: define a `MemBusMessage` Provable
  type, and the bundle becomes a structural property of the message
  type, not an axiom. Net: 7 → 0 axioms (the structural facts
  move into the type definition), plus 1 retained axiom for the
  bus's permutation soundness.

- **Memory-bus + MemAlign permutation.** Two `memalign_*` axioms
  are specializations of the memory-bus permutation soundness to
  the MemAlign* providers. Consolidate by deriving them from a
  general memory-bus axiom. Net: 2 → 0 (provable from general).

- **Lookup-table soundness.** `bin_table_consumer_wf`,
  `bin_ext_table_consumer_wf` plus the BinaryExtension chain are
  structurally similar to one `StaticLookupChannel` axiom per
  table. Net: ~6 → 2.

**Realistic total trust ledger reduction**: ~12-15 axioms (mostly
from MemBus emission bundles + OpBus consolidation + lookup-table
consolidation), not the 20+ estimated in the original plan. Range
bus stays as-is.

---

### `import Clean` umbrella collides with Mathlib's Batteries.Data.Fin.Fold

**Observed:** `ZiskFv/Channels/OperationBus.lean` initial draft, line 1.

**Reproduction:**

```lean
-- file: scratch/CleanImportCollision.lean
import Clean
import Mathlib
example : True := trivial
```

Yields:

```
error: import Batteries.Data.Fin.Fold failed,
       environment already contains 'Fin.foldl_eq_foldl_finRange'
       from Clean.Utils.Misc
```

The collision is structural: `Clean.Utils.Misc` (line 62) defines
`Fin.foldl_eq_foldl_finRange`, and Lean's stdlib / Batteries
`Data.Fin.Fold` define the same name. Order-of-import flips which
one wins; loading both fails.

**Ask:**

Option A — rename Clean's lemma (preferred, since the stdlib one is
the more canonical home).
Option B — make the top-level `Clean` umbrella module skip
`Clean.Utils.Misc`'s utility lemmas that already live in stdlib.

**Severity:** friction — `import Clean` is the documented entry
point in `~/clean/Clean/Examples/`, so anyone integrating Clean
*alongside* Mathlib has to discover the narrower-imports workaround.

**Workaround used:** Import only `Clean.Circuit.Channel` +
`Clean.Circuit.Provable` + `Clean.Utils.Tactics.ProvableStructDeriving`,
which avoids pulling `Clean.Utils.Misc` and the collision.

---

### `[Field F]` requirement on TypeMap-shaped records

**Observed:** `ZiskFv/Airs/OperationBus/OperationBus.lean::OperationBusEntry`,
`ZiskFv/Airs/Bus/Interaction.lean::MemoryBusEntry`.

**Reproduction:** zisk-fv's existing bus-entry records declare
`structure OperationBusEntry (F : Type) [Field F] where ...`. Clean's
`ProvableType` / `TypeMap` machinery operates over `Type → Type` with
no `[Field F]` constraint on the structure itself. Trying to use
`OperationBusEntry` directly as a `Message` in `Channel F Message`
fails with the typeclass mismatch.

**Ask:** Documentation note in Clean's `ProvableType` / `Channel`
section explaining the convention — "your Message type should be
declared `structure Foo (F : Type) where ...` without `[Field F]`
unless its fields require it". The narrowing is straightforward
once you know to do it, but the failure mode is opaque to a first-
time integrator.

**Severity:** friction (documentation, no code change in Clean).

**Workaround used:** Introduced parallel TypeMap records
(`OpBusMessage`, `MemBusMessage`) without `[Field F]`, with
@[reducible] conversions to/from the existing zisk-fv records.


---

### LeanZKCircuit's `Circuit F ExtF C` extension-field parameter is operationally vestigial

**Observed:** Every `Valid_<AIR>` record, every `equiv_<OP>` theorem, every `Compliance/Wrappers/<Op>.lean`, every trust-ledger axiom in `ZiskFv/Trusted/Transpiler.lean` opens with the boilerplate `variable {C : Type → Type → Type} [Circuit FGL FGL C]` (`F = FGL, ExtF = FGL` — both Goldilocks). 43 files in zisk-fv import `LeanZKCircuit.OpenVM.Circuit`.

**Reproduction:** Investigation in this branch's conversation log. The `Circuit F ExtF α` typeclass at `LeanZKCircuit/OpenVM/Circuit.lean:3-11` has 8 methods; three of them return ExtF (`challenge`, `exposed`, `permutation`). In principle these are needed to express PIL2 permutation-accumulator constraints of shape `gsum_next = gsum + challenge * column` which genuinely mix F (column) with ExtF (challenge, gsum).

But in *both* openvm-fv and zisk-fv, the ExtF-using constraints are filtered out at extraction time:

- openvm-fv: `OpenvmFv/Extraction/AccessAdapterAir_4.lean:27-43` — ExtF-using constraints are emitted as Lean comments. No proof consumes them.
- zisk-fv: `tools/pil-extract/src/main.rs:425-435` — extractor `bail!`s on any constraint mixing F with ExtF, so the constraint never reaches the Lean output. `grep "Circuit.challenge\|Circuit.permutation\|Circuit.exposed" build/extraction/Extraction/*.lean` returns zero uncommented hits.
- Bus emissions: `tools/pil-extract/src/main.rs:769-771` stubs any ExtF-tainted slot to literal `0`. **50 of 99 bus emission slots in `build/extraction/Extraction/Buses.lean` are stubbed.**

The permutation-argument soundness that ExtF was meant to express lives instead in the trust-ledger axioms (class #4 bus/lookup soundness, class #6 lookup-table soundness) — *separate from* the constraint encoding. So ExtF is structurally present in the typeclass but operationally unused for the zisk-fv proof.

**Why this is feedback for the Clean migration:** Clean's `Channel F Message` and `Air.Flat.Component F` use **one field type** at the user level. There is no analogue of the permutation-accumulator constraint that exposes a second field, because Clean handles permutation soundness via `Air.Balance` (a theorem over multisets of channel interactions, not via per-row constraints over F+ExtF). So replacing `Valid_<AIR>` with `Component F` is *principled*, not just convenient — it drops a 30-character boilerplate prefix (`variable {C : Type → Type → Type} [Circuit FGL FGL C]`) from every theorem signature, and removes 43 files' worth of LeanZKCircuit import overhead.

**Ask:** Not a Clean change request — Clean already gets this right. This entry documents the *contrast* with LeanZKCircuit's design as a justification for the migration, so future readers don't recreate the ExtF parameter under the impression it's load-bearing. It isn't.

**Severity:** N/A (justification for the integration choice, not a Clean defect).

**Workaround used:** Phase 3-6 of the integration plan replaces `Valid_<AIR>` with Clean Components, drops the `Circuit FGL FGL C` boilerplate from all theorem signatures, and at the final cutover removes the `LeanZKCircuit` require from `lakefile.toml`.

