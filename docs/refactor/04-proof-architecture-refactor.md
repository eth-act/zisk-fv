# 04 — Proof architecture refactor

This targets the maintainability/extensibility problems S2–S4 from `01`. The
theme: **make the Clean model the spine, factor by *shape* not by *opcode*, and
derive facts at the ensemble seam instead of passing them in per opcode.**

## 4.1 R2 — One circuit model: make Clean the spine, retire `Airs/` records

**Problem (D1/S2).** `Airs/Valid_<AIR>` records are a second circuit model that
the whole equivalence stack is written against; `AirsClean` components are bridged
*into* them per opcode. `Valid_Main` alone is referenced by 299 files.

**Target.** The `GeneralFormalCircuit.Spec` of each `AirsClean` component is the
*only* interface the equivalence proofs consume. The per-opcode `Bridge.lean`
adapters (`rowAt`, `spec_of_valid`, `spec_via_component`) and the `Valid_<AIR>`
records disappear, or `Valid_<AIR>` survives only as a mechanically-derived
*view* of an `Air.Flat.Table` + environment (a `ℕ → FGL` projection) with a
single generic `rowAt`, not a parallel hand-written constraint model.

**Why it's safe.** `AcceptedZiskTrace` already derives per-table `Spec`s from
constraints + balance (`witness_spec_of_constraints`). So the Clean `Spec` is
*already available* wherever a `Valid_<AIR>` fact is used today; the bridge is
pure re-packaging. Removing it cannot weaken the theorem — it removes a
translation, not a hypothesis.

**How to sequence (per AIR family, incrementally):**
1. Pick the smallest family with a bridge (BinaryAdd is the pilot — it already
   has the full 6-file Clean component). Prove a *generic* `rowAt`-view lemma
   once: `Valid_<AIR>` facts ⇔ Clean `Spec` of the row projection.
2. Rewrite that family's `EquivCore/<Op>` to consume the Clean `Spec` directly.
3. Delete the family's `Bridge.lean` once nothing imports it.
4. When a `Valid_<AIR>` record has no remaining consumers, delete it.

**Measure of done:** `grep -rl Valid_Main ZiskFv | wc -l` trends toward the
handful of files that genuinely need a column view; `AirsClean/*/Bridge.lean`
count → 0.

> This is the single highest-value structural change. It removes ~18k lines of
> legacy model + the entire bridge surface, and it is what makes "idiomatic
> Clean" true from the components all the way up.

## 4.2 R3 — Factor per opcode → per shape

**Problem (S3).** ~63 opcodes × 7–9 layers of near-identical files.

**Observation.** The opcodes fall into ~12 *shapes* that already exist implicitly
(the ten `Compliance/Dispatch/*` families, the `Promises/{RType,IType,Branch,…}`
bundles, and the `EquivCore/WriteValueProofs/*` families). Within a shape, files
differ only by an input record name and one `instruction`/`rop`/`bop`/`shiftop`
constructor.

**Target layering (per shape `S`, not per opcode):**

```
Shapes/S/Spec.lean          -- parametric Sail-side + circuit-side statement for shape S
Shapes/S/Equiv.lean         -- ONE parametric theorem: equiv_S (op : SOpcode) …
Shapes/S/Promises.lean      -- the S-shape Promises bundle (already exists under Promises/)
```

and a **single generated instance table** mapping each opcode to
`(shape, input_type, instruction_ctor)`:

```lean
-- one place lists every opcode; instances are derived
def rtypeOps : List (RTypeOp) := [.add, .sub, .and, .or, .xor, .slt, .sltu, …]
-- equiv_<OP> for each op := equiv_RType op (by decide) …
```

Two implementation options (from `simplification-suggestions.md`, still valid):
- **Lower-friction, do this first:** per-shape envelopes
  (`RTypeBinaryEnvelope`, `BranchEnvelope`, …) parameterised by the opcode's
  `Input` and `instruction` constructor. `OpEnvelope` becomes ~12 shape arms
  instead of 63 opcode arms; the six branch arms collapse 6→1.
- **Higher-friction, only if needed:** a Lean `macro` generating the opcode
  instances from the table. Do this only where per-shape grouping still leaves
  real duplication (it may not, per that file's own assessment).

**Extensibility payoff:** a new RV64IM-shaped instruction becomes *one row in the
instance table* plus (if genuinely new) one shape file — not 7–9 new files.

**Naming cleanup that must ride along:** collapse the confusing
`EquivCore/<Op>` vs `Equivalence/<Op>` split (see `05`). After R3, "core" and
"canonical" are the same parametric theorem; keep one directory
(`Equivalence/`), delete the other, and fix the misfiled `EquivCore/README.md`.

## 4.3 R4 — Derive facts at the ensemble seam; shrink `Promises`

**Problem (D4).** `equiv_<OP>` carries caller-supplied facts that are true of any
accepted trace (`h_component`, `h_table_spec`, `h_provider_row`, `h_match`,
`h_lane_rd`, and much of `Promises`).

**Target.** Prove these *once*, generically, from `AcceptedZiskTrace`
(`constraints_hold` + `channels_balanced`) as reusable lemmas:

- `provider_row_facts` — for any accepted trace and any op-bus consumer, the
  matching provider row exists, its component is the expected one, and the
  op-bus entries match. This is a channel-balance consequence
  (`Balance.lean`'s guarantees-to-requirements reversal) — exactly what
  `Clean/Air/Vm.lean` or `OrderedChannels.lean` is for.
- `register_lane_facts` — `register_write_lanes_match` from the memory-bus
  balance.
- `main_row_pins` — `MainRowPins` from the Main table's constraints.

Then `equiv_S` takes *no* provider/lane/match binders; the `StepStrong*`
constructions feed these derived facts instead of demanding them. The
`trust/forbidden-param-shapes.txt` + caller-burden baselines then guard a *much
smaller* residual surface (ideally only genuine external trust from `03`'s
`SoundnessTrust`).

**Correctness guard (from `AGENTS.md`):** each removed binder must be *proved*,
never moved to a broader universal premise. The trust-gate baseline should
*shrink* at each step; a step that doesn't shrink it is suspect.

## 4.4 R5 — Idiomatic dispatch

Replace the `True`-padded conjunction (`OpEnvelope.exec_eq`) with a dependent
`match` returning the single relevant conclusion (`03` §3.3). This deletes the
ten `exec_eq_<family>` fields, the `Dispatch/` fan-out becomes one function by
cases, and the reader sees an honest case split. This also subsumes
`simplification-suggestions.md` #1 (collapse `dispatch_X`) and #3 (per-shape
envelopes).

## 4.5 Reusable abstractions to introduce (the "beautiful" part)

These are the small, general declarations that, once present, make the per-opcode
code shrink and read well. Several are already half-present under
`EquivCore/WriteValueProofs/` and `Equivalence/Promises/`; the point is to make
them *the* interface, not optional helpers.

1. **`ShapeSpec`** — a typeclass or record per shape capturing "how this shape's
   Sail `execute` relates to its circuit `bus_effect`", with one instance per
   shape. `equiv_S` is generic over it.
2. **`AcceptedTrace` fact-bundle lemmas** (R4): provider/lane/pin facts, proved
   once from balance.
3. **A single `Promises S`** per shape, threaded through *all* layers (canonical,
   wrapper, envelope) rather than re-exploded (this is
   `simplification-suggestions.md` #2, now mandatory rather than optional).
4. **`byteRange`/limb helpers** — the repeated 8-fold `(v.free_in_c_i r).val <
   256` extraction and the 29-way `op ∈ Binary table` disjunction become one
   lemma each (`simplification-suggestions.md` #6). Put them next to the Clean
   component, keyed on the component `Spec`, not on `Valid_<AIR>`.
5. **`WriteValue S`** — the rd-value derivation per shape (already factored under
   `WriteValueProofs/`); make every shave-off opcode consume it.

## 4.6 File-size hygiene

Several files exceed the 1000-line guidance and should be split as they are
touched: `Compliance/TraceLevelExport/BootSegmentMemorySeed.lean` (5.7k),
`Airs/Binary/BinaryExtensionPackedCorrect.lean` (5.2k),
`Compliance/TraceLevelExport/RomDecodeBindingOps.lean` (4.3k),
`EquivCore/Bridge/Binary.lean` (3.8k), `Compliance/OpEnvelope.lean` (2.7k),
`RowShape/Contract.lean` (1.4k, single file for the whole directory). Splitting
by shape (R3) naturally addresses most of these.

## 4.7 Order of operations (see `06` for the full roadmap)

R4 (derive facts) and R2 (Clean spine) are the load-bearing changes and should
lead, because R3 (shape factoring) and R5 (dispatch) are far cheaper once the
per-opcode hypotheses are gone and there is only one circuit model to factor.
