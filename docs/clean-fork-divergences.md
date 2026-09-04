# Clean fork divergences (`codygunton/clean` vs upstream `Verified-zkEVM/clean`)

The `clean-src` flake input (`flake.nix`) points at **`github:codygunton/clean`**, a fork of
`Verified-zkEVM/clean`. This file records each **semantic** patch the fork carries *beyond* upstream,
why it exists, and whether it is an **upstream-PR candidate** — so we remember to contribute them back
rather than carry them indefinitely. Purely cosmetic or proof-ergonomic patches are not given entries
here; the `clean-src` comment in `flake.nix` is the complete patch list, and currently carries one such
patch (`structure-instance notation in the *_mk lemmas`). (That comment also notes the fork is meant to
re-point at upstream once changes merge.)

> Maintenance: when you add/remove a semantic fork patch, update this file AND the `clean-src` comment in
> `flake.nix` (and re-pin `flake.lock`). When an entry lands upstream, delete it here and drop the patch.
>
> Do not record per-patch commit hashes here. A fork rebase rewrites them — it has already invalidated
> this file's hashes twice — while `flake.nix`'s `inputs.clean-src` comment sits next to the pinned rev
> and `flake.lock` holds the immutable one. Those are the provenance sources of truth.

---

## D1 — `Air.Flat` indexed adjacent-row (transition) constraints  · zisk-fv #100 / #226  · **UPSTREAM CANDIDATE (strong)**

- **Fork branch:** `port-zero-mult-gating`; see `flake.nix`'s `clean-src` comment for the patch that
  introduces it.
- **What:** an *additive* transition-constraint facility on the modern `Air.Flat` layer:
  - `Air.Flat.Component.transition : Nat → Environment F → Environment F → Prop := fun _ _ _ => True`;
  - `Air.Flat.Table.TransitionConstraints` applies it at every row index to the canonical predecessor/current
    effective environments, with row zero saturated to itself;
  - `Air.Flat.EnsembleWitness.TransitionConstraints` folds that over `allTables`.
  The indexed form is necessary for generated AIR expressions that read periodic fixed data at a successor
  position. Existing components remain unaffected because the default predicate is trivial.
- **Row-zero warning:** Lean's `row - 1` saturates at row zero; an imported PIL
  negative rotation is sound only with its source row-zero gate, never as an
  unguarded predecessor access.
- **Why:** `Air.Flat` is single-row *by design* (`FlatComponent.lean:8-10`: "There are no direct adjacent-row
  constraints; communication … is expressed by channel interactions"). But ZisK's Main AIR enforces a
  genuine cross-row **polynomial** PC-handshake constraint (`main.pil:409-410`), which is **not** a channel —
  so it cannot be modeled either as a per-row `Air.Flat` constraint or as a (faithful) channel. Clean already
  has the needed capability, but only in the *older, unused, unbridged* `Clean/Table` layer
  (`InductiveTable` / `CellOffset.next` / `everyRowExceptLast` / `table_soundness`). This patch brings a
  minimal slice of that capability onto `Air.Flat` so a single component can carry **both** channels (which
  Main needs for the op/mem/rom buses) **and** a transition constraint.
- **Upstream candidacy — strong.** Clean's own `Clean/Air/README.md:35-37` names exactly this as intended
  future work: *"Clean.Air is intended to become the common home for AIR-style infrastructure, including
  future support for the older inductive table style now living under Clean/Table."* This patch is the first
  step of that convergence.
- **Scope vs the "proper" convergence (deliberately NOT done here):** the full upstream feature would be a
  general k-row windowing facility (port `CellOffset W`/`CellAssignment`/`windowEnv`), with the windowed
  constraint **consumed by ensemble soundness** (not an inert field), plus completeness, the inductive
  chaining theorem, boundary constraints, and retiring `Clean/Table.InductiveTable`. We chose the minimal
  additive field because (a) it solves #100 faithfully, and (b) the proper version is a much larger,
  partly-research effort (integrating cross-row constraints with the channel-balance ensemble soundness) —
  scoped as a separate future contribution. Our `Component.transition` is **inert** (no Clean soundness
  theorem consumes it); on the zisk-fv side it is carried as a verifier-checked accepted-trace certificate
  (`AcceptedZiskTrace.transitions_hold`), in the same epistemic class as `main_height`. The upstream version
  should instead thread the transition through the soundness lift.

---

## D2 — `Air.Flat` component-owned indexed fixed columns  · zisk-fv #243 / S1b  · **UPSTREAM CANDIDATE (strong)**

- **Fork branch:** `port-zero-mult-gating`; see `flake.nix`'s `clean-src` comment for the patch that
  introduces it.
- **What:** `IndexedFixedColumns` declares a physical capacity, a raw-or-fixed layout for each effective
  output cell, and periodic fixed values. `Component` owns an optional schema; `Table` stores only raw rows
  and definitionally materializes canonical effective `table` rows. The same rows feed constraints, channel
  interactions and balance, indexed transitions, and projections. `Table.fixed_domain` bounds a table to the
  schema capacity, and `Table.index_lt_fixed_capacity` derives the no-wrap fact for an actual row.
- **Why:** preprocessed PIL columns, including Main's `SEGMENT_L1`/`STEP` and Mem's appended
  `SEGMENT_L1`/`__L1__`, are verifier-side data rather than caller-provided witness cells. A projection-only
  override would prove chronology against data different from the balanced interaction trace. Making the
  layout component-owned keeps all consumers on one canonical source and keeps the domain/no-wrap bound a
  structural facility invariant rather than an accepted-trace certificate or caller-supplied promise.
- **Upstream candidacy — strong.** It is a small, generic representation of standard AIR fixed columns and
  makes the modern `Air.Flat` layer usable for preprocessed-column AIRs without introducing a parallel table
  model. The eventual upstream convergence should establish a soundness lift for both D1 and D2; this fork
  deliberately does not claim that larger result.

---

## D3 — `Air.Flat` intrinsic cyclic successor transitions  · zisk-fv #242 / S4  · **UPSTREAM CANDIDATE (strong)**

- **Fork branch:** `port-zero-mult-gating`; a *separate* patch from D2's, offered upstream as PR
  [codygunton/clean#2](https://github.com/codygunton/clean/pull/2). See `flake.nix`'s `clean-src`
  comment for the patch list and its order.
- **What:** an additive `Component.cyclicSuccessorTransition` predicate with a
  trivial default, `successorEnvironment` over the component's materialized
  effective rows (indexed through an internal successor-index relation, which
  zisk-fv does not name directly), and table/ensemble predicates that apply it
  at every row. The `Fin table.length` successor is modulo the effective
  length, so the final effective row maps definitionally to row zero.
- **Why:** D1 deliberately retains predecessor/current semantics, including
  row-zero predecessor saturation. MemAlign's unmasked bus-133 lookup reads
  `DELTA_PC = pc' - pc` at every physical row, including the last-to-first
  rotation; modeling that with D1 would omit the required wrap or move it into a
  caller-supplied boundary promise. D3 owns that indexing relation structurally
  while leaving D1 and every existing D1 consumer unchanged.
- **Upstream candidacy — strong.** This is a small, general flat-AIR primitive
  for circuits whose next-row rotation is semantically cyclic. As with D1, the
  current predicate is inert in Clean's own soundness lift; any zisk-fv use must
  be carried by a verifier-checked accepted-trace certificate, never by a caller
  assumption. The longer-term upstream design should thread it through the
  ensemble soundness theorem alongside the D1 transition surface.
