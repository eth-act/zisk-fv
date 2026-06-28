# Clean fork divergences (`codygunton/clean` vs upstream `Verified-zkEVM/clean`)

The `clean-src` flake input (`flake.nix`) points at **`github:codygunton/clean`**, a fork of
`Verified-zkEVM/clean`. This file records every patch the fork carries *beyond* upstream, why it exists,
and whether it is an **upstream-PR candidate** — so we remember to contribute them back rather than carry
them indefinitely. (The flake comment already notes the fork is meant to re-point at upstream once changes
merge.)

> Maintenance: when you add/remove a fork patch, update this file AND the `clean-src` comment in
> `flake.nix` (and re-pin `flake.lock`). When an entry lands upstream, delete it here and drop the patch.

---

## D1 — `Air.Flat` adjacent-row (transition) constraints  · zisk-fv #100  · **UPSTREAM CANDIDATE (strong)**

- **Branch / commit:** `air-flat-transition-constraints` @ `497e4a41` (off the pinned base).
- **What:** an *additive* transition-constraint facility on the modern `Air.Flat` layer —
  - `Air.Flat.Component.transition : Input F → Input F → Prop := fun _ _ => True` (a new field, defaults to
    trivial so every existing component/proof is unaffected);
  - `Air.Flat.Table.TransitionConstraints` — the transition holds on each consecutive row pair
    (`∀ i, i+1 < len → component.transition (rowInput row_i) (rowInput row_{i+1})`);
  - `Air.Flat.EnsembleWitness.TransitionConstraints` — folds that over `allTables`.
  Plus the mechanical `⟨…⟩ → { circuit := … }` constructor sweep that adding a struct field forces
  (3 sites in Clean: `FlatEnsemble.lean` verifierTable ×2 + `empty_allTables`; 4 in `FibonacciWithChannels.lean`).
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
