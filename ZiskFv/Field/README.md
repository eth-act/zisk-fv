# `ZiskFv/Field/`

The **Goldilocks field** layer, used everywhere as the ground field
for ZisK's algebraic constraints.

- **`Goldilocks.lean`** — defines `FGL := Fin (2^64 - 2^32 + 1)`
  (Goldilocks prime *p*) and the canonical `[Field FGL]` instance.
  The Field instance is declared **once globally** and a guard
  comment forbids shadowing it as a proof-local variable —
  shadowing creates a dummy instance that defeats `ring` and breaks
  `linear_combination` in subtle ways.
- **`GoldilocksPrimality.lean`** — Pratt-style primality certificate
  for *p*, proved by normalizing the concrete certificate with `norm_num`.
  Mathlib's Azure cache covers everything else, but this proof is
  project-local.
- **`GoldilocksBridge.lean`** — ties the Mathlib `Field` / `ZMod`
  formalisation to the `Fin p` representation used elsewhere in the
  tree.

No axioms; pure-proof layer. Imported transitively by essentially
every other file under `ZiskFv/`.
