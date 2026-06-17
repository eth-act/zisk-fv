# "Promise discharge" is layered; per-opcode promises relocate into OpEnvelope

Traced ADD end-to-end against source (Lesson 02). The CLAUDE.md shorthand
"`Compliance/Wrappers/<Op>` does promise discharge" is looser than the literal
structure. Validated reality for ADD:

- **EquivCore `equiv_ADD_of_wf`** — the real arithmetic proof (Sail ADD = bus
  effect, given ~80 exploded row facts). `EquivCore/Add.lean`.
- **EquivCore `equiv_ADD_of_static_row`** (`Add.lean:378`) — discharges the ~80
  facts from one well-formed `BinaryRow` (`byte_chain_discharge_64_of_static_row`).
- **Wrapper `Compliance.equiv_ADD`** (`Wrappers/Add.lean:42`) — discharges row
  *existence + WF* from the Clean `Air.Flat.Table` spec. **Threads `promises`,
  `pins`, `h_match` through untouched.**
- **Canonical `Equivalence.equiv_ADD`** (`Equivalence/Add.lean:21`) — no
  discharge; only reshapes the conclusion (`bus_effect.2` → channel-balance).
- **Dispatch** (`Dispatch/ADD_RTYPEW.lean:48`) — `cases env`, unpacks
  `OpEnvelope.add_via_binary` fields (incl. `promises`) into the canonical thm.
- **`OpEnvelope`** (`OpEnvelope.lean:161`, inductive, 2384 lines) — the
  `.add_via_binary` constructor (`:366`) carries `promises : RTypePromises`
  (`:391`) **as a field**.

**Decision-grade insight:** the per-opcode promises are never proved — they are
**relocated into the `OpEnvelope` the caller must construct**. What is genuinely
proven is narrower and real: arithmetic ← well-formed row ← valid table.
Residual trust for ADD = constructing a valid `OpEnvelope` (the promises +
`h_match` + `pins`) **plus** the three global hypotheses. This is consistent
with — and is the concrete instance of — the "structural-unpacking exception"
in CLAUDE.md, where per-opcode binders collapse into shared `Compliance`/
envelope parameters so the *global* footprint stays at 0 axioms.

**Implications:** (1) `RTypePromises` = Sail-state ↔ bus correspondence (15
fields, `Promises/RType.lean:31`); this is the per-opcode answer to "what do the
hypotheses mean." (2) The open re-architecture question is whether promises
should be *derived* (from the Aeneas/trace side) rather than assumed as envelope
fields — Lesson 04 (global hypotheses) and a future extraction lesson. (3)
Corrected Lesson 01's diagram + tower prose, which had overstated the wrapper as
"discharging promise hypotheses." Supersedes the wrapper framing in LR-0001's
mental model.
