# The global claim is conditioned; "0 axioms" ≠ "0 trust"

Validated the headline README/CLAUDE claims against source (not just paraphrased
them). Most held: `zisk_riscv_compliant_program_bus` exists
(`Compliance.lean:95`), `rv64im_completeness` exists (`Rv64im.lean:5919`), both
axiom ledgers are genuinely empty (`baseline-axioms.txt` "Total entries: 0";
global closure 0 non-comment names), 63 `Equivalence/` files, `Wrappers/` is
current (so `simplification-suggestions.md`'s `FromTrust/` references are stale).

**The correction that matters for teaching:** the global theorem is **not
unconditional**. Its signature takes `(env : OpEnvelope)`,
`(h_bridge : env.aeneasBridgeTrust)`, `(h_memory_construction)`, and
`(h_known_bugs : Defects.NoKnownDefect env)`. So "0 axioms" is true *and* the
residual trust is real — it has been **relocated** from axioms into the global
theorem's hypotheses + the caller-burden ledger, and the claim is explicitly
**modulo known defects** (`trust/defects.md`; ZisK v0.17.0 bugs this repo found).
A green `lake build` therefore means "Sail = circuit for each arm, given the
bridge/memory/no-defect premises," not "ZisK matches the spec, period."

**Implications for future lessons:**
- Pitch every "what's proven" statement in terms of *what the caller must
  supply* (the OpEnvelope validity + bridge + no-defect premises). The trust
  gate, caller-burden ledger, and the "promise discharge" story (Lesson 04) are
  the heart of the re-architecture mission, not a footnote.
- Lesson 02 (one opcode end-to-end) must surface where each hypothesis enters
  and gets discharged, ending at the conditioned global theorem — not a clean
  unconditional one.

**Process note (feedback to self):** in-repo docs here grew alongside
AI-assisted code and are partly stale/overclaimed; the README even carries a
"no assurances" caution. Read signatures and baselines, don't paraphrase docs.
Also: `build/` and `.lake/` are unpopulated in this worktree, so the definitive
`lake build` has not been run locally — the strongest validation is still
outstanding (needs `nix run .#populate`, which is heavy).
