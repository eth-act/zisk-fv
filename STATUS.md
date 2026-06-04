Plan: docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md
Focus: Sail relation infrastructure needed before the M extension slice.
Blocking: Nothing external; the next proof step is to make Sail encode/decode state-aware for extension-gated constructors.
Next step: Add a state-aware SailM return relation and lift the closed unconditional families into it, then resume M extension containment.
Digression: Register word ALU was verified and committed as `472522e4`.
