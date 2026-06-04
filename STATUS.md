Plan: docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md
Focus: M extension slice: add Sail containment for MUL/DIV/REM register and word opcodes using the state-aware Sail relation.
Blocking: Nothing currently blocking.
Next step: Prove M constructor state-aware encoder facts under `Rv64imEnabledSailState`, then map them into `RTypeRegisterShape`.
Digression: Sail relation infrastructure now supports extension-gated Sail constructors and preserves the closed Register ALU / Register word ALU containment path.
