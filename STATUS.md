Plan: docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md
Focus: Completed RV64IM Sail-source acceptance completeness slice.
Blocking: none; generated Aeneas, checked-in Lean, and Rust extraction sanity tests all passed.
Next step: PR open for review: https://github.com/eth-act/zisk-fv/pull/57
Digression: Implemented the intended acceptance boundary: raw materialization now delegates to the extracted accepted wrapper, generated decode checks are split into one-proof modules, and both generated and checked-in completeness have decode-gap-only global theorems for supported Sail-shaped RV64IM raw words.
