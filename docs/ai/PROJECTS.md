# RV64IM Global Completeness

Plan to prove RV64IM completeness with Sail as the source of truth for valid raw instructions. The current result adds checked-in and generated decode-gap-only global theorem surfaces, splits exhaustive generated decode checks into one-proof modules, and verifies that production ZisK accepts/materializes every Sail-shaped supported RV64IM raw word outside explicit generic FENCE decode gaps. Full plan: `docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md`.
