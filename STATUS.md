Plan: docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md
Focus: Immediate ALU slice: add Sail containment for ADDI/SLLI/SLTI/SLTIU/XORI/SRLI/SRAI/ORI/ANDI.
Blocking: Nothing currently blocking.
Next step: Commit the verified M extension slice, then start Immediate ALU whitelist and raw-shape lemmas.
Digression: M extension Sail containment is verified under the state-aware `Rv64imEnabledSailState` relation; Lake build and Aeneas production completeness both passed.
