Plan: docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md
Focus: Strengthen RV64IM completeness from edge-grid coverage to Sail-source full acceptance for all non-FENCE RV64IM shapes.
Blocking: none.
Next step: Prove JAL full decode acceptance by isolating the `signext 21` totality obligation, then wire it into the upper/jump generated target.
Digression: JALR, non-shift I-type ALU, ADDIW, loads, stores, branches, LUI, and AUIPC now have full generated decode acceptance over their full encoded immediate/register domains; JAL remains open.
