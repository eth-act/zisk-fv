Plan: docs/ai/plan/PLAN_RV64IM_GLOBAL_COMPLETENESS.md
Focus: Strengthen RV64IM completeness from edge-grid coverage to Sail-source full acceptance for all non-FENCE RV64IM shapes.
Blocking: none.
Next step: Extend full decode-acceptance checks to loads, then stores/branches.
Digression: JALR, non-shift I-type ALU, and ADDIW now pass full generated decode acceptance over all architectural registers and 12-bit immediate encodings; prior edge-grid coverage was too weak.
