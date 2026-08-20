# Status — #357 register derivation

Branch: `357-register-derivation`
Worktree: `/home/cody/zisk-fv/.worktrees/clean-migration-330/`
Plan: `../../docs/ai/plan/PLAN_RAW_ROOT_SOUNDNESS_320.md`

## Current state

All three `laneBridge_of_regAgree` conditions are resolved. Zero sorry in
Soundness.lean. Conditions 1 and 2 are proved; condition 3 is surfaced as a
premise (`entryRange`) because `packed_no_wrap` is not derivable from the
current infrastructure (Goldilocks field limitation: max packed value
2^64 - 1 exceeds GL_prime = 2^64 - 2^32 + 1 by 2^32 - 2).

### Proved

- **Condition 1** (`h_stepRegWrite_consistent`): proved in prior session.
- **Condition 2** (`h_stepRegWrite_converse`): all 63 opcodes. Commit `1cdfc46b`.
- **Condition 3** (`entryRange`): surfaced as a `root_soundness` premise.
  The `chunks_in_range` half is derivable per-opcode via `ComponentSpecFacts`;
  `packed_no_wrap` is not derivable (see RegisterCoverageBridge.lean:176
  corrected comment). This is an honest trust expansion, not laundering:
  the condition cannot be proved from the accepted trace.

### Errata fixed

- RegisterCoverageBridge.lean:176 comment claimed `packed_no_wrap` follows
  from `chunks_in_range`; arithmetic was wrong (2^32 + (2^32-1)*2^32 = 2^64,
  not 2^64 - 2^32). Corrected.

### Sorry not in #357 scope

- `h_start_store_reg_zero` in JALR RowDecode (RomDecodeBindingOps.lean)
- 57 `h_store_reg` in Decode_*_of_program (RomDecodeBindingOps.lean)
- ~20 `h_bits_store_reg` in ProgramDecode constructors
- 12 spin-file sorry (lb forwarding)
- ~224 RomDecodeBindingOps source-column sorry
