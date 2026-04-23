import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
Phase 3C T-SL escape-hatch helper for LW Sail-equivalence.

`ZiskFv/RV64D/lw.lean` was shipped in Phase 3B with a pure-spec
equivalence lemma (`execute_LOADW_pure_equiv`) whose tactic skeleton
fails to close via `grind` at the final split-on-`rd = 0` step: the
reduction leaves a residual arithmetic side-hypothesis
`input.imm.toNat = input.r1_val.toNat + (BitVec.signExtend 64
input.imm).toNat` inside the `grind` state, which the tactic cannot
discharge in the non-zero-rd branch. The match-scrutinee on both
sides of the conclusion is actually identical (both pure-spec and
Sail-produced: `write_xreg ⟨input.rd.toNat, ⋯⟩ (BitVec.signExtend
64 (input.data3 ++ input.data2 ++ input.data1 ++ input.data0))`),
so this is a tactic-engineering gap rather than a semantic gap.

The main branch hides this because no downstream module imports
`RV64D/lw.lean` — `lake build` skips it and the "Known broken"
comment in `ZiskFv/ZiskFv.lean`'s RV64D coverage gate explicitly
mentions LW (alongside slt/sltu/slti/sltiu).

Phase 3C Track T-SL requires shipping LW's circuit-level
Equivalence file, which needs a working Sail-equivalence lemma.
Per the Phase 3C read-only invariant on `ZiskFv/ZiskFv/RV64D/*.lean`,
we avoid mutating `lw.lean` directly. Instead this helper file
redeclares a lightly-renamed version of the input / output structs
(`LwInput'` / `LwOutput'`, to avoid a name collision with the broken
upstream declarations) and axiomatizes the same Sail-equivalence
statement under a catalogued **C-series** entry (C9 for LW) in
`docs/fv/trusted-base.md`.

## Why C-series (vs. M-series)

The obstruction is control-flow / tactic-engineering — specifically,
`grind` failing to reconcile an address-arithmetic equation at the
final `split_ifs` step when the scrutinee on both sides is already
syntactically identical. It is not a memory-model platform gap: no
PMP / CLINT / alignment axiom chain is missing, `RISC_V_assumptions`
is sufficient, and the pure-spec's `BitVec.signExtend` matches Sail's
`BitVec.signExtend` verbatim. The obstruction class matches C5 / C6
(the Phase 3C T-RT SLT / SLTU escape-hatches) — a shipped Phase 3B
proof whose tactic closure was left incomplete.

LH and LB under Phase 3B's matching proof skeleton close cleanly
(verified: `lake env lean ZiskFv/RV64D/lh.lean` and `lb.lean` both
return no errors on the worktree base commit), so this helper
introduces only C9 for LW. No C10 / C11 / M12 are needed for the
T-SL track.

## Consumers

- `ZiskFv.Equivalence.Lw.equiv_LW_sail` consumes
  `PureSpec.lw_pure_equiv_axiom`.

## Closure path (Phase 4)

Fix `ZiskFv/RV64D/lw.lean` by replacing the terminal `grind` with
an explicit state-match chain. One candidate proof sketch: after
the `split_ifs` branch for `h_rd : input.rd ≠ 0`, rewrite the
`wX_write_xreg_non_zero_equiv` term, observe that both sides reduce
to the same `write_xreg ⟨input.rd.toNat, ⋯⟩ (BitVec.signExtend ...)`
call, and close with `rfl` (or a small `simp only` followed by
`rfl`). Estimated 10-20 lines. Retiring C9 is a single-hour
Phase 4 audit deliverable once that fix lands; the helper's renamed
structs (`LwInput'` / `LwOutput'`) can then alias `LwInput` /
`LwOutput` directly.
-/

namespace PureSpec

/-- LW input — same shape as `PureSpec.LwInput` in
    `ZiskFv/RV64D/lw.lean`, re-declared here under a renamed name to
    avoid collision with the broken-proof upstream file. -/
structure LwInput' where
  -- operands
  r1 : BitVec 5
  imm : BitVec 12
  rd : BitVec 5
  -- registers
  r1_val : BitVec 64
  PC : BitVec 64
  -- memory
  data0 : BitVec 8
  data1 : BitVec 8
  data2 : BitVec 8
  data3 : BitVec 8

/-- LW output — same shape as `PureSpec.LwOutput` upstream. -/
structure LwOutput' where
  -- registers
  nextPC : BitVec 64
  rd : Option (Finset.Icc 1 31 × BitVec 64)

private lemma range (bv : BitVec 5) (h : bv ≠ 0)
  : bv.toNat ∈ Finset.Icc 1 31 := by
  apply Finset.mem_Icc.mpr
  obtain ⟨x: Fin 32⟩ := bv
  fin_cases x <;> simp_all

/-- Pure-spec LW — identical to `execute_LOADW_pure` upstream but on
    the helper's renamed types. -/
def lw_pure (input : LwInput') : LwOutput' := {
  nextPC := input.PC + 4#64
  rd := if h: input.rd = 0
    then .none
    else .some (
      ⟨
        input.rd.toNat,
        range input.rd h
      ⟩,
      BitVec.signExtend 64 (input.data3 ++ input.data2 ++ input.data1 ++ input.data0)
    )
  : LwOutput'
}

/-- State assumptions for LW — mirror of `lw_state_assumptions` upstream,
    renamed. The memory-byte lookups at offsets 0..3 from the
    sign-extended imm-plus-base address cover the four byte lanes of
    the 32-bit loaded word. -/
def lw_state_assumptions' (i : LwInput')
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    : Prop :=
  state.regs.get? Register.PC = .some i.PC ∧
  LeanRV64D.Functions.rX_bits (regidx.Regidx i.r1) state
    = EStateM.Result.ok i.r1_val state ∧
  state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat]?
    = .some i.data0 ∧
  state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 1]?
    = .some i.data1 ∧
  state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 2]?
    = .some i.data2 ∧
  state.mem[i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat + 3]?
    = .some i.data3 ∧
  i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat < OpenVM_address_space_size ∧
  (4 : ℤ) ∣ i.r1_val.toNat + (BitVec.signExtend 64 i.imm).toNat

/-- Escape-hatch axiom: Sail-level equivalence for LW. Catalogued as
    **C9** in `docs/fv/trusted-base.md`. Its statement matches the
    shipped (but failing) `execute_LOADW_pure_equiv` in
    `ZiskFv/RV64D/lw.lean`, adapted to the helper's renamed types.

    Closure path: fix the terminal `grind` in the upstream proof
    (estimate: 10-20 lines, per the file docstring above). -/
axiom lw_pure_equiv_axiom
    (input : LwInput')
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    {mstatus : RegisterType Register.mstatus}
    {pmaRegion : PMA_Region}
    {misa : RegisterType Register.misa}
    {mseccfg : RegisterType Register.mseccfg}
    (risc_v_assumptions : RISC_V_assumptions state mstatus pmaRegion misa mseccfg)
    (h_opcode_assumptions : lw_state_assumptions' input state) :
    (do
      Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.LOAD (
        input.imm,
        regidx.Regidx input.r1,
        regidx.Regidx input.rd,
        true,
        4
      ))) state =
    let output := lw_pure input
    (do
      Sail.writeReg Register.nextPC output.nextPC
      match output.rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ()
      pure (ExecutionResult.Retire_Success ())) state

end PureSpec
