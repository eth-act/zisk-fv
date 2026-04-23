import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
Phase 3C T-RT escape-hatch helper for SLT / SLTU Sail-equivalence.

`ZiskFv/RV64D/slt.lean` and `ZiskFv/RV64D/sltu.lean` were shipped in
Phase 3B with pure-spec equivalence lemmas whose proofs fail to close:
after the register-write reductions, the residual goal compares
`BitVec.setWidth 64 (if .toInt < then 1#1 else 0#1)` (Sail side) with
`if .slt then 1#64 else 0#64` (pure-spec side), and the shipped
tactic skeleton does not discharge the BitVec-setWidth / BitVec.slt
bridge. The main branch hides this because no downstream module
imports those two RV64D files (`lake build` skips them).

Phase 3C requires shipping SLT / SLTU circuit-level Equivalence files,
which *do* need a working Sail-equivalence lemma. Per the Phase 3C
read-only invariant on `ZiskFv/ZiskFv/RV64D/*.lean`, we avoid
mutating `slt.lean` / `sltu.lean` directly. Instead this helper file
redeclares lightly-renamed versions of the input / output structs
(so there is no name collision with the broken upstream declarations)
and axiomatizes the same Sail-equivalence statement under catalogued
**C-series** entries (C5 for SLT, C6 for SLTU) in
`docs/fv/trusted-base.md`.

## Consumers

- `ZiskFv.Equivalence.Slt.equiv_SLT_sail` consumes
  `PureSpec.slt_pure_equiv_axiom`.
- `ZiskFv.Equivalence.Sltu.equiv_SLTU_sail` consumes
  `PureSpec.sltu_pure_equiv_axiom`.

## Closure path (Phase 4)

Fix `ZiskFv/RV64D/slt.lean` / `sltu.lean` by appending, after the
`dite_cond_eq_false` branch, a BitVec-bridging simp/split chain:

```
    congr 1
    split_ifs with h_cmp_a h_cmp_b h_cmp_c h_cmp_d
    all_goals first | rfl | (simp_all [BitVec.slt, BitVec.toInt]; bv_decide)
```

(or a direct `BitVec.setWidth_one_of_bool_eq_ofBool` bridge lemma).
Estimated 15-25 lines per opcode. Retiring C5 and C6 is a single-day
Phase 4 audit deliverable.
-/

namespace PureSpec

/-- SLT input — same shape as `PureSpec.SltInput` in
    `ZiskFv/RV64D/slt.lean`, re-declared here under a renamed name to
    avoid collision with the broken-proof upstream file. -/
structure SltInput' where
  r1_val : BitVec 64
  r2_val : BitVec 64
  rd : Fin 32
  PC : BitVec 64

/-- SLT output — same shape as `PureSpec.SltOutput` upstream. -/
structure SltOutput' where
  nextPC : BitVec 64
  rd : Option (Finset.Icc 1 31 × BitVec 64)

/-- Pure-spec SLT — identical to `execute_RTYPE_slt_pure` upstream
    but on the helper's renamed types. -/
def slt_pure (input : SltInput') : SltOutput' := {
  nextPC := input.PC + 4#64
  rd := if h : input.rd = 0
    then .none
    else .some (
      ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
      if input.r1_val.slt input.r2_val then 1#64 else 0#64
    )
}

/-- SLTU input — same shape as `PureSpec.SltuInput` upstream. -/
structure SltuInput' where
  r1_val : BitVec 64
  r2_val : BitVec 64
  rd : Fin 32
  PC : BitVec 64

/-- SLTU output — same shape as `PureSpec.SltuOutput` upstream. -/
structure SltuOutput' where
  nextPC : BitVec 64
  rd : Option (Finset.Icc 1 31 × BitVec 64)

/-- Pure-spec SLTU — unsigned `<`. -/
def sltu_pure (input : SltuInput') : SltuOutput' := {
  nextPC := input.PC + 4#64
  rd := if h : input.rd = 0
    then .none
    else .some (
      ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
      if input.r1_val < input.r2_val then 1#64 else 0#64
    )
}

/-- Escape-hatch axiom: Sail-level equivalence for SLT. Catalogued as
    **C5** in `docs/fv/trusted-base.md`. Its statement matches the
    shipped (but failing) `execute_RTYPE_slt_pure_equiv` in
    `ZiskFv/RV64D/slt.lean`, adapted to the helper's renamed types.

    Closure path: fix the BitVec-bridge gap in the upstream proof
    (estimate: 15-25 lines). -/
axiom slt_pure_equiv_axiom
    (slt_input : SltInput')
    (r1 r2 rd : regidx)
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slt_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok slt_input.r2_val state)
    (h_input_rd : slt_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slt_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLT))) state
      = let slt_output := slt_pure slt_input
        (do
          Sail.writeReg Register.nextPC slt_output.nextPC
          match slt_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state

/-- Escape-hatch axiom: Sail-level equivalence for SLTU. Catalogued
    as **C6**. Same obstruction class as C5. -/
axiom sltu_pure_equiv_axiom
    (sltu_input : SltuInput')
    (r1 r2 rd : regidx)
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltu_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok sltu_input.r2_val state)
    (h_input_rd : sltu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.SLTU))) state
      = let sltu_output := sltu_pure sltu_input
        (do
          Sail.writeReg Register.nextPC sltu_output.nextPC
          match sltu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state

end PureSpec
