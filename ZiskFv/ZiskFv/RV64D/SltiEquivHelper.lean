import ZiskFv.RV64D.Auxiliaries
import ZiskFv.Fundamentals.Execution

/-!
Phase 3C T-IT escape-hatch helper for SLTI / SLTIU Sail-equivalence.

`ZiskFv/RV64D/slti.lean` and `ZiskFv/RV64D/sltiu.lean` were shipped in
Phase 3B with pure-spec equivalence lemmas whose proofs fail to close
for the same structural reason SLT / SLTU fail (see
`ZiskFv/RV64D/SltEquivHelper.lean` docstring): after the
register-write reductions, the residual goal compares
`BitVec.setWidth 64 (if .toInt < then 1#1 else 0#1)` (Sail side) with
`if .slt then 1#64 else 0#64` (pure-spec side), and the shipped
tactic skeleton does not discharge the BitVec-setWidth / BitVec.slt
bridge. The main branch hides this because no downstream module
imports those two RV64D files (`lake build` skips them).

Phase 3C T-IT requires shipping SLTI / SLTIU circuit-level
Equivalence files, which *do* need a working Sail-equivalence lemma.
Per the Phase 3C read-only invariant on `ZiskFv/ZiskFv/RV64D/*.lean`,
we avoid mutating `slti.lean` / `sltiu.lean` directly. Instead this
helper file redeclares lightly-renamed versions of the input / output
structs (so there is no name collision with the broken upstream
declarations) and axiomatizes the same Sail-equivalence statement
under catalogued **C-series** entries (C7 for SLTI, C8 for SLTIU) in
`docs/fv/trusted-base.md`.

## Consumers

- `ZiskFv.Equivalence.Slti.equiv_SLTI_sail` consumes
  `PureSpec.slti_pure_equiv_axiom`.
- `ZiskFv.Equivalence.Sltiu.equiv_SLTIU_sail` consumes
  `PureSpec.sltiu_pure_equiv_axiom`.

## Closure path (Phase 4)

Identical to C5 / C6: fix `ZiskFv/RV64D/slti.lean` /
`ZiskFv/RV64D/sltiu.lean` by appending, after the
`dite_cond_eq_false` branch, a BitVec-bridging simp/split chain:

```
    congr 1
    split_ifs with h_cmp_a h_cmp_b h_cmp_c h_cmp_d
    all_goals first | rfl | (simp_all [BitVec.slt, BitVec.toInt]; bv_decide)
```

(or a direct `BitVec.setWidth_one_of_bool_eq_ofBool` bridge lemma).
Estimated 15-25 lines per opcode. Retiring C7 and C8 is a single-day
Phase 4 audit deliverable, jointly closable with C5 / C6 under a
single BitVec-bridge helper.
-/

namespace PureSpec

/-- SLTI input — same shape as `PureSpec.SltiInput` in
    `ZiskFv/RV64D/slti.lean`, re-declared here under a renamed name
    to avoid collision with the broken-proof upstream file. -/
structure SltiInput' where
  r1_val : BitVec 64
  imm : BitVec 12
  rd : Fin 32
  PC : BitVec 64

/-- SLTI output — same shape as `PureSpec.SltiOutput` upstream. -/
structure SltiOutput' where
  nextPC : BitVec 64
  rd : Option (Finset.Icc 1 31 × BitVec 64)

/-- Pure-spec SLTI — identical to `execute_ITYPE_slti_pure` upstream
    but on the helper's renamed types. The compared `b`-side value is
    the sign-extension of the 12-bit immediate. -/
def slti_pure (input : SltiInput') : SltiOutput' := {
  nextPC := input.PC + 4#64
  rd := if h : input.rd = 0
    then .none
    else .some (
      ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
      if input.r1_val.slt (BitVec.signExtend 64 input.imm) then 1#64 else 0#64
    )
}

/-- SLTIU input — same shape as `PureSpec.SltiuInput` upstream. -/
structure SltiuInput' where
  r1_val : BitVec 64
  imm : BitVec 12
  rd : Fin 32
  PC : BitVec 64

/-- SLTIU output — same shape as `PureSpec.SltiuOutput` upstream. -/
structure SltiuOutput' where
  nextPC : BitVec 64
  rd : Option (Finset.Icc 1 31 × BitVec 64)

/-- Pure-spec SLTIU — unsigned `<` against the sign-extended 12-bit
    immediate (the RV64I spec preserves sign-extension even for the
    unsigned comparison; the comparator itself is the unsigned
    `BitVec.lt` operator). -/
def sltiu_pure (input : SltiuInput') : SltiuOutput' := {
  nextPC := input.PC + 4#64
  rd := if h : input.rd = 0
    then .none
    else .some (
      ⟨ input.rd.val, by apply Finset.mem_Icc.mpr; omega ⟩,
      if input.r1_val < (BitVec.signExtend 64 input.imm) then 1#64 else 0#64
    )
}

/-- Escape-hatch axiom: Sail-level equivalence for SLTI. Catalogued as
    **C7** in `docs/fv/trusted-base.md`. Its statement matches the
    shipped (but failing) `execute_ITYPE_slti_pure_equiv` in
    `ZiskFv/RV64D/slti.lean`, adapted to the helper's renamed types.

    Closure path: fix the BitVec-bridge gap in the upstream proof
    (estimate: 15-25 lines; jointly with C5 / C6 / C8 under a single
    BitVec-bridge helper). -/
axiom slti_pure_equiv_axiom
    (slti_input : SltiInput')
    (r1 rd : regidx)
    {imm : BitVec 12}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slti_input.r1_val state)
    (h_input_imm : slti_input.imm = imm)
    (h_input_rd : slti_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slti_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTI))) state
      = let slti_output := slti_pure slti_input
        (do
          Sail.writeReg Register.nextPC slti_output.nextPC
          match slti_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state

/-- Escape-hatch axiom: Sail-level equivalence for SLTIU. Catalogued
    as **C8**. Same obstruction class as C7. -/
axiom sltiu_pure_equiv_axiom
    (sltiu_input : SltiuInput')
    (r1 rd : regidx)
    {imm : BitVec 12}
    {state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource}
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok sltiu_input.r1_val state)
    (h_input_imm : sltiu_input.imm = imm)
    (h_input_rd : sltiu_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some sltiu_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.SLTIU))) state
      = let sltiu_output := sltiu_pure sltiu_input
        (do
          Sail.writeReg Register.nextPC sltiu_output.nextPC
          match sltiu_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state

end PureSpec
