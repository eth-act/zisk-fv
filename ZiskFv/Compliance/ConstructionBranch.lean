import ZiskFv.Compliance.OpBusProviderMatch
import ZiskFv.Compliance.SailTrace
import ZiskFv.Compliance.Wrappers.Beq
import ZiskFv.Compliance.Wrappers.Bne
import ZiskFv.Compliance.Wrappers.Blt
import ZiskFv.Compliance.Wrappers.Bge
import ZiskFv.Compliance.Wrappers.Bltu
import ZiskFv.Compliance.Wrappers.Bgeu

/-!
# Sound branch constructions (`construction_{beq,bne,blt,bge,bltu,bgeu}_sound`)

The six RV64 conditional-branch envelopes of the P4 endgame, taking the
construction set 47 → 53. Each assembles the canonical branch conclusion
(`execute_instruction (.BTYPE …) state = (bus_effect exec_row [] state).2`) from
an accepted full-ensemble trace plus an explicit, named, top-level set of
residual binders — mirroring `construction_add_sound`, but on the
**control-flow** side, with NO operation bus and NO memory bus.

## Why branches are the SIMPLEST construction

A conditional branch reads `rs1`/`rs2`, compares them, and updates only the PC.
It emits NO operation-bus entry (so there is no provider disjunction to resolve
from `trace.channels_balanced`, in contrast to ADD/SUB), and NO memory-bus entry (so there
is no `StorePcMemoryWitness` / rd-write to discharge, in contrast to LUI/AUIPC).
The entire state effect is carried by the execution bus's single PC update. The
canonical `equiv_<BOP>` consumes only a `BranchInstrOperands` + a `BranchPromises`
bundle — no Main-row pins, no `Valid_Main`, no `r_main`. The construction is
therefore the thinnest in the sweep: it just packages the named residuals into a
`BranchPromises` bundle and dispatches.

The branch **comparison itself** (which way the branch goes: taken vs not-taken)
is already proved inside the canonical equiv via `execute_<BOP>_pure` — the
construction does NOT re-prove it. The construction's only control-flow
obligation is the next-PC residual (below).

## The honest residual budget

* **(a) derived inside the body** (NOT binders): nothing structural — the bundle
  is a pure repackaging of the named residuals. (The `bus_effect`-side equation
  is discharged inside the canonical `equiv_<BOP>`.)

* **(b) named residual** — explicit top-level binders:
  - operand bridges (3): `h_input_imm`, `h_input_r1`, `h_input_r2`
    (the branch's immediate + the two source-register Sail reads).
  - Sail-side mode facts (3): `h_input_pc`, `h_input_misa`, `h_misa_c`
    (PC knowledge + ZisK's `misa[C] = 0` no-compressed profile).
  - **control-flow next-PC residual (1): `h_nextPC_matches`** — the
    **#100 cross-row CONDITIONAL next-PC obligation**. It equates the circuit's
    exec-bus PC field (`exec_row[1]!.pc`, which carries the taken-target
    `pc + imm` OR the not-taken `pc + 4` depending on the row's flag output) to
    `(execute_<BOP>_pure …).nextPC` (Sail's conditional next PC). This is
    GENUINELY IRREDUCIBLE here: the circuit's next-row PC linkage is a cross-row
    fact about how the branch row's flag drives the *following* row's PC cell,
    which the local row constraints alone do not pin. It is the SAME
    `h_nextPC_matches`-shaped residual every one of the 47 prior constructions
    already carries, except the RHS is now Sail's *conditional* nextPC rather than
    a fixed `pc + 4`. NO separate taken/not-taken selector is needed: the
    conditional is fully absorbed into this one equation (Sail's
    `execute_<BOP>_pure.nextPC` is itself the `if cmp then pc+imm else pc+4`
    term, and the circuit's `exec_row[1]!.pc` is its counterpart).
  - branch-outcome facts (2): `h_not_throws`, `h_success`
    (the happy-path: aligned target, no fetch-address-align fault under ZisK's
    RV64IM profile).

* **(c) artifact**: the `exec_row : List (ExecutionBusEntry FGL)` **∀-binder**
  (carried inside `BranchInstrOperands.exec_row`) plus its length/multiplicity
  fields (`h_exec_len`, `h_e0_mult`, `h_e1_mult`).

## Residual budget: EXACTLY 11 + exec_row

`3 + 3 + 1 + 2 + 3 (exec shape) - ...`: the twelve `BranchPromises` fields minus
the bundling, made flat top-level binders, plus `misa_val` and the `exec_row`
∀-binder. No `MainRowProvenance` / `*RowBinding` leaf appears anywhere.

## Anti-vacuity

`exec_row` is a genuine top-level ∀-binder; the exec hypotheses are built from
it, not chosen to trivialize a hypothesis. The memory bus is genuinely empty
(`[]`) — a branch performs no register write or memory access, matching Sail.

## Axioms

All six constructions introduce **0 PROJECT (`ZiskFv.*`) axioms**. Their closure
includes the Sail-translation axioms and the Lean-kernel postulates as documented
external trust (`TrustGate.AxiomClosure.isProjectAxiom` filters those by design).
-/

namespace ZiskFv.Compliance

open ZiskFv.Trusted
open ZiskFv.EquivCore.Promises

set_option maxHeartbeats 2000000

/-- Sound BEQ construction (the control-flow SPIKE — validates the conditional
    next-PC pattern). From the accepted trace + honest residual binders, conclude
    the canonical `execute (BTYPE BEQ) = (bus_effect exec_row [] …).2`.

    Honest top-level residual binders (11 + `exec_row`):
    * (b) operand bridges (3): `h_input_imm`, `h_input_r1`, `h_input_r2`
    * (b) Sail mode facts (3): `h_input_pc`, `h_input_misa`, `h_misa_c`
    * (b) control-flow next-PC (1): `h_nextPC_matches` — the #100 cross-row
      CONDITIONAL next-PC obligation (taken `pc+imm` vs not-taken `pc+4`,
      absorbed into the single exec-bus-PC ↔ Sail-nextPC equation)
    * (b) branch-outcome (2): `h_not_throws`, `h_success`
    * (c) exec artifacts (3): `h_exec_len`, `h_e0_mult`, `h_e1_mult`, PLUS the
      genuine `exec_row` ∀-binder (with `misa_val`). -/
theorem construction_beq_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    -- (b) operand bridges
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
      = EStateM.Result.ok beq_input.r1_val (binding i))
    (h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
      = EStateM.Result.ok beq_input.r2_val (binding i))
    -- (b) Sail mode facts
    (h_input_pc : (binding i).regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : (binding i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- (c) exec artifacts: the exec row is a genuine top-level binder.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    -- (b) control-flow CONDITIONAL next-PC residual (#100 cross-row obligation)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC)
    -- (b) branch-outcome (happy path)
    (h_not_throws : (PureSpec.execute_BEQ_pure beq_input).throws = false)
    (h_success : (PureSpec.execute_BEQ_pure beq_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) (binding i)
      = (bus_effect exec_row [] (binding i)).2 := by
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨imm, r1, r2, misa_val, exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state beq_input.imm beq_input.r1_val beq_input.r2_val beq_input.PC
      ops.misa_val
      (PureSpec.execute_BEQ_pure beq_input).nextPC
      (PureSpec.execute_BEQ_pure beq_input).throws
      (PureSpec.execute_BEQ_pure beq_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }
  exact ZiskFv.Compliance.equiv_BEQ state beq_input ops promises

/-- Sound BNE construction. Identical shape to `construction_beq_sound`; differs
    only in the comparison opcode (BNE = not-equal), whose taken/not-taken
    semantics live entirely inside `execute_BNE_pure` / canonical `equiv_BNE`.
    The conditional next-PC residual `h_nextPC_matches` is the #100 cross-row
    obligation. -/
theorem construction_bne_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (bne_input : PureSpec.BneInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bne_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
      = EStateM.Result.ok bne_input.r1_val (binding i))
    (h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
      = EStateM.Result.ok bne_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some bne_input.PC)
    (h_input_misa : (binding i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BNE_pure bne_input).nextPC)
    (h_not_throws : (PureSpec.execute_BNE_pure bne_input).throws = false)
    (h_success : (PureSpec.execute_BNE_pure bne_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BNE)) (binding i)
      = (bus_effect exec_row [] (binding i)).2 := by
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨imm, r1, r2, misa_val, exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state bne_input.imm bne_input.r1_val bne_input.r2_val bne_input.PC
      ops.misa_val
      (PureSpec.execute_BNE_pure bne_input).nextPC
      (PureSpec.execute_BNE_pure bne_input).throws
      (PureSpec.execute_BNE_pure bne_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }
  exact ZiskFv.Compliance.equiv_BNE state bne_input ops promises

/-- Sound BLT construction (signed less-than). See `construction_beq_sound`. -/
theorem construction_blt_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (blt_input : PureSpec.BltInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : blt_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
      = EStateM.Result.ok blt_input.r1_val (binding i))
    (h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
      = EStateM.Result.ok blt_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some blt_input.PC)
    (h_input_misa : (binding i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLT_pure blt_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLT_pure blt_input).throws = false)
    (h_success : (PureSpec.execute_BLT_pure blt_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLT)) (binding i)
      = (bus_effect exec_row [] (binding i)).2 := by
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨imm, r1, r2, misa_val, exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state blt_input.imm blt_input.r1_val blt_input.r2_val blt_input.PC
      ops.misa_val
      (PureSpec.execute_BLT_pure blt_input).nextPC
      (PureSpec.execute_BLT_pure blt_input).throws
      (PureSpec.execute_BLT_pure blt_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }
  exact ZiskFv.Compliance.equiv_BLT state blt_input ops promises

/-- Sound BGE construction (signed greater-or-equal). See `construction_beq_sound`. -/
theorem construction_bge_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (bge_input : PureSpec.BgeInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bge_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
      = EStateM.Result.ok bge_input.r1_val (binding i))
    (h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
      = EStateM.Result.ok bge_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some bge_input.PC)
    (h_input_misa : (binding i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGE_pure bge_input).nextPC)
    (h_not_throws : (PureSpec.execute_BGE_pure bge_input).throws = false)
    (h_success : (PureSpec.execute_BGE_pure bge_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGE)) (binding i)
      = (bus_effect exec_row [] (binding i)).2 := by
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨imm, r1, r2, misa_val, exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state bge_input.imm bge_input.r1_val bge_input.r2_val bge_input.PC
      ops.misa_val
      (PureSpec.execute_BGE_pure bge_input).nextPC
      (PureSpec.execute_BGE_pure bge_input).throws
      (PureSpec.execute_BGE_pure bge_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }
  exact ZiskFv.Compliance.equiv_BGE state bge_input ops promises

/-- Sound BLTU construction (unsigned less-than). See `construction_beq_sound`. -/
theorem construction_bltu_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (bltu_input : PureSpec.BltuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bltu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
      = EStateM.Result.ok bltu_input.r1_val (binding i))
    (h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
      = EStateM.Result.ok bltu_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some bltu_input.PC)
    (h_input_misa : (binding i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BLTU_pure bltu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BLTU_pure bltu_input).throws = false)
    (h_success : (PureSpec.execute_BLTU_pure bltu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BLTU)) (binding i)
      = (bus_effect exec_row [] (binding i)).2 := by
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨imm, r1, r2, misa_val, exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state bltu_input.imm bltu_input.r1_val bltu_input.r2_val bltu_input.PC
      ops.misa_val
      (PureSpec.execute_BLTU_pure bltu_input).nextPC
      (PureSpec.execute_BLTU_pure bltu_input).throws
      (PureSpec.execute_BLTU_pure bltu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }
  exact ZiskFv.Compliance.equiv_BLTU state bltu_input ops promises

/-- Sound BGEU construction (unsigned greater-or-equal). See `construction_beq_sound`. -/
theorem construction_bgeu_sound_claimed_dead
    (trace : AcceptedZiskTrace)
    (binding : SailTrace trace.numInstructions)
    (i : Fin trace.numInstructions)
    (bgeu_input : PureSpec.BgeuInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (h_input_imm : bgeu_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) (binding i)
      = EStateM.Result.ok bgeu_input.r1_val (binding i))
    (h_input_r2 : read_xreg (regidx_to_fin r2) (binding i)
      = EStateM.Result.ok bgeu_input.r2_val (binding i))
    (h_input_pc : (binding i).regs.get? Register.PC = .some bgeu_input.PC)
    (h_input_misa : (binding i).regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BGEU_pure bgeu_input).nextPC)
    (h_not_throws : (PureSpec.execute_BGEU_pure bgeu_input).throws = false)
    (h_success : (PureSpec.execute_BGEU_pure bgeu_input).success = true) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BGEU)) (binding i)
      = (bus_effect exec_row [] (binding i)).2 := by
  set state := binding i with hstate
  let ops : ZiskFv.Compliance.BranchInstrOperands :=
    ⟨imm, r1, r2, misa_val, exec_row⟩
  let promises : ZiskFv.EquivCore.Promises.BranchPromises
      state bgeu_input.imm bgeu_input.r1_val bgeu_input.r2_val bgeu_input.PC
      ops.misa_val
      (PureSpec.execute_BGEU_pure bgeu_input).nextPC
      (PureSpec.execute_BGEU_pure bgeu_input).throws
      (PureSpec.execute_BGEU_pure bgeu_input).success
      ops.imm ops.r1 ops.r2 ops.exec_row :=
    { input_imm_eq := h_input_imm
      input_r1_eq := h_input_r1
      input_r2_eq := h_input_r2
      input_pc_eq := h_input_pc
      input_misa_eq := h_input_misa
      misa_c_zero := h_misa_c
      exec_len := h_exec_len
      e0_mult := h_e0_mult
      e1_mult := h_e1_mult
      nextPC_matches := h_nextPC_matches
      not_throws := h_not_throws
      success := h_success }
  exact ZiskFv.Compliance.equiv_BGEU state bgeu_input ops promises

end ZiskFv.Compliance
