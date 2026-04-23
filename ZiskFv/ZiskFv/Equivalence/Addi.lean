import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Spec.Addi
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.addi
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.ALUITypeArchetype

/-!
End-to-end theorem for RV64 ADDI (Phase 3C T-IT).

Mirrors `Equivalence.Sub` / `Equivalence.And` shape with
`rop.<OP> → iop.ADDI` on the Sail side and `OP_SUB/AND → OP_ADD`
on the circuit side. ADDI shares `OP_ADD` with ADD — the piggyback
is transpiler-internal; the Main-AIR row carries the sign-extended
12-bit immediate through `(b_lo, b_hi)` rather than from `xreg(rs2)`.

**Bus-shape note (inherited from SLLI precedent).** The metaplan
hypotheses still take three memory-bus entries `[e0, e1, e2]` even
though an ITYPE microinstruction reads only one register. The
Phase 3A H-track chose to keep the `bus_effect_matches_sail_alu_rrw`
interface uniform for all register-write ALU ops; a Phase 4 audit
either justifies the second read as redundant or introduces a
dedicated 1-read-1-write bus-emission lemma.
-/

namespace ZiskFv.Equivalence.Addi

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Addi
open ZiskFv.Tactics.ALURTypeArchetype
open ZiskFv.Tactics.ALUITypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level ADDI theorem.** Main's packed `c` equals the bus
    entry's packed `c` lanes. Wraps `Spec.Addi.addi_compositional`. -/
theorem equiv_ADDI
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : addi_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  addi_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDI
    reduces to `PureSpec.execute_ITYPE_addi_pure`. Wraps
    `PureSpec.execute_ITYPE_addi_pure_equiv`. -/
theorem equiv_ADDI_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = let addi_output := PureSpec.execute_ITYPE_addi_pure addi_input
        (do
          Sail.writeReg Register.nextPC addi_output.nextPC
          match addi_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_addi_pure_equiv
    addi_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64 ADDI
    equals `(bus_effect exec_row mem_row state).2`. Uses shape (a)
    bus-emission (`bus_effect_matches_sail_alu_rrw`). -/
theorem equiv_ADDI_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addi_input : PureSpec.AddiInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addi_input.r1_val state)
    (h_input_imm : addi_input.imm = imm)
    (h_input_rd : addi_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addi_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_match :
      (if h : Transpiler.wrap_to_regidx e2.ptr = 0 then
        (pure () : SailM Unit)
      else
        let val := U64.toBV #v[e2.x0, e2.x1, e2.x2, e2.x3,
                                e2.x4, e2.x5, e2.x6, e2.x7]
        let reg_idx : Finset.Icc 1 31 :=
          ⟨ (Transpiler.wrap_to_regidx e2.ptr).val, by simp; omega ⟩
        write_xreg reg_idx val)
      =
      (match (PureSpec.execute_ITYPE_addi_pure addi_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ITYPE (imm, r1, rd, iop.ADDI))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_ADDI_sail state addi_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addi_pure addi_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_ITYPE_addi_pure addi_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Addi
