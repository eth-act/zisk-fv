import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.Addiw
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.addiw
import ZiskFv.RV64D.BusEffect
import ZiskFv.Tactics.RTypeWArchetype

/-!
End-to-end theorem for RV64 ADDIW (Phase 3C T-W). Sibling of
`Equivalence.Addw` for the immediate-source variant.

Mirrors `Equivalence.ShiftLI` for SLLIW's single-reg-plus-imm shape,
and `Equivalence.Addw` for the RTYPEW Sail triple. The Sail
instruction constructor is `instruction.ADDIW (imm, r1, rd)` (no
`r2` — the shift / imm source is encoded in the immediate). Bus
shape (a) — two-entry execution bus + three-entry memory bus
`[source, source, dst]`.

Routing note. ADDIW and ADDW share `OP_ADD_W` + `m32 = 1` at the
operation-bus layer; they differ only in the transpile axiom's
`b`-lane shape (reg for ADDW, imm for ADDIW).
-/

namespace ZiskFv.Equivalence.Addiw

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.Addiw
open ZiskFv.Tactics.RTypeWArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level ADDIW theorem (Phase 3C T-W).** Main's packed
    `c` equals the bus entry's packed `c` lanes. Wraps
    `Spec.Addiw.addiw_compositional`. -/
theorem equiv_ADDIW
    (_rs1 _rd : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : addiw_circuit_holds m r_main bus_entry) :
    main_c_packed m r_main
      = bus_entry.c_lo + bus_entry.c_hi * 4294967296 :=
  addiw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `execute_instruction` on an RV64 ADDIW
    reduces to `PureSpec.execute_ITYPE_addiw_pure`. Wraps
    `PureSpec.execute_ITYPE_addiw_pure_equiv`. -/
theorem equiv_ADDIW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addiw_input.r1_val state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addiw_input.PC) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = let addiw_output := PureSpec.execute_ITYPE_addiw_pure addiw_input
        (do
          Sail.writeReg Register.nextPC addiw_output.nextPC
          match addiw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_ITYPE_addiw_pure_equiv
    addiw_input r1 rd h_input_r1 h_input_imm h_input_rd h_input_pc

/-- **Metaplan theorem (Phase 3C T-W).** Sail's `execute_instruction`
    on an RV64 ADDIW equals `(bus_effect exec_row mem_row state).2`.
    Shape (a) — same bus skeleton as SLLIW. -/
theorem equiv_ADDIW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (addiw_input : PureSpec.AddiwInput)
    (r1 rd : regidx) (imm : BitVec 12)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok addiw_input.r1_val state)
    (h_input_imm : addiw_input.imm = imm)
    (h_input_rd : addiw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some addiw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC)
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
      (match (PureSpec.execute_ITYPE_addiw_pure addiw_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.ADDIW (imm, r1, rd))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_ADDIW_sail state addiw_input r1 rd imm
        h_input_r1 h_input_imm h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_ITYPE_addiw_pure addiw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_ITYPE_addiw_pure addiw_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.Addiw
