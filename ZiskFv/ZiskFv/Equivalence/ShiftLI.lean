import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Fundamentals.Execution
import ZiskFv.Spec.ShiftLI
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.RV64D.slliw
import ZiskFv.RV64D.BusEffect

/-!
End-to-end theorem for RV64 SLLIW (Phase 3A H2b — `ShiftArchetype`
sibling, W-variant immediate).

Mirrors `Equivalence.Shift` for SLLW, with the Sail instruction
constructor swapped from `.RTYPEW (r2, r1, rd, ropw.SLLW)` to
`.SHIFTIWOP (shamt, r1, rd, sopw.SLLIW)` (no `r2` register read — the
shift amount is an immediate). The Main-AIR compositional lemma is the
`ShiftArchetype` m32=1 instantiation at `OP_SLL_W` (same opcode as
SLLW — the bus shape doesn't distinguish register vs immediate shift
source).

Bus shape (a): register-read (r1) + register-write (rd), same as SLLW
modulo the dropped r2-read.

NOTE: SLLIW's execution bus actually has only **one** source-register
read (r1) versus SLLW's two (r1, r2). The Main AIR row still emits the
same two-entry execution bus (read PC + write nextPC), but the
memory-bus rd-write structure matches SLLW: `e2.ptr = rd, e2.x*` carry
the 64-bit result. The `bus_effect_matches_sail_alu_rrw` lemma is
shape-(a) and takes three memory entries `[e0, e1, e2]` where `e0/e1`
are the source reads (mapped to register-file source addresses) and
`e2` is the destination write. For SLLIW we pass `e0` as an arbitrary
register-read entry at address-space 1 (matches the Main-AIR's
emission of the r1 read; the shamt source slot is populated with the
immediate as a constant, which the memory bus represents as a
second-source no-op read entry).
-/

namespace ZiskFv.Equivalence.ShiftLI

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Spec.ShiftLI

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Circuit-level SLLIW theorem.** Given the SLLIW-mode Main
    constraints (including `m32 = 1`) and the bus-match to a secondary
    entry, the entry carries zero high lanes. Direct instantiation of
    `ShiftArchetype`'s m32=1 macro at `OP_SLL_W`. -/
theorem equiv_SLLIW
    (_rs1 : Fin 32) (_state : RV64State)
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (bus_entry : OperationBusEntry FGL)
    (h_circuit : slliw_circuit_holds m r_main bus_entry) :
    bus_entry.a_hi = 0 ∧ bus_entry.b_hi = 0 :=
  slliw_compositional m r_main bus_entry h_circuit

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 SLLIW reduces to the pure-function block. Wraps
    `PureSpec.execute_SHIFTIWOP_slliw_pure_equiv`. -/
theorem equiv_SLLIW_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slliw_input.r1_val state)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slliw_input.PC) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = let slliw_output := PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input
        (do
          Sail.writeReg Register.nextPC slliw_output.nextPC
          match slliw_output.rd with
            | .some (rd, rd_val) => write_xreg rd rd_val
            | .none => pure ()
          pure (ExecutionResult.Retire_Success ())) state :=
  PureSpec.execute_SHIFTIWOP_slliw_pure_equiv
    slliw_input r1 rd h_input_r1 h_input_rd h_input_pc

/-- **Metaplan theorem.** Sail's `execute_instruction` on an RV64
    SLLIW equals the state computed by applying `bus_effect` to the
    circuit's execution + memory bus rows.

    Same bus-shape as SLLW (shape (a) — `bus_effect_matches_sail_alu_rrw`):
    two-entry exec bus + three-entry memory bus `[source, source, dst]`.
    No `h_bus_execute_matches_sail` parameter remains. -/
theorem equiv_SLLIW_metaplan
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (slliw_input : PureSpec.SlliwInput)
    (r1 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok slliw_input.r1_val state)
    (h_input_rd : slliw_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some slliw_input.PC)
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC)
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
      (match (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).rd with
        | .some (rd, rd_val) => write_xreg rd rd_val
        | .none => pure ())) :
    execute_instruction
      (instruction.SHIFTIWOP (slliw_input.shamt, r1, rd, sopw.SLLIW)) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  rw [equiv_SLLIW_sail state slliw_input r1 rd
        h_input_r1 h_input_rd h_input_pc]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_alu_rrw
        state exec_row e0 e1 e2
        (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).nextPC
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
        h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as]
  rw [h_rd_match]
  simp only [bind, pure, EStateM.bind, EStateM.pure]
  rcases (PureSpec.execute_SHIFTIWOP_slliw_pure slliw_input).rd with _ | ⟨r, v⟩ <;> rfl

end ZiskFv.Equivalence.ShiftLI
