import Mathlib

import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Interaction
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Circuit.Jalr
import ZiskFv.Airs.Main
import ZiskFv.Airs.OperationBus
import ZiskFv.Airs.BusEmission
import ZiskFv.Sail.jalr
import ZiskFv.Sail.BusEffect
import ZiskFv.Airs.BusHypotheses
import ZiskFv.Airs.OpBusEffect
import ZiskFv.Airs.OpBusHypotheses
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.MemoryBus.LaneMatch
import ZiskFv.Airs.MemoryBus.EntryRanges
import ZiskFv.Equivalence.Bridge.ControlFlow
import ZiskFv.Equivalence.RdValDerivation.JumpUType

/-!
End-to-end theorem for RV64 JALR. Combines:

* the trusted RV64 → Zisk transpilation contract
  (`ZiskFv.Trusted.transpile_JALR`),
* the compositional JALR spec (`ZiskFv.Circuit.Jalr.jalr_pc_advance`),
* the Sail pure-function equivalence
  (`PureSpec.execute_JALR_pure_equiv`, closed via the trusted
  `execute_JALR_pure_equiv_axiom` at `ZiskFv/RV64D/jalr.lean:67` —
  see `docs/fv/trusted-base.md` for the closure path),

into a canonical theorem:

* `equiv_JALR` — the canonical target shape:
  `execute_instruction (.JALR (imm, rs1, rd)) state
    = (bus_effect exec_row mem_row state).2`.

Like JAL (shape (c)), the bus-matching is discharged
internally via `bus_effect_matches_sail_jump_rrw`, which handles any
"two-exec-entry + one-rd-write-mem-entry" shape. JALR emits exactly
that shape under the archetype-validation contract in `transpile_JALR`
(internal-copyb, `store_pc = 1`, no operation-bus hop).
-/

namespace ZiskFv.Equivalence.Jalr

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.OperationBus
open ZiskFv.Circuit.Jalr

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Sail-level companion.** `LeanRV64D.execute_instruction` on an
    RV64 JALR reduces to the pure-function block supplied by
    `PureSpec.execute_JALR_pure`, given source-register readability
    (rs1), PC knowledge, misa, and ZisK-level privilege/PMA witnesses.

    Wraps `PureSpec.execute_JALR_pure_equiv`, which is closed via the
    trusted `execute_JALR_pure_equiv_axiom` (see `trusted-base.md`).
    The equivalence theorem below composes this with the shape-(c)
    bus-matching lemma. -/
theorem equiv_JALR_sail
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = let jalr_output := PureSpec.execute_JALR_pure jalr_input
        (do
          match jalr_output.nextPC with
            | .some nextPC => Sail.writeReg Register.nextPC nextPC
            | .none => pure ()
          match jalr_output.rd with
            | .some (reg, rd_val) => write_xreg reg rd_val
            | .none => pure ()
          if !jalr_output.success then
            pure (
              ExecutionResult.Memory_Exception (
                (virtaddr.Virtaddr (0xFFFFFFFFFFFFFFFE &&& (jalr_input.rs1_val +
                  BitVec.signExtend 64 jalr_input.imm))),
                (ExceptionType.E_Fetch_Addr_Align ())
              )
            )
          else
            (pure (ExecutionResult.Retire_Success ()))) state :=
  PureSpec.execute_JALR_pure_equiv jalr_input imm rs1 rd
    h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
    h_cur_privilege h_mseccfg

/-- **Canonical equivalence.** Sail's `execute_instruction` on an RV64
    JALR equals the state computed by applying `bus_effect` to the
    circuit's execution and memory bus rows.

    Every parameter classifies as one of {CIRCUIT-CONSTRAINT,
    LANE-MATCH, RANGE, TRANSPILE-BRIDGE, TRANSPILE-PIN} — no parameter
    asserts the spec output (`PC + 4`) directly; that equation is
    derived internally from circuit witnesses via the
    `RdValDerivation.JumpUType.h_rd_val_jut_jalr` discharge lemma.

    Composes `equiv_JALR_sail` with the shape-(c) bus-matching lemma
    `bus_effect_matches_sail_jump_rrw`. Unlike JAL, JALR does **not**
    raise `Assertion` on a misaligned target (its jump argument is
    pre-masked), so the `throws = false` path is trivially inhabited —
    no `h_not_throws` hypothesis is needed. -/
theorem equiv_JALR
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jalr_input : PureSpec.JalrInput)
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (misa_val : RegisterType Register.misa)
    (mseccfg : RegisterType Register.mseccfg)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_input_imm : jalr_input.imm = imm)
    (h_input_rd : jalr_input.rd = regidx_to_fin rd)
    (h_input_rs1 : read_xreg (regidx_to_fin rs1) state
      = EStateM.Result.ok jalr_input.rs1_val state)
    (h_input_pc : state.regs.get? Register.PC = .some jalr_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    (h_cur_privilege : Sail.readReg Register.cur_privilege state
      = EStateM.Result.ok Privilege.Machine state)
    (h_mseccfg : Sail.readReg Register.mseccfg state
      = EStateM.Result.ok mseccfg state)
    -- Shape-(c) structural bus hypotheses.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    -- Happy-path hypothesis: no alignment fault (ZisK enforces via
    -- the JALR_MASK operand in the transpiler).
    (h_success : (PureSpec.execute_JALR_pure jalr_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JALR_pure jalr_input).nextPC = .some nextPC_val)
    (h_rd_idx : jalr_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Discharge parameters
    (h_circuit : ZiskFv.Circuit.Jalr.jalr_circuit_holds m r_main next_pc)
    (h_lane_lo : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_lo m r_main e_rd)
    (h_lane_hi : ZiskFv.Airs.MemoryBus.store_pc_lanes_match_hi m r_main e_rd)
    (h_pc_bound : jalr_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jalr_input.PC + 4#64).toNat < 4294967296) :
    (do
        Sail.writeReg Register.nextPC (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
        LeanRV64D.Functions.execute (instruction.JALR (imm, rs1, rd))) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- Discharge `h_jmp2` via `transpile_JALR` (class #1).
  have h_jmp2 : m.jmp_offset2 r_main = 4 :=
    ZiskFv.Equivalence.Bridge.ControlFlow.jalr_discharge_full
      m r_main next_pc h_circuit
  have h_rd_val :=
    ZiskFv.Equivalence.RdValDerivation.JumpUType.h_rd_val_jut_jalr
      jalr_input.PC m r_main next_pc e_rd
      h_circuit h_jmp2 h_lane_lo h_lane_hi
      h_pc_bound h_lo_bound h_pc_offset_lt_2_32
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.2.1
      (ZiskFv.Airs.MemoryBus.memory_bus_entry_byte_range_perm_sound e_rd).2.2.2.2.2.2.2
  rw [equiv_JALR_sail state jalr_input imm rs1 rd misa_val mseccfg
        h_input_imm h_input_rd h_input_rs1 h_input_pc h_input_misa h_misa_c
        h_cur_privilege h_mseccfg]
  symm
  rw [ZiskFv.Airs.BusEmission.bus_effect_matches_sail_jump_rrw
        state exec_row e_rd nextPC_val
        h_exec_len h_e0_mult h_e1_mult h_nextPC_matches h_rd_mult h_rd_as]
  simp only [h_nextPC_option, h_success, Bool.not_true]
  -- From h_success (success = bit1_valid = true), derive !bit1_valid = false.
  have h_bit1_neg :
      (!BitVec.ofBool (jalr_input.rs1_val + BitVec.signExtend 64 jalr_input.imm)[1]! == 0#1)
      = false := by
    have h_s : (PureSpec.execute_JALR_pure jalr_input).success = true := h_success
    simp only [PureSpec.execute_JALR_pure] at h_s
    simp_all
  -- Unfold the pure spec and discharge the rd dite.
  simp only [PureSpec.execute_JALR_pure, h_rd_idx, h_bit1_neg]
  by_cases h_rd_zero : Transpiler.wrap_to_regidx e_rd.ptr = 0
  · simp only [h_rd_zero, decide_true, Bool.false_or, ↓reduceDIte,
               Bool.false_eq_true, if_false,
               bind, pure, EStateM.bind, EStateM.pure]
  · simp only [h_rd_zero, decide_false, Bool.or_false, ↓reduceDIte,
               Bool.false_eq_true, if_false,
               bind, pure, EStateM.bind, EStateM.pure]
    rw [h_rd_val]

/-! ## Misaligned-target companion

JALR differs from JAL at the alignment-check boundary: its jump argument
is pre-masked via `Sail.BitVec.update target 0 0#1`, which clears
bit-0 silently. Hence:

* Pure-spec output has only `success` — no `throws` field (jalr.lean:13-19).
* Bit-0 misaligned case **never fires** (cleared by the mask before the
  alignment check). No `_bit0` companion.
* Bit-1 misaligned case → `success = false` → Sail emits
  `Memory_Exception (Virtaddr (mask &&& (rs1_val + sext imm)),
  E_Fetch_Addr_Align)`.

The mask in the Memory_Exception's virtaddr is `0xFFFFFFFFFFFFFFFE`,
which equals `Sail.BitVec.update (rs1_val + sext imm) 0 0#1` (clearing
bit-0). The pure-spec uses the explicit `&&&` form, while the underlying
Sail uses the `update` form; both reduce to the same value, but the
pure-spec block from `equiv_JALR_sail` already exposes the `&&&` form. -/

end ZiskFv.Equivalence.Jalr
