import Mathlib

import ZiskFv.Equivalence.Auipc
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Airs.Main

/-!
# `equiv_AUIPC` Compliance wrapper — ControlFlow non-branch (Step 4.2)

> **Status:** within-shape wrapper, derived mechanically from
> `LuiExemplar.lean` (Step 4.1.1). Lives outside the canonical
> surface so V1 anti-laundering metrics on the canonical theorem
> are unaffected.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_AUIPC` via
  `auipc_discharge_lanes` (consumes `main_store_pc_emission_bundle`,
  trust class #4). Pre-discharged on the canonical surface.
* **Mode pins.** N/A on the provider side (no provider AIR). The
  Main-side mode pins come from `transpile_AUIPC` (class #1).
* **Sign-witness pins.** N/A.
* **Range/bound.** Internalized by `equiv_AUIPC`.
* **Operand bridges.** N/A (no register read; PC is a state value).

## Anti-laundering report

* **Zero new axioms** — consumes `transpile_AUIPC` (class #1) plus
  `equiv_AUIPC`'s existing closure. Matches per-AIR axiom map's
  0-new-axioms prediction.
* **Caller-burden** mirrors LUI's structural-unpacking pattern.
-/

namespace ZiskFv.Equivalence.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Tactics.UTypeArchetype

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_AUIPC`.** Mirrors
    `equiv_LUI_from_trust`'s structure with `transpile_AUIPC`
    substituted for `transpile_LUI` and AUIPC's mode/subset
    definitions in place of LUI's. -/
theorem equiv_AUIPC_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (auipc_input : PureSpec.AuipcInput)
    (imm : BitVec 20)
    (rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- AIR validator + row index.
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    -- Activation + opcode pins (Compliance ROM handshake).
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_auipc : m.op r_main = OP_FLAG)
    -- Per-row Main constraint bundle.
    (h_auipc_subset : auipc_subset_holds m r_main next_pc)
    -- Sail-side state predicates (SPEC-PRE).
    (h_input_imm : auipc_input.imm = imm)
    (h_input_rd : auipc_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some auipc_input.PC)
    -- Bus-shape structural hypotheses — pass-through from `equiv_AUIPC`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    (h_nextPC_eq :
      (PureSpec.execute_AUIPC_pure auipc_input).nextPC = nextPC_val)
    (h_rd_idx : auipc_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Range/no-wrap obligations.
    (h_no_wrap : auipc_input.PC.toNat
      + (BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < GL_prime)
    (h_lo_bound : (m.pc r_main + m.jmp_offset2 r_main : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 :
      (auipc_input.PC + BitVec.signExtend 64 (auipc_input.imm ++ (0 : BitVec 12))).toNat
        < 4294967296) :
    execute_instruction (instruction.UTYPE (imm, rd, uop.AUIPC)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- ============ Derive routing mode pins via `transpile_AUIPC` ============
  have h_tr := ZiskFv.Trusted.transpile_AUIPC m r_main (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 }
    h_main_active h_main_op_auipc
  obtain ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _, _, _⟩ := h_tr
  -- ============ Assemble `main_row_in_auipc_mode` ============
  have h_auipc_mode : main_row_in_auipc_mode m r_main := by
    refine ⟨h_main_active, ?_, h_m32, h_set_pc, h_store_pc⟩
    rw [h_main_op_auipc]; rfl
  -- ============ Assemble `auipc_archetype_circuit_holds` ============
  have h_circuit : auipc_archetype_circuit_holds m r_main next_pc :=
    ⟨h_auipc_subset, h_auipc_mode⟩
  -- ============ Delegate to canonical `equiv_AUIPC` ============
  exact ZiskFv.Equivalence.Auipc.equiv_AUIPC state auipc_input imm rd
    exec_row e_rd nextPC_val m r_main next_pc
    h_input_imm h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_nextPC_eq h_rd_idx
    h_circuit h_no_wrap h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Equivalence.Compliance
