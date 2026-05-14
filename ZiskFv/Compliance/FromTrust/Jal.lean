import Mathlib

import ZiskFv.Equivalence.Jal
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_JAL` Compliance wrapper — ControlFlow non-branch (Step 4.2)

> **Status:** within-shape wrapper, derived mechanically from
> `FromTrust/Lui.lean` (Step 4.1.1). Lives outside the canonical
> surface so V1 anti-laundering metrics on the canonical theorem
> are unaffected.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_JAL` via
  `jal_discharge_lanes` (consumes `main_store_pc_emission_bundle`,
  trust class #4). Pre-discharged on the canonical surface.
* **Mode pins.** N/A on the provider side (no provider AIR). The
  Main-side mode pins (`m32 = 0`, `set_pc = 0`, `store_pc = 1`,
  `jmp_offset2 = 4`) come from `transpile_JAL` (class #1) — already
  consumed inside `equiv_JAL`'s proof.
* **Sign-witness pins.** N/A.
* **Range/bound.** Internalized by `equiv_JAL` via
  `memory_bus_entry_byte_range_perm_sound` (class #5b).
* **Operand bridges.** N/A (no register read).

## Anti-laundering report

* **Zero new axioms** — consumes `transpile_JAL` (class #1) plus
  `equiv_JAL`'s existing closure. Matches the per-AIR axiom map's
  0-new-axioms prediction for ControlFlow.
* **Caller-burden** structural-unpacking, parallel to LUI exemplar
  (+1 hypothesis from unpacking `h_circuit` into `h_main_active`,
  `h_main_op_jal`, `h_jal_subset`). At the global Compliance.lean
  level the burden strictly shrinks via shared `(main, ∀ r, ...)`
  parameters across the eleven ControlFlow opcodes.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Compliance wrapper for `equiv_JAL`.** Mirrors `equiv_LUI_from_trust`'s
    structure with `transpile_JAL` substituted for `transpile_LUI` and
    the JAL mode/subset definitions in place of LUI's. -/
theorem equiv_JAL_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (jal_input : PureSpec.JalInput)
    (imm : BitVec 21)
    (rd : regidx)
    (misa_val : RegisterType Register.misa)
    -- AIR validator + row index.
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e_rd : Interaction.MemoryBusEntry FGL)
    (nextPC_val : BitVec 64)
    -- Activation + opcode pins (Compliance ROM handshake).
    (h_main_active : m.is_external_op r_main = 0)
    (h_main_op_jal : m.op r_main = OP_FLAG)
    -- Per-row Main constraint bundle (universal-row Main validity).
    (h_jal_subset :
      ZiskFv.Airs.Main.jump_subset_holds m r_main next_pc)
    -- Sail-side state predicates (SPEC-PRE).
    (h_input_imm : jal_input.imm = imm)
    (h_input_rd : jal_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some jal_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- Bus-shape structural hypotheses — pass-through from `equiv_JAL`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = nextPC_val)
    (h_rd_mult : e_rd.multiplicity = 1) (h_rd_as : e_rd.as.val = 1)
    -- Happy-path hypotheses (ZisK SPEC-PRE: branch targets aligned).
    (h_not_throws : (PureSpec.execute_JAL_pure jal_input).throws = false)
    (h_success : (PureSpec.execute_JAL_pure jal_input).success = true)
    (h_nextPC_option :
      (PureSpec.execute_JAL_pure jal_input).nextPC = .some nextPC_val)
    (h_rd_idx : jal_input.rd = Transpiler.wrap_to_regidx e_rd.ptr)
    -- Range/no-wrap obligations.
    (h_pc_bound : jal_input.PC.toNat < GL_prime - 4)
    (h_lo_bound : (m.pc r_main + 4 : FGL).val < 4294967296)
    (h_pc_offset_lt_2_32 : (jal_input.PC + 4#64).toNat < 4294967296) :
    execute_instruction (instruction.JAL (imm, rd)) state
      = (bus_effect exec_row [e_rd] state).2 := by
  -- ============ Derive routing mode pins via `transpile_JAL` ============
  have h_tr := ZiskFv.Trusted.transpile_JAL m r_main (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 } h_main_active h_main_op_jal
  obtain ⟨h_m32, h_set_pc, h_store_pc, _, _, _, _, _, _⟩ := h_tr
  -- ============ Assemble `main_row_in_jal_mode` ============
  have h_jal_mode : ZiskFv.ZiskCircuit.Jal.main_row_in_jal_mode m r_main := by
    refine ⟨h_main_active, ?_, h_m32, h_set_pc, h_store_pc⟩
    -- `OP_FLAG := 0` definitionally; the mode predicate expects
    -- `m.op r_main = (0 : FGL)`.
    rw [h_main_op_jal]; rfl
  -- ============ Assemble `jal_circuit_holds` ============
  have h_circuit : ZiskFv.ZiskCircuit.Jal.jal_circuit_holds m r_main next_pc :=
    ⟨h_jal_subset, h_jal_mode⟩
  -- ============ Delegate to canonical `equiv_JAL` ============
  exact ZiskFv.Equivalence.Jal.equiv_JAL state jal_input imm rd misa_val
    exec_row e_rd nextPC_val m r_main next_pc
    h_input_imm h_input_rd h_input_pc h_input_misa h_misa_c
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_rd_mult h_rd_as h_not_throws h_success h_nextPC_option h_rd_idx
    h_circuit h_pc_bound h_lo_bound h_pc_offset_lt_2_32

end ZiskFv.Compliance
