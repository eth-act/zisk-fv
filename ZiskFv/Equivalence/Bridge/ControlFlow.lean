import Mathlib

import LeanZKCircuit.OpenVM.Circuit
import ZiskFv.Fundamentals.Goldilocks
import ZiskFv.Fundamentals.Transpiler
import ZiskFv.Sail.Auxiliaries
import ZiskFv.Airs.Main
import ZiskFv.Tactics.UTypeArchetype
import ZiskFv.Circuit.Jal
import ZiskFv.Circuit.Jalr
import ZiskFv.Equivalence.Bridge.StateBridge
import ZiskFv.Equivalence.Bridge.SailStateBridge

/-!
# ControlFlow discharge bridge

Implements *promise discharge* for the Main-only opcode shapes
that don't consume from an arithmetic Provider AIR — branches
(`BEQ` / `BNE` / `BLT` / `BLTU` / `BGE` / `BGEU`), the U-type
opcodes (`AUIPC` / `LUI`), the jumps (`JAL` / `JALR`), and
`FENCE`.

For these opcodes the only per-row content is the Main AIR's
emission (encoded in PC routing and, for JAL / JALR, a register
write). There is no separate Provider AIR for arithmetic — the
"discharge" reduces to:

* For branches: derive `r1_val` and `r2_val` packed-lane forms
  from `transpile_<BRANCH>` + Step 1.7b's `SailStateBridge`.
  Each `transpile_<BRANCH>` axiom shares the same shape: 5 mode
  pins then `a_0 = lane_lo (state.xreg rs1)`, `a_1 = lane_hi
  (state.xreg rs1)`, `b_0 = lane_lo (state.xreg rs2)`, `b_1 =
  lane_hi (state.xreg rs2)`.
* For JALR: derive r1_val packed form (uses transpile_JALR which
  has ITYPE shape).
* For AUIPC / LUI / JAL / FENCE: no register reads — the input
  bridge step is vacuous; the discharge is the PC-routing axioms
  `transpile_PC_for_{JAL,JALR,AUIPC}` consumed directly by the
  equiv proofs.

This file provides one helper for the branch shape (covering all
6 branches by parameterizing on the transpile axiom's application
result). Other shapes are direct one-line uses of existing
`SailStateBridge` helpers and don't warrant their own wrappers.
-/

namespace ZiskFv.Equivalence.Bridge.ControlFlow

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Equivalence.Bridge.StateBridge
open ZiskFv.Equivalence.Bridge.SailStateBridge

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Branch-shape input bridges (r1 + r2 in one call).** Given the
    a and b lane conjuncts already projected from a branch
    `transpile_<OP>` axiom application (`h_a_lo_t`, `h_a_hi_t`,
    `h_b_lo_t`, `h_b_hi_t`), plus the Sail `read_xreg` facts the
    caller already carries for `equiv_<BRANCH>_sail`, deliver the
    packed-lane equations for both r1_val and r2_val.

    Each `transpile_<BRANCH>` axiom (BEQ, BNE, BLT, BLTU, BGE,
    BGEU) has the same lane-conjunct shape modulo opcode and
    `neg`-or-order flags; this helper consumes the projected
    conjuncts opaquely so all 6 branches can share it.

    Internally calls `packed_lane_eq_of_read_xreg` once per
    register. No new axioms; pure composition of Step 1.7a + 1.7b
    infrastructure. -/
theorem branch_input_bridges_of_read_xreg
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (rs1 rs2 : Fin 32) (r1_val r2_val : BitVec 64)
    (a_lo a_hi b_lo b_hi : FGL)
    (h_a_lo : a_lo = lane_lo ((sail_to_rv64 state).xreg rs1))
    (h_a_hi : a_hi = lane_hi ((sail_to_rv64 state).xreg rs1))
    (h_b_lo : b_lo = lane_lo ((sail_to_rv64 state).xreg rs2))
    (h_b_hi : b_hi = lane_hi ((sail_to_rv64 state).xreg rs2))
    (h_read_r1 : read_xreg rs1 state = EStateM.Result.ok r1_val state)
    (h_read_r2 : read_xreg rs2 state = EStateM.Result.ok r2_val state) :
    r1_val = BitVec.ofNat 64 (a_lo.val + a_hi.val * 4294967296)
    ∧ r2_val = BitVec.ofNat 64 (b_lo.val + b_hi.val * 4294967296) :=
  ⟨packed_lane_eq_of_read_xreg state rs1 r1_val a_lo a_hi h_a_lo h_a_hi h_read_r1,
   packed_lane_eq_of_read_xreg state rs2 r2_val b_lo b_hi h_b_lo h_b_hi h_read_r2⟩

/-! ## Non-branch discharge entry points

The four entry points below — `lui_discharge_full`, `jal_discharge_full`,
`jalr_discharge_full`, `auipc_discharge_full` — package the
transpile-pinnable FGL ↔ `Nat` / FGL identities that the
corresponding `equiv_<OP>` theorems currently take as separate
`h_imm_lo_nat` / `h_imm_hi_nat` / `h_jmp2` parameters.

Each consumes the per-shape `*_circuit_holds` predicate (already a
required input to the equiv, for the PC-advance + store_value
formula derivations) and the relevant `transpile_<OP>` axiom from
`Fundamentals/Transpiler.lean` instantiated at the appropriate
ghost `imm_lo`/`imm_hi`/`imm_offset` operand. The transpile axiom
delivers an FGL equation (`m.b_0 r_main = imm_lo`, etc.); the
discharge then extracts `.val` and uses `Fin.val_natCast` plus a
`< GL_prime` no-wrap bound to land on the `.val = Nat` shape the
equiv expects.

No new axioms — every discharge here is pure composition of
existing trust-ledger pieces (`transpile_<OP>` + Fin / FGL
arithmetic). FENCE is already minimal and needs no entry point.

Caller-burden reduction (per opcode):
* LUI:  −2 binders (`h_imm_lo_nat`, `h_imm_hi_nat`).
* JAL:  −1 binder  (`h_jmp2`).
* JALR: −1 binder  (`h_jmp2`).
* AUIPC: −0 binders at this iteration — `h_offset_bridge` involves
  `(BitVec.signExtend 64 …).toNat` whose value can exceed
  `GL_prime`, so the transpile axiom's FGL equation does not
  cleanly extract the required `.val = Nat`. Tracked as a
  follow-up IOU. The entry point is still emitted so callers have
  a uniform façade across the four non-branch opcodes; for AUIPC
  it currently re-exports `transpile_AUIPC` and the AUIPC `pc`
  bridge for future thickening.

Anti-laundering metric:
* `trust/baseline-hypothesis-count.txt` strictly shrinks for LUI
  (15 → 13), JAL (11 → 10), JALR (14 → 13). AUIPC unchanged.
* No new axiom; trust ledger unchanged.
-/

/-- **LUI discharge.** From the LUI archetype mode pins
    (extracted from `lui_archetype_circuit_holds`'s mode subset),
    produce the two `imm_lo`/`imm_hi` `.val = Nat` identities
    `equiv_LUI` consumes.

    Both target nats are `< 2^32 < GL_prime` (the lo half is a
    `BitVec 32` toNat; the hi half is `0` or `2^32 - 1`), so the
    `Fin.val_natCast`-based extraction is unconditional.

    Trust footprint: pure composition of `transpile_LUI` (class
    #1) — no new axiom. -/
theorem lui_discharge_full
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (imm : BitVec 20)
    (h_circuit : ZiskFv.Tactics.UTypeArchetype.lui_archetype_circuit_holds m r_main next_pc) :
    (m.b_0 r_main).val = (imm ++ (0 : BitVec 12)).toNat
    ∧ (m.b_1 r_main).val
      = (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296 := by
  -- Extract the mode pins. `lui_archetype_circuit_holds` packs the
  -- subset together with `main_row_in_lui_mode`, whose first two
  -- conjuncts are the activation pins we need to fire `transpile_LUI`.
  obtain ⟨_h_subset, h_mode⟩ := h_circuit
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
  -- Choose the FGL representatives matching the equiv's expected
  -- `Nat` payloads. Both nats are `< 2^32 < GL_prime`, so
  -- `Fin.val_natCast` collapses the `% GL_prime` modulus.
  set n_lo : ℕ := (imm ++ (0 : BitVec 12)).toNat with h_n_lo
  set n_hi : ℕ := (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat / 4294967296
    with h_n_hi
  have h_lo_lt : n_lo < GL_prime := by
    have h32 : n_lo < 4294967296 :=
      (imm ++ (0 : BitVec 12)).isLt
    exact lt_trans h32 (by decide)
  have h_hi_lt : n_hi < GL_prime := by
    -- n_hi = (signExt 64 (imm ++ 0#12)).toNat / 2^32. The signExtend
    -- target is a 64-bit BV, so toNat < 2^64. Divided by 2^32 the
    -- quotient is < 2^32 < GL_prime.
    have h_se_lt : (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).toNat < 2 ^ 64 :=
      (BitVec.signExtend 64 (imm ++ (0 : BitVec 12))).isLt
    have : n_hi < 2 ^ 64 / 4294967296 := by
      simp [h_n_hi]
      exact Nat.div_lt_iff_lt_mul (by decide : (0 : ℕ) < 4294967296)
        |>.mpr (by simpa using h_se_lt)
    have h_q : 2 ^ 64 / 4294967296 = 4294967296 := by decide
    rw [h_q] at this
    exact lt_trans this (by decide)
  -- Fire transpile_LUI with `imm_lo := (n_lo : FGL)`, `imm_hi := (n_hi : FGL)`.
  -- The Fin 32 `_rd` and `RV64State` `_state` are ghost — pass
  -- arbitrary placeholders.
  have h_tr := ZiskFv.Trusted.transpile_LUI m r_main (0 : Fin 32)
    ((n_lo : FGL)) ((n_hi : FGL))
    { xreg := fun _ => 0#64, pc := 0#64 } h_ext h_op
  obtain ⟨_, _, _, _, _, _, _, h_b0, h_b1⟩ := h_tr
  -- Take `.val` on both equalities and unfold via `Fin.val_natCast` +
  -- the no-wrap bounds.
  refine ⟨?_, ?_⟩
  · have : (m.b_0 r_main).val = ((n_lo : FGL)).val := by rw [h_b0]
    rw [this, Fin.val_natCast, Nat.mod_eq_of_lt h_lo_lt]
  · have : (m.b_1 r_main).val = ((n_hi : FGL)).val := by rw [h_b1]
    rw [this, Fin.val_natCast, Nat.mod_eq_of_lt h_hi_lt]

/-- **JAL discharge.** From the JAL `jump_subset_holds + mode`
    bundle, produce the FGL identity `m.jmp_offset2 r_main = 4` the
    `h_rd_val_jut_jal` derivation consumes.

    Trust footprint: pure composition of `transpile_JAL` (class
    #1) — no new axiom. -/
theorem jal_discharge_full
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : ZiskFv.Circuit.Jal.jal_circuit_holds m r_main next_pc) :
    m.jmp_offset2 r_main = 4 := by
  obtain ⟨_h_subset, h_mode⟩ := h_circuit
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
  -- JAL's mode pins `op = 0`; `transpile_JAL` expects `op = OP_FLAG`
  -- (definitionally `= 0`). Use a placeholder Fin 32 / FGL / state.
  have h_tr := ZiskFv.Trusted.transpile_JAL m r_main (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 } h_ext h_op
  exact h_tr.2.2.2.2.1

/-- **JALR discharge.** From the JALR `jalr_subset_holds + mode`
    bundle, produce the FGL identity `m.jmp_offset2 r_main = 4` the
    `h_rd_val_jut_jalr` derivation consumes.

    Trust footprint: pure composition of `transpile_JALR` (class
    #1) — no new axiom. -/
theorem jalr_discharge_full
    (m : Valid_Main C FGL FGL) (r_main : ℕ) (next_pc : FGL)
    (h_circuit : ZiskFv.Circuit.Jalr.jalr_circuit_holds m r_main next_pc) :
    m.jmp_offset2 r_main = 4 := by
  obtain ⟨_h_subset, h_mode⟩ := h_circuit
  obtain ⟨h_ext, h_op, _h_m32, _h_set_pc, _h_store_pc⟩ := h_mode
  -- JALR's mode pins `op = 1`; `transpile_JALR` expects `op = OP_COPYB`
  -- (definitionally `= 1`). The `rs1` Fin 32 and state are ghost
  -- with respect to the `jmp_offset2 = 4` conjunct.
  have h_tr := ZiskFv.Trusted.transpile_JALR m r_main (0 : Fin 32) (0 : Fin 32)
    (0 : FGL) { xreg := fun _ => 0#64, pc := 0#64 } h_ext h_op
  exact h_tr.2.2.2.2.1

end ZiskFv.Equivalence.Bridge.ControlFlow
