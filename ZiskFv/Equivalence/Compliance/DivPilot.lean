import Mathlib

import ZiskFv.Equivalence.Div
import ZiskFv.Equivalence.Bridge.Arith
import ZiskFv.Airs.Arith.Ranges
import ZiskFv.Airs.Arith.Bridge1
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus.MemBridge
import ZiskFv.Fundamentals.PackedBitVec.SignedChunkLift

/-!
# `equiv_DIV` Compliance pilot (Step 4, single-opcode trust-discharge)

> **Status:** PILOT. Not part of the canonical `equiv_<OP>` surface
> (lives outside `ZiskFv/Equivalence/Div.lean`). Demonstrates, for a
> *single* opcode, the shape of a future `Compliance.lean` caller
> that supplies `Valid_Main`, `Valid_ArithDiv`, op-bus permutation-
> soundness inputs, and per-AIR universal-row validity, and DERIVES
> the seventeen structural binders that `equiv_DIV` currently accepts
> directly.
>
> The wrapper `equiv_DIV_from_trust` below consumes:
>
> * Five new trust-ledger consequences (already shipped on this
>   branch): `op_bus_perm_sound_ArithDiv` (PHASE A's OpBus axiom),
>   `arith_table_op_div_rem_signed_d_sign_pin` (existing class #6),
>   plus this branch's three additions
>   `arith_table_op_div_rem_signed_mode_pin` (class #6, GAP-M),
>   `arith_div_remainder_bound` (class #6, GAP-C), and the
>   literal-corrected `op_bus_perm_sound_ArithDiv{,Secondary}`
>   (GAP-O: bus literals 0xb8..0xbf per `zisk/pil/operations.pil:79`
>   replacing the earlier 0xa0..0xa7 misencoding).
>
> Closed gaps:
> * **GAP-M** — `h_sext`/`h_m32`/`h_div` derived from
>   `arith_table_op_div_rem_signed_mode_pin v r_a h_op_arith`.
> * **GAP-O** — `v.op r_a = 186` derived from the `matches_entry`
>   op-slot equality plus `m.op r_main = OP_DIV` (the bus opcode
>   equals the arith-table opcode after the literal correction;
>   both columns are the same column on the bus side).
> * **GAP-C** — `h_r_abs`/`h_r_sign` derived from
>   `arith_div_remainder_bound v r_a h_sext h_m32 h_div h_op_arith`
>   composed with the operand TRANSPILE-BRIDGE equations
>   `h_op1`/`h_op2`.
> * **GAP-A (lo)** — `h_byte_lo` derived from
>   `main_external_arith_emission_bundle` (class #4 axiom) composed
>   with the `matches_entry` c_lo projection from `h_match_primary`
>   (FGL → ℕ lift via the chunk-range axiom on `v.a_0`, `v.a_1`).
> * **GAP-A (hi)** — `h_byte_hi` derived from
>   `main_external_arith_emission_bundle` (c_hi byte pack →
>   `m.c_1 r_main`) composed with the `matches_entry` c_hi
>   projection (`m.c_1 r_main = v.bus_res1 r_a`) and the new
>   `div_bus_res1_eq_a_hi` bridge (`bus_res1 = v.a_2 + v.a_3 * 65536`
>   under DIV-primary mode pins). The required mode pins
>   `main_div = 1`, `main_mul = 0` come from this branch's new
>   class-#6b axiom `arith_table_op_div_rem_main_selector_pin`;
>   `sext = 0`, `m32 = 0` from the existing mode-triple axiom.
>   Constraint 46 is accepted as an explicit row-shape obligation
>   (`h_c46`), in the same constructibility category as `h_chain`.
>
> Remaining caller obligations (NOT closed by this branch):
> * **GAP-B** (`h_op1` / `h_op2`) — connects Sail register reads
>   (`r1_val`/`r2_val`) to ArithDiv's `c[] - np·2^64` /
>   `b[] - nb·2^64` signed-packed columns. The unsigned form
>   `r.toNat = packed4 c[]` follows from OpBus + `transpile_DIV` +
>   `SailStateBridge.packed_lane_eq_of_read_xreg`; the signed lift
>   requires linking the sign-witness `np`/`nb` to the MSB of `r1`/
>   `r2`. The prior pilot report's "pure-Lean bridge work — no new
>   axiom" framing under-estimated this: `na = a[3].msb` is NOT a
>   free-standing PIL constraint; it is implicit in the consistency
>   of the carry-chain signed-DIV identity (derivable via Euclidean
>   uniqueness on `div_signed_chain_witnesses`), or alternatively
>   could be pinned by a new class-#6b axiom directly. Left as a
>   follow-up that legitimately requires either route.
>
> Anti-laundering: this PR adds ONE new class-#6b axiom in
> `Airs/Arith/Ranges.lean` (`arith_table_op_div_rem_main_selector_pin`,
> PIL-cited to `arith.pil:286-287` + the row-type table at
> `arith.pil:222-234`), pinning the `main_mul`/`main_div` selector
> columns from the `op` literal — same trust kind as the existing
> mode-triple pin (`arith_table_op_div_rem_signed_mode_pin`),
> narrower covering set (single column pair, single op-value
> instance). Net change to the pilot's caller burden: drop
> `h_byte_hi` (–1 promise hypothesis); add `h_c46` (+1
> constructibility obligation, same category as `h_chain`).
> Net –1 promise hypothesis on the trust-burden ledger.
-/

namespace ZiskFv.Equivalence.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.ArithDiv
open ZiskFv.Airs.OperationBus
open ZiskFv.PackedBitVec.SignedChunkLift

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_DIV`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `div_input`, `r1`, `r2`, `rd`)
       and the structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    2. The two AIR validators with their selected row indices
       (`m : Valid_Main`, `r_main`, `v : Valid_ArithDiv`, `r_a`).
       In Compliance.lean's downstream caller these collapse into
       a single `(m, v)` shared across every per-opcode invocation;
       per-opcode work supplies `r_main` (from Main's program counter
       handshake) and `r_a` (which a follow-up will derive existentially
       from OpBus instead of accepting as a parameter).
    3. The two activation pins (`h_main_active`, `h_main_op_div`).
       In Compliance.lean these are themselves derived from the
       Main AIR's ROM-handshake on the row that hosts the DIV
       instruction.
    4. The structural exec/mem row shape — exactly what
       `equiv_DIV` already accepts; passed through unchanged
       (these are *constructibility* obligations on the bus
       protocol, NOT promise hypotheses on Sail outputs).
    5. The SPEC-PRE preconditions on the Sail input
       (`h_input_r1`, `h_input_r2`, `h_input_rd`, `h_input_pc`,
       `h_op2_ne`, `h_no_overflow`).
    6. The universal-per-row constructibility obligations (the
       per-row Arith-AIR constraints: `h_chain`, `h_na_bool`,
       `h_nb_bool`, `h_nr_bool`, `h_np_xor`). In Compliance.lean
       these collapse into a single
       `∀ r, arith_div_row_well_formed v r`.
    7. The two remaining promise hypotheses (`h_byte_lo`/`h_byte_hi`
       for GAP-A, `h_op1`/`h_op2` for GAP-B) plus `h_rd_idx`.

    Derived internally (NOT caller-supplied):
    * `h_op_arith : v.op r_a = 186 ∨ v.op r_a = 187` — from the
      `matches_entry` op-slot equality (op-bus permutation).
    * `h_sext`, `h_m32`, `h_div` — from
      `arith_table_op_div_rem_signed_mode_pin` (GAP-M).
    * `h_nr_pin` — from
      `arith_table_op_div_rem_signed_d_sign_pin` (existing).
    * `h_r_abs`, `h_r_sign` — from `arith_div_remainder_bound`
      (GAP-C) composed with `h_op1`/`h_op2`.

    After this branch the wrapper carries 37 binders / 24
    hypotheses (vs. 38/25 at HEAD and 43/32 on `equiv_DIV`); the
    GAP-A hi-lane promise is now discharged via the new class-#6b
    selector-pin axiom + Bridge1; GAP-B (`h_op1`/`h_op2`) remains
    the sole surfaced promise-hypothesis follow-up. The narrowing
    of `h_main_op_div` to `OP_DIV` (was `OP_DIV ∨ OP_REM`)
    eliminates the vestigial REM dispatch path; a parallel pilot
    `equiv_REM_from_trust` is the proper future home for REM
    discharge. -/
theorem equiv_DIV_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (div_input : PureSpec.DivInput)
    (r1 r2 rd : regidx)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- ============ DISCHARGE INPUTS ============
    -- AIR validators + row indices. Compliance.lean shares (m, v)
    -- across opcodes; per-opcode caller supplies the row indices.
    (m : Valid_Main C FGL FGL) (r_main : ℕ)
    (v : Valid_ArithDiv C FGL FGL) (r_a : ℕ)
    -- Activation / opcode pin on Main.
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_div : m.op r_main = OP_DIV)
    -- Cross-AIR row selection: the OpBus permutation gives an
    -- existential `r_a`; we accept it explicitly here so the bridge
    -- shape stays simple (Compliance.lean will obtain `r_a` via
    -- `op_bus_perm_sound_ArithDiv` and pass it in). The matching
    -- predicate carries `m.op r_main = v.op r_a`.
    (h_match_primary :
      matches_entry (opBus_row_Main m r_main)
                    (ZiskFv.Airs.ArithDiv.opBus_row_ArithDiv v r_a))
    -- ============ STRUCTURAL BUS / EXEC SHAPE (passed through) ============
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_DIVREM_div_pure div_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : div_input.rd = Transpiler.wrap_to_regidx e2.ptr)
    -- ============ SAIL-SIDE STATE PREDICATES (SPEC-PRE) ============
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok div_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok div_input.r2_val state)
    (h_input_rd : div_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some div_input.PC)
    (h_op2_ne : div_input.r2_val.toInt ≠ 0)
    (h_no_overflow :
      ¬ (div_input.r1_val.toInt = -(2:ℤ)^63 ∧ div_input.r2_val.toInt = -1))
    -- ============ UNIVERSAL-PER-ROW VALIDITY (constructibility) ============
    -- Per-row Arith-AIR constraints, EXTENDED bundle: the standard
    -- carry-chain (constraints 6-8 + 31-38) PLUS constraint 46
    -- (`bus_res1` normalization at `arith.pil:263`, required for
    -- the GAP-A hi-lane discharge via `div_bus_res1_eq_a_hi`).
    -- Compliance.lean collapses this into the universal
    -- `∀ r, arith_div_row_well_formed v r` parameter.
    (h_row_constraints :
      ZiskFv.Airs.ArithDiv.div_row_constraints_with_c46 v r_a)
    (h_na_bool : v.na r_a = 0 ∨ v.na r_a = 1)
    (h_nb_bool : v.nb r_a = 0 ∨ v.nb r_a = 1)
    (h_nr_bool : v.nr r_a = 0 ∨ v.nr r_a = 1)
    (h_np_xor :
      toIntZ (v.np r_a)
        = toIntZ (v.na r_a) + toIntZ (v.nb r_a)
            - 2 * toIntZ (v.na r_a) * toIntZ (v.nb r_a))
    -- ============ REMAINING PROMISE HYPOTHESES ============
    -- GAP-B: signed Sail-state bridge — connects r1/r2 (Sail values)
    -- to `packed4 c[] - np·2^64` / `packed4 b[] - nb·2^64`. The
    -- unsigned form `r.toNat = packed4 c[]` follows from OpBus +
    -- `transpile_DIV` + `packed_lane_eq_of_read_xreg`; the signed
    -- lift requires linking the sign witnesses to the BitVec MSB
    -- (pure-Lean bridge — no new axiom). Surfaced for follow-up.
    (h_op1 :
      div_input.r1_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.c_0 r_a).val (v.c_1 r_a).val (v.c_2 r_a).val (v.c_3 r_a).val : ℤ)
            - (v.np r_a).val * (2:ℤ)^64)
    (h_op2 :
      div_input.r2_val.toInt
        = (ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.b_0 r_a).val (v.b_1 r_a).val (v.b_2 r_a).val (v.b_3 r_a).val : ℤ)
            - (v.nb r_a).val * (2:ℤ)^64) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute (instruction.DIV (r2, r1, rd, false))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ DERIVE arith-side opcode literal (GAP-O) ============
  -- `matches_entry`'s op-slot equality projects to
  -- `m.op r_main = v.op r_a` (the bus opcode column IS the
  -- v.op column on the prove side, per `arith.pil:269`).
  have h_op_eq : v.op r_a = m.op r_main := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.1.symm
  have h_op_arith_div : v.op r_a = 186 := by
    rw [h_op_eq, h_main_op_div]; simp [OP_DIV]
  have h_op_arith : v.op r_a = 186 ∨ v.op r_a = 187 := Or.inl h_op_arith_div
  -- ============ Unpack extended row-constraint bundle ============
  have h_chain : ZiskFv.Airs.ArithDiv.div_carry_chain_holds v r_a :=
    ZiskFv.Airs.ArithDiv.div_carry_chain_holds_of_extended v r_a h_row_constraints
  have h_c46 : Arith.extraction.constraint_46_every_row v.circuit r_a :=
    ZiskFv.Airs.ArithDiv.constraint_46_of_extended v r_a h_row_constraints
  -- ============ DISCHARGE mode pins (GAP-M) ============
  obtain ⟨h_sext, h_m32, h_div⟩ :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_mode_pin v r_a h_op_arith
  -- ============ DISCHARGE main_div/main_mul selector pins (GAP-A hi prep) ============
  -- Class-#6b axiom: `op = 186 (DIV)` pins `main_div = 1, main_mul = 0`
  -- on the same arith_table lookup as `arith_table_op_div_rem_signed_mode_pin`.
  obtain ⟨h_main_div_one, h_main_mul_zero⟩ :=
    (ZiskFv.Airs.Arith.arith_table_op_div_rem_main_selector_pin
      v r_a h_op_arith).1 h_op_arith_div
  -- ============ DISCHARGE h_nr_pin (existing trust ledger) ============
  have h_nr_pin_fgl :=
    ZiskFv.Airs.Arith.arith_table_op_div_rem_signed_d_sign_pin
      v r_a h_sext h_m32 h_div h_op_arith
  have h_nr_pin :
      toIntZ (v.nr r_a) = toIntZ (v.np r_a)
      ∨ ((toIntZ (v.a_0 r_a) + toIntZ (v.a_1 r_a) * 65536
            + toIntZ (v.a_2 r_a) * (65536 * 65536)
            + toIntZ (v.a_3 r_a) * (65536 * 65536 * 65536)) * 0 = 0
          ∧ (v.d_0 r_a).val = 0 ∧ (v.d_1 r_a).val = 0
          ∧ (v.d_2 r_a).val = 0 ∧ (v.d_3 r_a).val = 0) := by
    rcases h_nr_pin_fgl with h_eq | ⟨hd0, hd1, hd2, hd3⟩
    · left; rw [h_eq]
    · right
      refine ⟨by ring, hd0, hd1, hd2, hd3⟩
  -- ============ DISCHARGE h_byte_lo / h_byte_hi (GAP-A) ============
  -- Bundle delivers BOTH the `e2.x0..x3` (lo) pack and the
  -- `e2.x4..x7` (hi) pack as ℕ-form equalities tied to Main's
  -- `c_0`/`c_1` columns. Op-bus `matches_entry` gives FGL equalities
  -- on the c_lo / c_hi slots of `opBus_row_ArithDiv`:
  --   c_lo: m.c_0 r_main = v.a_0 r_a + v.a_1 r_a * 65536
  --   c_hi: m.c_1 r_main = v.bus_res1 r_a
  -- The lo side is direct. For the hi side we further apply
  -- `div_bus_res1_eq_a_hi` (Bridge1) under the DIV-primary mode pins
  -- (`main_div = 1`, `main_mul = 0`, plus `sext = 0`, `m32 = 0`,
  -- plus per-row constraint 46) to get `v.bus_res1 = v.a_2 + v.a_3 * 65536`.
  -- Both lanes lift FGL → ℕ via the chunk-range axiom on `v.a_*` (each
  -- < 2^16, so the rhs is < 2^32 < GL_prime — no modular reduction).
  have h_bundle :=
    ZiskFv.Airs.MemoryBus.MemBridge.main_external_arith_emission_bundle
      m r_main e2 (0 : BitVec 5) (m.op r_main)
      h_main_active rfl
      -- OP_DIV literal in the 16-way op-set disjunction.
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl h_main_op_div)))))))))
      h_m2_mult (by rw [h_m2_as])
  have h_byte_lo_to_c0 : e2.x0.val + e2.x1.val * 256
      + e2.x2.val * 65536 + e2.x3.val * 16777216
      = (m.c_0 r_main).val := h_bundle.1
  have h_byte_hi_to_c1 : e2.x4.val + e2.x5.val * 256
      + e2.x6.val * 65536 + e2.x7.val * 16777216
      = (m.c_1 r_main).val := h_bundle.2.1
  -- Extract op-bus's c_lo / c_hi equalities (FGL form).
  have h_c0_eq_FGL : m.c_0 r_main = v.a_0 r_a + v.a_1 r_a * 65536 := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.2.2.2.2.2.1
  have h_c1_eq_FGL : m.c_1 r_main = v.bus_res1 r_a := by
    have := h_match_primary
    simp only [matches_entry, opBus_row_Main, opBus_row_ArithDiv] at this
    exact this.2.2.2.2.2.2.2.1
  -- Chunk-range bounds for v.a_0..v.a_3.
  obtain ⟨h_a0_lt, h_a1_lt, h_a2_lt, h_a3_lt, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    ZiskFv.Airs.Arith.arith_div_columns_in_range v r_a
  -- Helper: FGL → ℕ lift for `x + y * 65536` when both are < 65536.
  have h_pair_lift : ∀ (x y : FGL),
      x.val < 65536 → y.val < 65536 →
      (x + y * 65536 : FGL).val = x.val + y.val * 65536 := by
    intro x y hx hy
    have h_cast : (x + y * 65536 : FGL)
        = (((x.val + y.val * 65536 : ℕ) : FGL)) := by
      push_cast; ring
    rw [h_cast, Fin.val_natCast]
    apply Nat.mod_eq_of_lt
    have h_sum_bound : x.val + y.val * 65536 < 65536 + 65536 * 65536 := by
      have h_y_mul : y.val * 65536 < 65536 * 65536 :=
        (Nat.mul_lt_mul_right (by decide : (0:ℕ) < 65536)).mpr hy
      exact Nat.add_lt_add hx h_y_mul
    have h_lt_prime : (65536 + 65536 * 65536 : ℕ) < GL_prime := by decide
    exact lt_trans h_sum_bound h_lt_prime
  -- FGL → ℕ lift for c_0.
  have h_c0_val_eq : (m.c_0 r_main).val
      = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := by
    rw [h_c0_eq_FGL]; exact h_pair_lift _ _ h_a0_lt h_a1_lt
  -- Compose lo lane: byte-lo-pack = (m.c_0).val = v.a_0.val + v.a_1.val * 65536.
  have h_byte_lo :
      e2.x0.val + e2.x1.val * 256 + e2.x2.val * 65536 + e2.x3.val * 16777216
        = (v.a_0 r_a).val + (v.a_1 r_a).val * 65536 := by
    rw [h_byte_lo_to_c0, h_c0_val_eq]
  -- ============ DISCHARGE h_byte_hi (GAP-A, hi lane) ============
  -- `div_bus_res1_eq_a_hi` consumes constraint 46 + the four mode pins.
  have h_bus_res1_eq : v.bus_res1 r_a = v.a_2 r_a + v.a_3 r_a * 65536 :=
    ZiskFv.Airs.ArithBridge1.div_bus_res1_eq_a_hi v r_a h_c46
      h_sext h_m32 h_main_mul_zero h_main_div_one
  -- Compose: m.c_1 = bus_res1 = v.a_2 + v.a_3 * 65536, then lift FGL → ℕ.
  have h_c1_val_eq : (m.c_1 r_main).val
      = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536 := by
    rw [h_c1_eq_FGL, h_bus_res1_eq]; exact h_pair_lift _ _ h_a2_lt h_a3_lt
  have h_byte_hi :
      e2.x4.val + e2.x5.val * 256 + e2.x6.val * 65536 + e2.x7.val * 16777216
        = (v.a_2 r_a).val + (v.a_3 r_a).val * 65536 := by
    rw [h_byte_hi_to_c1, h_c1_val_eq]
  -- ============ DISCHARGE h_r_abs, h_r_sign (GAP-C) ============
  -- `arith_div_remainder_bound` gives the bound in terms of the
  -- AIR's signed `b - nb·2^64` and `c - np·2^64` packings; we
  -- rewrite via `h_op2` and `h_op1` to land on `r2.toInt` /
  -- `r1.toInt` shapes that `equiv_DIV` consumes.
  obtain ⟨h_r_abs_air, h_r_sign_air⟩ :=
    ZiskFv.Airs.Arith.arith_div_remainder_bound v r_a h_sext h_m32 h_div h_op_arith
  have h_r_abs :
      ((ZiskFv.PackedBitVec.MulNoWrap.packed4
          (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
        - (v.nr r_a).val * (2:ℤ)^64).natAbs < div_input.r2_val.toInt.natAbs := by
    rw [h_op2]; exact h_r_abs_air
  have h_r_sign :
      0 ≤ ((ZiskFv.PackedBitVec.MulNoWrap.packed4
            (v.d_0 r_a).val (v.d_1 r_a).val (v.d_2 r_a).val (v.d_3 r_a).val : ℤ)
            - (v.nr r_a).val * (2:ℤ)^64) * div_input.r1_val.toInt := by
    rw [h_op1]; exact h_r_sign_air
  -- ============ Delegate to `equiv_DIV` ============
  -- The Sail `instruction.DIV` LHS matches; all derived hypotheses fit.
  exact ZiskFv.Equivalence.Div.equiv_DIV
    state div_input r1 r2 rd exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    v r_a h_chain h_na_bool h_nb_bool h_nr_bool h_np_xor h_nr_pin
    h_sext h_m32 h_div h_byte_lo h_byte_hi h_op1 h_op2
    h_op2_ne h_no_overflow h_r_abs h_r_sign

end ZiskFv.Equivalence.Compliance
