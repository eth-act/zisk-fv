import Mathlib

import ZiskFv.Equivalence.BranchEqual
import ZiskFv.SailSpec.beq
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main

/-!
# `equiv_BEQ` trust-discharge wrapper — ControlFlow branches shape exemplar
## Why BEQ

BEQ is the cheapest branch in RV64IM:

* **Symmetric** in `rs1` / `rs2` (vs. BLT/BGE which are signed and
  need MSB sign-witness pins; vs. BLTU/BGEU which use an unsigned
  comparison flag but no sign witness).
* No `rd` write (no memory-bus rd-write entry — vs. LUI/AUIPC/JAL/JALR
  which write `pc + 4` or an immediate).
* No signed-vs-unsigned distinction at the comparison layer
  (equality is sign-agnostic).
* Sign-witness pins (category 3) are N/A — BLT / BGE would add them
  in their within-shape authoring.

The remaining wrapper-level discharge targets on `equiv_BEQ` are the
*pure-spec misalignment promises* `h_not_throws` and `h_success`,
plus the *Sail aux* `h_misa_c`. The misalignment promises are
discharged from a single SPEC-PRE `h_target_aligned` describing the
branch target's 4-byte alignment — a ZisK runtime invariant. `h_misa_c`
passes through (Compliance.lean owns the ZisK-misa configuration).

## 5-category discharge applied to BEQ

* **Lane-match (category 1).** N/A on the provider side. The
  flag-correctness fact (`m.flag = 1 ↔ r1_val = r2_val`) lives on
  the Binary AIR via the operation-bus hop with `OP_EQ`; on the
  canonical surface, the Sail-pure-spec form
  `(execute_BEQ_pure beq_input).nextPC` already incorporates the
  branch decision, and the **structural pin** `h_nextPC_matches`
  ties the bus's exec_row[1].pc to that pure-spec output. The
  wrapper does NOT discharge `h_nextPC_matches`; that work
  belongs to a separate Binary-flag-correctness bridge consumed
  by Compliance.lean's PC handshake.
* **Mode pins (category 2).** N/A on the provider AIR side
  (branches don't flow through a provider AIR with mode columns).
  The Main-side mode pins (`m32 = 0`, `set_pc = 0`,
  `is_external_op = 1`, `op = OP_EQ`) come from `transpile_BEQ`
  (class #1) applied to `h_main_active` + `h_main_op_beq` — but
  the canonical `equiv_BEQ` does not consume them directly; it
  pivots on the Sail-side pure-spec equivalence. They are tracked
  in `Bridge/ControlFlow.lean::branch_input_bridges_of_read_xreg`
  for the Binary-flag-correctness path (not exercised here).
* **Sign-witness pins (category 3).** N/A — equality is
  sign-agnostic. BLT/BGE within-shape authoring will additionally
  need `binary_b_op_or_sext_eq_OP_LT` or similar sign pins; BEQ
  does not.
* **Range/bound (category 4).** N/A — BEQ writes no register and
  consumes no byte-level Mem entries.
* **Operand bridges (category 5).** N/A at the wrapper level —
  `equiv_BEQ` already consumes the unstructured Sail `read_xreg`
  facts (`h_input_r1`, `h_input_r2`) directly; no
  `packed_lane_eq_of_read_xreg` step is needed because the
  comparison is performed inside `execute_BEQ_pure` via raw
  `BitVec` equality, not via lane chunks.

## The actual discharge: alignment promises

The two promise hypotheses `h_not_throws` and `h_success` on
`equiv_BEQ` say that the BEQ pure-spec output reports no exception.
Reading `PureSpec.execute_BEQ_pure`:

```
skip   := !(input.r1_val == input.r2_val)
throws := !skip && BitVec.ofBool (input.PC + signExt 64 input.imm)[0] == 1#1
fails  := throws || (!skip && BitVec.ofBool (input.PC + signExt 64 input.imm)[1] == 1#1)
success := !fails
```

So both `throws` and `!success` depend on bits 0 and 1 of
`input.PC + signExt 64 input.imm` being zero. When the branch target
is 4-byte-aligned (its low 2 bits are zero), both bit checks fail,
giving `throws = false` and `success = true` uniformly — **regardless
of whether the branch is taken**.

The wrapper therefore discharges both promise hypotheses from a
single caller-supplied alignment fact
`h_target_aligned : (input.PC + signExt 64 input.imm).toNat % 4 = 0`.
This is a SPEC-PRE caller obligation in the same trust class as
`h_misa_c` (a ZisK-runtime configuration invariant). RV64I requires
all branch targets to be 4-byte-aligned (RISC-V ISA Manual, §2.5),
and ZisK's assembler/transpiler emits only well-formed branch
instructions, so this hypothesis is unconditionally true in any
real trace.

## Anti-laundering report

Per the discharge-recipe.md wrapper-specific checks:

* **No new axioms.** This wrapper consumes only `equiv_BEQ` itself
  plus pure Lean composition. Trust ledger unchanged — matches the
  per-AIR axiom map's 0-new-axioms prediction for ControlFlow.
* **Caller-burden shrinks.** −2 promises (`h_not_throws`,
  `h_success`) discharged from +1 SPEC-PRE (`h_target_aligned`).
  Net −1 binder / −1 hypothesis at the per-opcode level.
* **Bridges cross-shape if possible.** N/A — no new helper added;
  the alignment derivation is a 5-line BitVec computation local to
  this file.

## Caller-burden

`equiv_BEQ` (canonical): 19 binders / 11 hypotheses (state, beq_input,
imm, r1, r2, misa_val, exec_row, h_input_imm, h_input_r1, h_input_r2,
h_input_pc, h_input_misa, h_misa_c, h_exec_len, h_e0_mult, h_e1_mult,
h_nextPC_matches, h_not_throws, h_success).

`equiv_BEQ_from_trust` (this file): 18 binders / 10 hypotheses
(state, beq_input, imm, r1, r2, misa_val, exec_row, h_input_imm,
h_input_r1, h_input_r2, h_input_pc, h_input_misa, h_misa_c,
h_target_aligned, h_exec_len, h_e0_mult, h_e1_mult, h_nextPC_matches).

**Net: −1 binder / −1 hypothesis.** Beats the +1 hypothesis growth
observed on LUI's structural-unpacking pattern; the BEQ exemplar is a
clean promise discharge with no compensating bundle unpack required
(branches are simpler than UTYPE because no rd-write entries are
involved).

## Cross-shape lessons

* **No new bridge added** to `Equivalence/Bridge/ControlFlow.lean`
  or `Equivalence/Bridge/SailStateBridge.lean`. The misalignment
  derivation is a local BitVec.toNat-vs-bit-extract argument.
* **Generalizes mechanically to BNE / BLT / BGE / BLTU / BGEU** —
  every branch's pure spec has the same `throws`/`success` shape
  parameterized on the comparison output. The within-shape wrappers
  swap `execute_BEQ_pure` for the per-branch pure spec; the
  alignment lemma is opcode-agnostic. **Signed branches (BLT/BGE)
  additionally need sign-witness pins** to discharge their flag-
  correctness path through the Binary AIR's `OP_LT` lookup — but
  those pins are independent of the alignment discharge done here.
* **Flag-correctness discharge is deferred.** Discharging
  `h_nextPC_matches` from circuit witnesses requires composing
  `branch_eq_compositional` (`Circuit/BranchEqual.lean`) with a
  Binary-AIR flag-correctness axiom (`OP_EQ` lookup-bus pin) plus
  `transpile_BEQ`'s `jmp_offset1 = imm`, `jmp_offset2 = 4` pins.
  That work belongs to a future ControlFlow flag-correctness
  bridge and is not in scope for this exemplar. The branches'
  per-AIR axiom map entry for category 1 is "bridge-only" — the
  needed `OP_EQ` flag-correctness bridge lives in
  `Bridge/ControlFlow.lean` (not added by this PR) consuming
  `op_bus_perm_sound_Binary` (class #4) + `bin_table_consumer_wf`
  (class #6) on the `wf_EQ` clause.
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Alignment-implies-no-exception lemma for BEQ.** Given a
    4-byte-aligned branch target, both `throws` and `!success`
    evaluate to `false` uniformly (regardless of taken/not-taken).

    Pure BitVec computation: bits 0 and 1 of an address ≡ 0 mod 4
    are both zero, so both `BitVec.ofBool x[i] == 1#1` checks fail. -/
private theorem beq_pure_no_exception_of_aligned
    (input : PureSpec.BeqInput)
    (h_aligned : (input.PC + BitVec.signExtend 64 input.imm).toNat % 4 = 0) :
    (PureSpec.execute_BEQ_pure input).throws = false
    ∧ (PureSpec.execute_BEQ_pure input).success = true := by
  -- Set up an abbreviation for the target address.
  set t : BitVec 64 := input.PC + BitVec.signExtend 64 input.imm with h_t
  -- Bits 0 and 1 of an address ≡ 0 mod 4 are both zero.
  have h_bit0 : t[0] = false := by
    -- t[0] = (t.toNat / 2^0) % 2 == 1 ; equivalently testBit 0.
    rw [BitVec.getElem_eq_testBit_toNat]
    rw [Nat.testBit_zero]
    -- Now goal: (t.toNat % 2 == 1) = false, i.e. t.toNat % 2 ≠ 1.
    -- From t.toNat % 4 = 0 we have t.toNat % 2 = 0.
    have h_mod2 : t.toNat % 2 = 0 := by omega
    simp [h_mod2]
  have h_bit1 : t[1] = false := by
    rw [BitVec.getElem_eq_testBit_toNat]
    rw [Nat.testBit_succ, Nat.testBit_zero]
    -- Goal: ((t.toNat / 2) % 2 == 1) = false.
    have h_div_mod : (t.toNat / 2) % 2 = 0 := by omega
    simp [h_div_mod]
  -- Now compute both fields of execute_BEQ_pure under the bit
  -- equalities. The structure of execute_BEQ_pure is:
  --   throws := !skip && (bit0 == 1)
  --   fails  := throws || (!skip && (bit1 == 1))
  --   success := !fails
  -- With bit0 = bit1 = false, throws = false and fails = false, so
  -- success = true, regardless of `skip`.
  refine ⟨?_, ?_⟩
  · -- throws = false
    simp [PureSpec.execute_BEQ_pure, ← h_t, h_bit0]
  · -- success = true
    simp [PureSpec.execute_BEQ_pure, ← h_t, h_bit0, h_bit1]

/-- **Pilot wrapper for `equiv_BEQ`.** Discharges the two
    pure-spec exception promises (`h_not_throws`, `h_success`)
    from a single SPEC-PRE 4-byte-alignment hypothesis.

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `beq_input`, `imm`, `r1`, `r2`,
       `misa_val`).
    2. The structural bus row (`exec_row`).
    3. The Sail `read_xreg` / PC / misa state predicates (pass-through
       from `equiv_BEQ`).
    4. The `misa[C] = 0` ZisK-config pin `h_misa_c` (pass-through).
    5. The SPEC-PRE alignment witness `h_target_aligned`. ZisK's
       assembler / transpiler guarantees this on every BEQ
       instruction; Compliance.lean delivers it from the program-
       level well-formedness invariant.
    6. The bus-shape pins (`h_exec_len`, `h_e0_mult`, `h_e1_mult`,
       `h_nextPC_matches`) — pass-through from `equiv_BEQ`.

    Derived internally (NOT caller-supplied):
    * `h_not_throws : (execute_BEQ_pure beq_input).throws = false`
    * `h_success : (execute_BEQ_pure beq_input).success = true`
    Both derived from `h_target_aligned` via
    `beq_pure_no_exception_of_aligned`.

    Trust footprint: `equiv_BEQ`'s existing closure (no new axioms).
    Zero new axioms — matches `docs/fv/per-air-axiom-map.md`'s
    prediction for ControlFlow branches. -/
theorem equiv_BEQ_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (beq_input : PureSpec.BeqInput)
    (imm : BitVec 13)
    (r1 r2 : regidx)
    (misa_val : RegisterType Register.misa)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    -- Sail-side state predicates (SPEC-PRE).
    (h_input_imm : beq_input.imm = imm)
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok beq_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok beq_input.r2_val state)
    (h_input_pc : state.regs.get? Register.PC = .some beq_input.PC)
    (h_input_misa : state.regs.get? Register.misa = .some misa_val)
    (h_misa_c : Sail.BitVec.extractLsb misa_val 2 2 = 0#1)
    -- SPEC-PRE alignment witness on the branch target. ZisK's
    -- assembler/transpiler invariant; Compliance.lean delivers
    -- from the program-level well-formedness obligation.
    (h_target_aligned :
      (beq_input.PC + BitVec.signExtend 64 beq_input.imm).toNat % 4 = 0)
    -- Bus-shape structural hypotheses — pass-through from `equiv_BEQ`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_BEQ_pure beq_input).nextPC) :
    execute_instruction (instruction.BTYPE (imm, r2, r1, bop.BEQ)) state
      = (bus_effect exec_row [] state).2 := by
  -- ============ Discharge `h_not_throws` and `h_success` from `h_target_aligned` ============
  obtain ⟨h_not_throws, h_success⟩ :=
    beq_pure_no_exception_of_aligned beq_input h_target_aligned
  -- ============ Delegate to canonical `equiv_BEQ` ============
  exact ZiskFv.Equivalence.BranchEqual.equiv_BEQ
    state beq_input imm r1 r2 misa_val exec_row
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

end ZiskFv.Compliance
