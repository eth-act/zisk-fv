import Mathlib

import ZiskFv.Equivalence.Or
import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.MemoryBus
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges

/-!
# `equiv_OR` Compliance pilot — Binary shape exemplar (Step 4.1.4)

> **Status:** PILOT. Fourth shape exemplar after DIV (`FromTrust/Div.lean`,
> the Arith provider-AIR shape), LUI (`FromTrust/Lui.lean`, the
> Main-only ControlFlow non-branch shape), and ADD (`FromTrust/Add.lean`,
> the BinaryAdd provider-AIR shape). Demonstrates the discharge
> recipe applied to the **Binary provider-AIR shape** — the largest
> provider-AIR in the inventory (14 opcodes: AND/ANDI/OR/ORI/XOR/XORI/
> SLT/SLTI/SLTU/SLTIU/SUB/SUBW/ADDIW/ADDW).
>
> Lives outside the canonical surface (under
> `Compliance/FromTrust/`) so V1 anti-laundering metrics on the
> canonical theorem are unaffected.

## Why OR

OR is the simplest of the 14 Binary-shape opcodes:

* No signed comparison (unlike SLT/SLTI/SLTU/SLTIU — those add
  sign-witness pins).
* No 32-bit truncation (unlike SUBW/ADDIW/ADDW — those add m32-mode
  pins).
* No carry-chain consumer (unlike SUB/SLT-family — those need the
  6-field `consumer_byte_match_chain` family that AND/OR/XOR's
  byte-local 3-field family covers).
* Symmetric in rs1/rs2 (unlike Tier-2 ops, no extra ordering).

Per `docs/fv/per-air-axiom-map.md` the Binary shape pilot has the
largest predicted axiom delta (2–4) of the six remaining shapes —
the AIR covers 14 opcodes across several sub-shapes, and the
mode-pin / sign-pin surface is broader than BinaryAdd's. **This OR
pilot lands 1 new axiom** at the low end of the prediction, because
the OR-shape (and AND/XOR by symmetry) only need the
`b_op_or_sext = OP_OR` mode pin — no sign or W-mode pins required.

## 5-category discharge applied

* **Lane-match.** Internalized by `equiv_OR` via the `Bridge.Binary`
  discharge family (`byte_ranges_at_holds`, `byte_chain_discharge_logic`,
  `match_clo_chi_OR`, `input_r1_packed_a`, `input_r2_packed_b`,
  `e2_byte_ranges_discharge`). These consume the trust-ledger axioms
  `binary_columns_in_range` (#6), `binary_per_byte_lookup_witness`
  (#6), `binary_carry_bits_in_range` (#6), `bin_table_consumer_wf`
  (#6), and `memory_bus_entry_byte_range_perm_sound` (#5b). The
  wrapper-level lane-match obligation is the **existential row**
  `r_binary` plus the `matches_entry` predicate; both come from
  `op_bus_perm_sound_Binary` (#4).
* **Mode pins.** OR consumes one mode pin on the provider AIR:
  `(v.b_op_or_sext r_binary).val = OP_OR`. This is the gap addressed
  by the **new axiom** `binary_b_op_or_sext_eq_OP_OR` (class #6) in
  `ZiskFv/Airs/Binary/BinaryRanges.lean` — the consequence of
  PIL's `b_op_or_sext` linear def (`binary.pil:104`) plus the
  per-byte BinaryTable lookup (`binary.pil:131-148`) restricting the
  `(b_op, mode32, c_is_signed)` triple to a unique valid decomposition
  when the on-bus emission `b_op + 16 * mode32 = 15`.
* **Sign-witness pins.** N/A for OR (unsigned bitwise op).
* **Range/bound.** Discharged by the Binary AIR's range axioms
  (`binary_columns_in_range`, `binary_carry_bits_in_range`) —
  pre-internalized by `equiv_OR` via the `Bridge.Binary` helpers.
  No wrapper-level work.
* **Operand bridges.** Discharged by
  `Bridge.SailStateBridge.packed_lane_eq_of_read_xreg` (consumed
  through `Bridge.Binary.input_r1_packed_a` / `input_r2_packed_b`).
  Pre-internalized on the canonical surface.

## Anti-laundering report

* **One new axiom.** `binary_b_op_or_sext_eq_OP_OR` in
  `ZiskFv/Airs/Binary/BinaryRanges.lean`. Class #6 (Binary AIR
  lookup soundness — table-pin sub-class). PIL-cited
  (`binary.pil:104` + `binary.pil:131-148`). At the **low end** of
  the per-AIR axiom map's 2–4 prediction — possible because OR's
  byte-local logic shape (shared with AND/XOR) only needs one pin
  to distinguish OR from AND/XOR at the `b_op_or_sext` lookup level;
  AND and XOR will need parallel `binary_b_op_or_sext_eq_OP_{AND,XOR}`
  pins for their wrappers (so the shape's mass-author phase will
  add 2 more class-#6 axioms — still within the 2–4 envelope).
* **Bridges cross-shape if possible.** No new bridge helpers added.
  The existing `Bridge.Binary` infrastructure (`carry_7_zero_OR_pure`,
  `byte_chain_discharge_logic`, `match_clo_chi_OR`, the
  `input_r{1,2}_packed_a/b` Sail-state bridges) already covers
  every category the OR pilot needs.
* **Caller-burden shrinks.** See the count below.

## Caller-burden

`equiv_OR` (canonical): **32 binders / 22 hypotheses**.
`equiv_OR_from_trust` (this file): **29 binders / 19 hypotheses**.

Net **−3 binders / −3 hypotheses** per Binary-shape opcode.
Composition:

* Drops `r_binary` (1 binder): existential row witness produced by
  `op_bus_perm_sound_Binary`.
* Drops `h_match` (1 hypothesis): the cross-AIR `matches_entry`
  comes paired with `r_binary` from `op_bus_perm_sound_Binary`.
* Drops `h_bop_or_sext` (1 hypothesis): the `b_op_or_sext = OP_OR`
  mode pin is derived by the new axiom
  `binary_b_op_or_sext_eq_OP_OR` after projecting matches_entry's
  `.op` slot through `h_main_op_or`.

At the **global Compliance.lean** level the reduction extends further:
`(m, v, ∀ r, core_every_row v r)` collapse into shared parameters
across all 14 Binary-shape opcodes, and `h_main_active` /
`h_main_op_or` come from Compliance.lean's program-counter handshake.

The remaining wrapper-level promise hypothesis (caller-burden) on
this exemplar is `h_lane_rd : register_write_lanes_match m r_main e2`,
deferred to the Mem pilot (Step 4.1.3 SD) for cross-shape discharge
via a Binary-side `main_external_logic_emission_bundle` (or equivalent
class-#4 bundle). The AddExemplar follows the same convention.

## Cross-shape lessons

* The **matches_entry `.op` projection** under `OP_OR = 15` is
  one-step: `simp only [matches_entry, opBus_row_Main, opBus_row_Binary]`
  exposes the `m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary`
  equality; combined with `h_main_op_or`, this gives the precondition
  `v.b_op r_binary + 16 * v.mode32 r_binary = 15` for the new pin
  axiom. The same pattern transfers verbatim to AND (`OP_AND = 14`)
  and XOR (`OP_XOR = 16`).
* The discharge generalizes mechanically to the **6 byte-local logic
  opcodes** (AND/ANDI/OR/ORI/XOR/XORI):
  * Swap `transpile_OR` for `transpile_<AND,XOR,…>`.
  * Swap `OP_OR = 15` for the relevant opcode literal.
  * Swap the new axiom `binary_b_op_or_sext_eq_OP_OR` for the
    parallel `_OP_AND` / `_OP_XOR` pin.
  * The 8 byte-chain matches and the c-lane discharge use the
    matching `Bridge.Binary.byte_chain_discharge_logic` /
    `match_clo_chi_{AND,XOR}` already in place.
* **For SLT/SLTI/SLTU/SLTIU (signed comparison)** the wrapper will
  additionally need a sign-witness pin (e.g.
  `binary_use_first_byte_pin_SLT` or a c-lane sign-bit pin) — out
  of scope for this pilot, predicted in the per-AIR axiom map's
  "sign-witness pins (1–2)" line.
* **For SUB/SUBW/ADDIW/ADDW** the wrapper will additionally need a
  cin/carry-chain pin (`consumer_byte_match_chain` 6-field variant)
  — out of scope for this pilot.

The byte-chain infrastructure (`Bridge.Binary.byte_chain_discharge_logic`)
is shape-agnostic in the opcode literal — it works for any
`b_op_or_sext = op_val` pinning. The wrapper-level work for AND/XOR
will be ~30 lines apiece (essentially copy of this file).
-/

namespace ZiskFv.Compliance

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus

variable {C : Type → Type → Type} [Circuit FGL FGL C]

/-- **Pilot wrapper for `equiv_OR`.**

    Caller obligations (signature header, ordered):
    1. The Sail-side inputs (`state`, `or_input`, `r1`, `r2`, `rd`).
    2. The two AIR validators with the selected Main row index
       (`m : Valid_Main`, `v : Valid_Binary`, `r_main : ℕ`).
       Compliance.lean shares `(m, v)` across all Binary-shape
       opcodes (14 ops).
    3. The structural bus rows (`exec_row`, `e0`, `e1`, `e2`).
    4. The activation + opcode pins on Main (`h_main_active`,
       `h_main_op_or`). Both come from Compliance.lean's
       program-counter handshake on the row hosting the OR
       instruction.
    5. The lane-match for the rd-write entry (`h_lane_rd`).
       Currently caller-supplied; the Mem pilot (Step 4.1.x) will
       discharge this from a Binary-side
       `main_external_logic_emission_bundle` (class #4) once the
       Mem-side AIR data is plumbed through Compliance.lean. The
       AddExemplar (Step 4.1.2) follows the same convention.
    6. The Sail-side state predicates (SPEC-PRE):
       `h_input_r1`, `h_input_r2`, `h_input_rd`, `h_input_pc`.
    7. The bus-protocol structural hypotheses — pass-through from
       `equiv_OR`; Compliance.lean supplies these from the same
       bus-shape obligations as every other opcode in the shape.

    Derived internally (NOT caller-supplied):
    * Existential row witness `r_binary` and the cross-AIR
      `matches_entry` predicate — from `op_bus_perm_sound_Binary`
      (class #4) applied to `h_main_active` + `h_main_op_or`.
    * `(v.b_op_or_sext r_binary).val = OP_OR` — from the new axiom
      `binary_b_op_or_sext_eq_OP_OR` (class #6) applied to the
      matches_entry `.op`-slot projection composed with
      `h_main_op_or`.

    Trust footprint: `op_bus_perm_sound_Binary` (class #4),
    `binary_b_op_or_sext_eq_OP_OR` (class #6, **new**), plus
    `equiv_OR`'s existing closure (which transitively consumes the
    Binary range / per-byte-lookup / carry-bit-range / table-consumer
    axioms, plus `memory_bus_entry_byte_range_perm_sound` and
    `transpile_OR`). One new axiom — at the low end of
    `docs/fv/per-air-axiom-map.md`'s 2–4 prediction. -/
theorem equiv_OR_from_trust
    (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (or_input : PureSpec.OrInput)
    (r1 r2 rd : regidx)
    -- AIR validators + row index. Compliance.lean shares (m, v)
    -- across all Binary-shape opcodes (AND/ANDI/OR/ORI/XOR/XORI/
    -- SLT/SLTI/SLTU/SLTIU/SUB/SUBW/ADDIW/ADDW).
    (m : Valid_Main C FGL FGL) (v : Valid_Binary C FGL FGL)
    (r_main : ℕ)
    (exec_row : List (Interaction.ExecutionBusEntry FGL))
    (e0 e1 e2 : Interaction.MemoryBusEntry FGL)
    -- Activation / opcode pins. Compliance.lean derives these from
    -- the Main AIR's ROM handshake on the row hosting OR.
    (h_main_active : m.is_external_op r_main = 1)
    (h_main_op_or : m.op r_main = OP_OR)
    -- Lane-match for the rd-write entry. Currently caller-supplied;
    -- the Mem pilot will discharge this from a Binary-side
    -- `main_external_logic_emission_bundle`.
    (h_lane_rd : ZiskFv.Airs.MemoryBus.register_write_lanes_match m r_main e2)
    -- Sail-side state predicates (SPEC-PRE).
    (h_input_r1 : read_xreg (regidx_to_fin r1) state
      = EStateM.Result.ok or_input.r1_val state)
    (h_input_r2 : read_xreg (regidx_to_fin r2) state
      = EStateM.Result.ok or_input.r2_val state)
    (h_input_rd : or_input.rd = regidx_to_fin rd)
    (h_input_pc : state.regs.get? Register.PC = .some or_input.PC)
    -- Bus-protocol structural hypotheses — pass-through from `equiv_OR`.
    (h_exec_len : exec_row.length = 2)
    (h_e0_mult : exec_row[0]!.multiplicity = -1)
    (h_e1_mult : exec_row[1]!.multiplicity = 1)
    (h_nextPC_matches :
      (register_type_pc_equiv ▸ (BitVec.ofNat 64 (exec_row[1]!.pc).val))
        = (PureSpec.execute_RTYPE_or_pure or_input).nextPC)
    (h_m0_mult : e0.multiplicity = -1) (h_m0_as : e0.as.val = 1)
    (h_m1_mult : e1.multiplicity = -1) (h_m1_as : e1.as.val = 1)
    (h_m2_mult : e2.multiplicity = 1) (h_m2_as : e2.as.val = 1)
    (h_rd_idx : or_input.rd = Transpiler.wrap_to_regidx e2.ptr) :
    (do
      Sail.writeReg Register.nextPC
        (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
      LeanRV64D.Functions.execute
        (instruction.RTYPE (r2, r1, rd, rop.OR))) state
      = (bus_effect exec_row [e0, e1, e2] state).2 := by
  -- ============ Derive existential `r_binary` + `matches_entry` ============
  -- `op_bus_perm_sound_Binary` (class #4) gives the cross-AIR row
  -- match for any active Main row whose `op` selector lies in
  -- Binary's coverage disjunction (0x02..0x10, 0x12..0x1d, 0x50, 0x51).
  -- OP_OR = 15 = 0x0F satisfies the disjunction.
  have h_op_disj :
      m.op r_main = 0x02 ∨ m.op r_main = 0x03 ∨ m.op r_main = 0x04
    ∨ m.op r_main = 0x05 ∨ m.op r_main = 0x06 ∨ m.op r_main = 0x07
    ∨ m.op r_main = 0x08 ∨ m.op r_main = 0x09 ∨ m.op r_main = 0x0a
    ∨ m.op r_main = 0x0b ∨ m.op r_main = 0x0c ∨ m.op r_main = 0x0d
    ∨ m.op r_main = 0x0e ∨ m.op r_main = 0x0f ∨ m.op r_main = 0x10
    ∨ m.op r_main = 0x12 ∨ m.op r_main = 0x13 ∨ m.op r_main = 0x14
    ∨ m.op r_main = 0x15 ∨ m.op r_main = 0x16 ∨ m.op r_main = 0x17
    ∨ m.op r_main = 0x18 ∨ m.op r_main = 0x19 ∨ m.op r_main = 0x1a
    ∨ m.op r_main = 0x1b ∨ m.op r_main = 0x1c ∨ m.op r_main = 0x1d
    ∨ m.op r_main = 0x50 ∨ m.op r_main = 0x51 := by
    -- `h_main_op_or : m.op r_main = OP_OR` and `OP_OR = 15 = 0x0F`
    -- definitionally — pick the 14th disjunct (0x0f).
    have h15 : m.op r_main = 15 := by rw [h_main_op_or]; rfl
    tauto
  obtain ⟨r_binary, h_match⟩ :=
    op_bus_perm_sound_Binary m v r_main h_main_active h_op_disj
  -- ============ Derive `b_op_or_sext = OP_OR` mode pin ============
  -- Project `matches_entry`'s `.op` slot:
  --   m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary
  -- Compose with `h_main_op_or : m.op r_main = OP_OR = 15` to get
  -- the precondition for `binary_b_op_or_sext_eq_OP_OR`.
  have h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary = 15 := by
    have h_op_match : m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary := by
      simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
      exact h_match.2.1
    rw [h_main_op_or] at h_op_match
    -- `OP_OR := (15 : FGL)`; unfold to land at the literal.
    simp only [OP_OR] at h_op_match
    exact h_op_match.symm
  have h_bop_or_sext : (v.b_op_or_sext r_binary).val = ZiskFv.Airs.Tables.BinaryTable.OP_OR :=
    binary_b_op_or_sext_eq_OP_OR v r_binary h_emit_op
  -- ============ Delegate to canonical `equiv_OR` ============
  exact ZiskFv.Equivalence.Or.equiv_OR
    state or_input r1 r2 rd m v r_main r_binary exec_row e0 e1 e2
    h_input_r1 h_input_r2 h_input_rd h_input_pc
    h_exec_len h_e0_mult h_e1_mult h_nextPC_matches
    h_m0_mult h_m0_as h_m1_mult h_m1_as h_m2_mult h_m2_as h_rd_idx
    h_main_active h_main_op_or h_match h_bop_or_sext h_lane_rd

end ZiskFv.Compliance
