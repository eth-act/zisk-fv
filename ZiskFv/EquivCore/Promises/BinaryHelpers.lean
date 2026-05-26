import Mathlib

import ZiskFv.Trusted.Transpiler
import ZiskFv.Airs.Main.Main
import ZiskFv.Airs.OperationBus.OperationBus
import ZiskFv.Airs.OperationBus.Bridge
import ZiskFv.Airs.Binary.Binary
import ZiskFv.Airs.Binary.BinaryRanges
import ZiskFv.Airs.Binary.BinaryPackedCorrect

/-!
# Binary-family wrapper helpers

Per-AIR helper lemmas hoisted from the 14 Binary-family
`Compliance/Wrappers/<Op>.lean` wrappers (SUB, AND, OR, XOR, SLT,
SLTU, ANDI, ORI, XORI, SLTI, SLTIU, ADDW, SUBW, ADDIW). Each
wrapper had ~30-200 lines of near-identical "AIR plumbing"
discharging the chain-pin / mode-pin axiom output. These helpers
hoist that plumbing into a thin reusable layer.

**Trust footprint:** These helpers are `lemma` / `def` only — they
CONSUME existing trust-ledger axioms (`op_bus_perm_sound_Binary`,
`binary_consumer_byte_match_chain_pin`,
`binary_b_op_or_sext_eq_OP_{AND,OR,XOR}`, `binary_w_sext_choice_pin`,
`binary_w_mode_carry_7_zero`, `bin_table_consumer_wf`,
`bin_carry_7_is_boolean`) without adding any new axioms. The
`baseline-equiv-axiom-deps.txt` closure is preserved.

**Naming convention:** `binary_<predicate>_<of|from>_<inputs>`,
following the `BranchHelpers.lean` / `StoreHelpers.lean` precedent.
-/

namespace ZiskFv.EquivCore.Promises

open Goldilocks
open ZiskFv.Trusted
open ZiskFv.Airs.Main
open ZiskFv.Airs.Binary
open ZiskFv.Airs.OperationBus


/-! ## Helper 1: op-bus disjunction membership

Bundles `op_bus_perm_sound_Binary` with the 29-way `op` disjunction
that it requires. Caller supplies the opcode pin `h_main_op :
m.op r_main = (n : FGL)` for `n` one of the 29 allowed Binary
on-bus literals — `binary_op_disj_of_eq` builds the disjunction by
selecting the appropriate disjunct via `tauto`. -/

/-- Given `m.op r_main = (n : FGL)` where `n` is one of the 29
    Binary on-bus opcode literals (0x02..0x10, 0x12..0x1d, 0x50, 0x51),
    produce the disjunction that `op_bus_perm_sound_Binary` consumes.
    Implementation: `rw` the equality, then `tauto` selects the
    matching disjunct (all 29 RHS values are pure `FGL` literals). -/
lemma binary_op_disj_of_eq
    (m : Valid_Main FGL FGL) (r_main : ℕ) (n : ℕ)
    (h_eq : m.op r_main = (n : FGL))
    (h_mem : n = 0x02 ∨ n = 0x03 ∨ n = 0x04 ∨ n = 0x05 ∨ n = 0x06
        ∨ n = 0x07 ∨ n = 0x08 ∨ n = 0x09 ∨ n = 0x0a ∨ n = 0x0b
        ∨ n = 0x0c ∨ n = 0x0d ∨ n = 0x0e ∨ n = 0x0f ∨ n = 0x10
        ∨ n = 0x12 ∨ n = 0x13 ∨ n = 0x14 ∨ n = 0x15 ∨ n = 0x16
        ∨ n = 0x17 ∨ n = 0x18 ∨ n = 0x19 ∨ n = 0x1a ∨ n = 0x1b
        ∨ n = 0x1c ∨ n = 0x1d ∨ n = 0x50 ∨ n = 0x51) :
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
  rw [h_eq]
  rcases h_mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
                  | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> tauto

/-! ## Helper 2: matches_entry projection → op-emission equation -/

/-- Given the existential `matches_entry` produced by
    `op_bus_perm_sound_Binary` and a Main-side opcode pin
    `h_main_op : m.op r_main = (n : FGL)`, project Binary's
    op-emission equation `v.b_op r + 16 * v.mode32 r = (n : FGL)`.
    This is the precondition for `binary_consumer_byte_match_chain_pin`
    and `binary_b_op_or_sext_eq_OP_*`. -/
lemma binary_h_emit_op_of_matches_entry
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ} {n : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_main_op : m.op r_main = (n : FGL)) :
    v.b_op r_binary + 16 * v.mode32 r_binary = (n : FGL) := by
  have h_op_match : m.op r_main = v.b_op r_binary + 16 * v.mode32 r_binary := by
    simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
    exact h_match.2.1
  rw [← h_op_match, h_main_op]

/-! ## Helper 3: matches_entry → c-lane equalities

The `c_lo` and `c_hi` slot equations from `matches_entry`, used by
both the chain-pin family and mode-pin family wrappers. -/

/-- Project `matches_entry` into the pair of c-lane equations
    `(m.c_0 r_main = …)` and `(m.c_1 r_main = …)`. -/
lemma binary_c_lane_eqs_of_matches_entry
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary)) :
    m.c_0 r_main = v.free_in_c_0 r_binary + 256 * v.free_in_c_1 r_binary
        + 65536 * v.free_in_c_2 r_binary + 16777216 * v.free_in_c_3 r_binary
        + v.carry_7 r_binary
    ∧ m.c_1 r_main = v.free_in_c_4 r_binary + 256 * v.free_in_c_5 r_binary
        + 65536 * v.free_in_c_6 r_binary + 16777216 * v.free_in_c_7 r_binary := by
  simp only [matches_entry, opBus_row_Main, opBus_row_Binary] at h_match
  exact ⟨h_match.2.2.2.2.2.2.1, h_match.2.2.2.2.2.2.2.1⟩

/-! ## Helper 6: carry_7 = 0 for SUB-shape

For SUB / SUBW / ADDW / ADDIW, the chain ends at `pos_ind = 1` and
the SUB / ADD `wf_*` clause pins `flags.val % 2 = 0` at the
chain-end byte; combined with `e7.flags = v.carry_7` and the
boolean range on `carry_7`, this yields `v.carry_7 r_binary = 0`. -/

/-- Derive `v.carry_7 r_binary = 0` from a SUB-shape chain-end byte
    pin (`e_7.op.val = OP_SUB`, `e_7.pos_ind.val = 1`, and
    `e_7.flags = v.carry_7 r_binary`). The SUB `wf` clause at
    pos_ind=1 forces `e_7.flags.val % 2 = 0`; carry_7's boolean
    bound then forces it to be `0`. -/
lemma binary_carry_7_zero_of_chain_end_SUB
    (v : Valid_Binary FGL FGL) (r_binary : ℕ)
    (e7 : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL)
    (h_mult7 : e7.multiplicity = 1)
    (h_op7 : e7.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_SUB)
    (h_pi7 : e7.pos_ind.val = 1)
    (h_flags7 : e7.flags = v.carry_7 r_binary) :
    v.carry_7 r_binary = 0 := by
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e7 h_mult7
  obtain ⟨_, _, _, _, _, _, _, _, h_sub, _⟩ := h_wf
  have h_e7_flags_mod : e7.flags.val % 2 = 0 :=
    (h_sub h_op7).2.2.2 h_pi7
  have h_carry_mod : (v.carry_7 r_binary).val % 2 = 0 := by
    rw [← h_flags7]; exact h_e7_flags_mod
  have h_bool := bin_carry_7_is_boolean v r_binary
  have h_or : v.carry_7 r_binary = 0 ∨ v.carry_7 r_binary = 1 := by
    rcases mul_eq_zero.mp h_bool with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  rcases h_or with h | h
  · exact h
  · exfalso
    have hval : (v.carry_7 r_binary).val = 1 := by rw [h]; rfl
    omega

/-! ## Helper 7: c-lane reconstruction for SUB-shape

`m.c_0 r_main = Σ free_in_c_i * 256^i` (low 4 bytes) and
`m.c_1 r_main = Σ free_in_c_i * 256^(i-4)` (high 4 bytes), after
substituting `v.carry_7 = 0` into the `matches_entry` projection. -/

/-- Reconstruct `m.c_0 r_main` from the 4 low c-bytes once
    `v.carry_7 = 0`. Consumed by SUB / SUBW / ADDW / ADDIW. -/
lemma binary_h_match_clo_of_carry_7_zero
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ}
    (h_c_lo_m : m.c_0 r_main = v.free_in_c_0 r_binary
        + 256 * v.free_in_c_1 r_binary + 65536 * v.free_in_c_2 r_binary
        + 16777216 * v.free_in_c_3 r_binary + v.carry_7 r_binary)
    (h_carry_7_zero : v.carry_7 r_binary = 0) :
    m.c_0 r_main = v.free_in_c_0 r_binary
        + v.free_in_c_1 r_binary * 256 + v.free_in_c_2 r_binary * 65536
        + v.free_in_c_3 r_binary * 16777216 := by
  rw [h_c_lo_m, h_carry_7_zero]; ring

/-- Reconstruct `m.c_1 r_main` from the 4 high c-bytes. Consumed by
    SUB / SUBW / ADDW / ADDIW (and any other Binary 6-field chain
    op whose c-hi recipe is the standard 4-byte sum). -/
lemma binary_h_match_chi_standard
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ}
    (h_c_hi_m : m.c_1 r_main = v.free_in_c_4 r_binary
        + 256 * v.free_in_c_5 r_binary + 65536 * v.free_in_c_6 r_binary
        + 16777216 * v.free_in_c_7 r_binary) :
    m.c_1 r_main = v.free_in_c_4 r_binary
        + v.free_in_c_5 r_binary * 256 + v.free_in_c_6 r_binary * 65536
        + v.free_in_c_7 r_binary * 16777216 := by
  rw [h_c_hi_m]; ring

/-! ## Helper 8: mode-pin discharge for AND / OR / XOR family

For the byte-local-logic Binary opcodes (AND, OR, XOR, and their I-type
companions ANDI, ORI, XORI), the wrapper consumes the
`binary_b_op_or_sext_eq_OP_*` mode-pin axiom (class #6) to derive
`(v.b_op_or_sext r_binary).val = OP_*`. This is a thin wrapper that
combines the `matches_entry` projection with the `b_op_or_sext` axiom
call. Caller picks the right axiom for their opcode. -/

/-- Combine `matches_entry` projection with a `b_op_or_sext` pin
    (trust-ledger lemma) to derive `(v.b_op_or_sext r_binary).val = op_canon`.
    The `pin_axiom` argument is `binary_b_op_or_sext_eq_OP_{AND,OR,XOR}`
    instantiated with `(v, r_binary)`. -/
lemma binary_h_bop_or_sext_via_axiom
    {m : Valid_Main FGL FGL} {v : Valid_Binary FGL FGL}
    {r_main r_binary : ℕ} {n : ℕ} {op_canon : ℕ}
    (h_match : matches_entry (opBus_row_Main m r_main) (opBus_row_Binary v r_binary))
    (h_main_op : m.op r_main = (n : FGL))
    (pin_axiom : v.b_op r_binary + 16 * v.mode32 r_binary = (n : FGL)
                  → (v.b_op_or_sext r_binary).val = op_canon) :
    (v.b_op_or_sext r_binary).val = op_canon :=
  pin_axiom (binary_h_emit_op_of_matches_entry h_match h_main_op)

/-! ## Helper 9: SLT/SLTU c-byte zeros + match-clo/chi reconstruction

For LT / LTU opcodes, every chain entry's `c_byte = 0` (by `wf_LT` /
`wf_LTU`). Thus all 8 `free_in_c_i` columns are zero, and the c-lane
equations collapse: `m.c_0 = e7.flags` and `m.c_1 = 0`. This helper
bundles the 8 zero proofs and the two lane equations. -/

/-- For an LTU chain entry, derive `free_c.val = 0` where
    `e.c_byte = free_c`. -/
lemma binary_c_byte_zero_LTU
    (e : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL)
    (free_c : FGL) (h_c_eq : e.c_byte = free_c)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LTU) :
    free_c.val = 0 := by
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, h_ltu, _⟩ := h_wf
  have h_c0 := (h_ltu h_op).1
  rw [← h_c_eq]; exact h_c0

/-- For an LT chain entry, derive `free_c.val = 0` where
    `e.c_byte = free_c`. -/
lemma binary_c_byte_zero_LT
    (e : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL)
    (free_c : FGL) (h_c_eq : e.c_byte = free_c)
    (h_mult : e.multiplicity = 1)
    (h_op : e.op.val = ZiskFv.Airs.Tables.BinaryTable.OP_LT) :
    free_c.val = 0 := by
  have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e h_mult
  obtain ⟨_, _, _, _, _, h_lt, _⟩ := h_wf
  have h_c0 := (h_lt h_op).1
  rw [← h_c_eq]; exact h_c0

end ZiskFv.EquivCore.Promises
