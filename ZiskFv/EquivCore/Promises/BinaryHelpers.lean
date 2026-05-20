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

/-! ## Helper 4: Binary chain pin — 64-bit destructure bundle

Bundles the 64-bit-mode case of `binary_consumer_byte_match_chain_pin`
into a `Prop`-valued aggregate: 8 entries (as existentials), 8
`consumer_byte_match_chain` witnesses (parameterised on the canonical
64-bit table opcode `op_canon` — typically `OP_SUB`, `OP_LT`, `OP_LTU`),
8 byte-c bounds (`< 256`), 8 cin pins, 7 `pos_ind ≠ 1` pins, 1
`pos_ind = 1` pin (at byte 7), and 8 flag-equations relating each
entry's `.flags` to the Binary AIR's `carry_i` columns. Consumed by
SUB, SLT, SLTU, SLTI, SLTIU wrappers. -/

/-- Aggregate output of unpacking `binary_consumer_byte_match_chain_pin`
    in 64-bit mode. This is a `Prop`-valued conjunction holding the 8
    chain witnesses, c-ranges, cin/pi pins, `pi_7 = 1`, and the 8
    `e_i.flags = v.carry_i` equations. The 8 entries `e0..e7` are
    parameters carried over from the surrounding `∃` in the obtain
    lemma below. -/
structure BinaryChainPinOut64 (v : Valid_Binary FGL FGL) (r_binary : ℕ)
    (op_canon : ℕ)
    (e0 e1 e2 e3 e4 e5 e6 e7 :
      ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL) : Prop where
  chain_0 : consumer_byte_match_chain op_canon
              (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary)
              (v.free_in_c_0 r_binary) e0.cin e0.flags e0.pos_ind
  chain_1 : consumer_byte_match_chain op_canon
              (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary)
              (v.free_in_c_1 r_binary) e1.cin e1.flags e1.pos_ind
  chain_2 : consumer_byte_match_chain op_canon
              (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary)
              (v.free_in_c_2 r_binary) e2.cin e2.flags e2.pos_ind
  chain_3 : consumer_byte_match_chain op_canon
              (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary)
              (v.free_in_c_3 r_binary) e3.cin e3.flags e3.pos_ind
  chain_4 : consumer_byte_match_chain op_canon
              (v.free_in_a_4 r_binary) (v.free_in_b_4 r_binary)
              (v.free_in_c_4 r_binary) e4.cin e4.flags e4.pos_ind
  chain_5 : consumer_byte_match_chain op_canon
              (v.free_in_a_5 r_binary) (v.free_in_b_5 r_binary)
              (v.free_in_c_5 r_binary) e5.cin e5.flags e5.pos_ind
  chain_6 : consumer_byte_match_chain op_canon
              (v.free_in_a_6 r_binary) (v.free_in_b_6 r_binary)
              (v.free_in_c_6 r_binary) e6.cin e6.flags e6.pos_ind
  chain_7 : consumer_byte_match_chain op_canon
              (v.free_in_a_7 r_binary) (v.free_in_b_7 r_binary)
              (v.free_in_c_7 r_binary) e7.cin e7.flags e7.pos_ind
  c0_lt : (v.free_in_c_0 r_binary).val < 256
  c1_lt : (v.free_in_c_1 r_binary).val < 256
  c2_lt : (v.free_in_c_2 r_binary).val < 256
  c3_lt : (v.free_in_c_3 r_binary).val < 256
  c4_lt : (v.free_in_c_4 r_binary).val < 256
  c5_lt : (v.free_in_c_5 r_binary).val < 256
  c6_lt : (v.free_in_c_6 r_binary).val < 256
  c7_lt : (v.free_in_c_7 r_binary).val < 256
  cin0_eq : e0.cin.val = 0
  cin1_eq : e1.cin.val = e0.flags.val % 2
  cin2_eq : e2.cin.val = e1.flags.val % 2
  cin3_eq : e3.cin.val = e2.flags.val % 2
  cin4_eq : e4.cin.val = e3.flags.val % 2
  cin5_eq : e5.cin.val = e4.flags.val % 2
  cin6_eq : e6.cin.val = e5.flags.val % 2
  cin7_eq : e7.cin.val = e6.flags.val % 2
  pi0_ne : e0.pos_ind.val ≠ 1
  pi1_ne : e1.pos_ind.val ≠ 1
  pi2_ne : e2.pos_ind.val ≠ 1
  pi3_ne : e3.pos_ind.val ≠ 1
  pi4_ne : e4.pos_ind.val ≠ 1
  pi5_ne : e5.pos_ind.val ≠ 1
  pi6_ne : e6.pos_ind.val ≠ 1
  pi7_eq : e7.pos_ind.val = 1
  flags0 : e0.flags = v.carry_0 r_binary
  flags1 : e1.flags = v.carry_1 r_binary
  flags2 : e2.flags = v.carry_2 r_binary
  flags3 : e3.flags = v.carry_3 r_binary
  flags4 : e4.flags = v.carry_4 r_binary
  flags5 : e5.flags = v.carry_5 r_binary
  flags6 : e6.flags = v.carry_6 r_binary
  flags7 : e7.flags = v.carry_7 r_binary
  mult0_eq : e0.multiplicity = 1
  mult1_eq : e1.multiplicity = 1
  mult2_eq : e2.multiplicity = 1
  mult3_eq : e3.multiplicity = 1
  mult4_eq : e4.multiplicity = 1
  mult5_eq : e5.multiplicity = 1
  mult6_eq : e6.multiplicity = 1
  mult7_eq : e7.multiplicity = 1
  op0_eq : e0.op.val = op_canon
  op1_eq : e1.op.val = op_canon
  op2_eq : e2.op.val = op_canon
  op3_eq : e3.op.val = op_canon
  op4_eq : e4.op.val = op_canon
  op5_eq : e5.op.val = op_canon
  op6_eq : e6.op.val = op_canon
  op7_eq : e7.op.val = op_canon
  c0_eq : e0.c_byte = v.free_in_c_0 r_binary
  c1_eq : e1.c_byte = v.free_in_c_1 r_binary
  c2_eq : e2.c_byte = v.free_in_c_2 r_binary
  c3_eq : e3.c_byte = v.free_in_c_3 r_binary
  c4_eq : e4.c_byte = v.free_in_c_4 r_binary
  c5_eq : e5.c_byte = v.free_in_c_5 r_binary
  c6_eq : e6.c_byte = v.free_in_c_6 r_binary
  c7_eq : e7.c_byte = v.free_in_c_7 r_binary

/-- Unpack `binary_consumer_byte_match_chain_pin` for 64-bit-mode
    opcodes (`op_emit ∈ {0x06, 0x07, 0x0B}`, matching `op_canon`).
    Returns the 8 entries as existentials plus a `BinaryChainPinOut64`
    bundling everything wrappers need to discharge their plumbing in
    one destructure. -/
lemma binary_chain_pin_obtain_64
    (v : Valid_Binary FGL FGL) (r_binary : ℕ) (op_canon : ℕ)
    (h_branch_64 : op_canon = 0x06 ∨ op_canon = 0x07 ∨ op_canon = 0x0B)
    (h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary
        = ((op_canon : ℕ) : FGL)) :
    ∃ e0 e1 e2 e3 e4 e5 e6 e7 :
      ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL,
      BinaryChainPinOut64 v r_binary op_canon e0 e1 e2 e3 e4 e5 e6 e7 := by
  obtain ⟨e0', e1', e2', e3', e4', e5', e6', e7',
          h_b0, h_b1, h_b2, h_b3, h_b4, h_b5, h_b6, h_b7,
          h_cin0_eq, h_cin1_eq, h_cin2_eq, h_cin3_eq,
          h_cin4_eq, h_cin5_eq, h_cin6_eq, h_cin7_eq,
          h_pi0_ne, h_pi1_ne, h_pi2_ne,
          h_pi_64, _h_pi_W⟩ :=
    binary_consumer_byte_match_chain_pin v r_binary op_canon h_emit_op
  obtain ⟨h_mult0, h_a0, h_b_0, h_c0, h_flags0, h_op0_64, _, _⟩ := h_b0
  obtain ⟨h_mult1, h_a1, h_b_1, h_c1, h_flags1, h_op1_64, _, _⟩ := h_b1
  obtain ⟨h_mult2, h_a2, h_b_2, h_c2, h_flags2, h_op2_64, _, _⟩ := h_b2
  obtain ⟨h_mult3, h_a3, h_b_3, h_c3, h_flags3, h_op3_64, _, _⟩ := h_b3
  obtain ⟨h_mult4, h_a4, h_b_4, h_c4, h_flags4, h_op4_64⟩ := h_b4
  obtain ⟨h_mult5, h_a5, h_b_5, h_c5, h_flags5, h_op5_64⟩ := h_b5
  obtain ⟨h_mult6, h_a6, h_b_6, h_c6, h_flags6, h_op6_64⟩ := h_b6
  obtain ⟨h_mult7, h_a7, h_b_7, h_c7, h_flags7, h_op7_64⟩ := h_b7
  have h_op0 : e0'.op.val = op_canon := h_op0_64 h_branch_64
  have h_op1 : e1'.op.val = op_canon := h_op1_64 h_branch_64
  have h_op2 : e2'.op.val = op_canon := h_op2_64 h_branch_64
  have h_op3 : e3'.op.val = op_canon := h_op3_64 h_branch_64
  have h_op4 : e4'.op.val = op_canon := h_op4_64 h_branch_64
  have h_op5 : e5'.op.val = op_canon := h_op5_64 h_branch_64
  have h_op6 : e6'.op.val = op_canon := h_op6_64 h_branch_64
  have h_op7 : e7'.op.val = op_canon := h_op7_64 h_branch_64
  obtain ⟨h_pi3_ne, h_pi4_ne, h_pi5_ne, h_pi6_ne, h_pi7_eq⟩ := h_pi_64 h_branch_64
  have hc0 : (v.free_in_c_0 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e0' h_mult0
    have := h_wf.1.2.2.1
    rwa [h_c0] at this
  have hc1 : (v.free_in_c_1 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e1' h_mult1
    have := h_wf.1.2.2.1
    rwa [h_c1] at this
  have hc2 : (v.free_in_c_2 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e2' h_mult2
    have := h_wf.1.2.2.1
    rwa [h_c2] at this
  have hc3 : (v.free_in_c_3 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e3' h_mult3
    have := h_wf.1.2.2.1
    rwa [h_c3] at this
  have hc4 : (v.free_in_c_4 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e4' h_mult4
    have := h_wf.1.2.2.1
    rwa [h_c4] at this
  have hc5 : (v.free_in_c_5 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e5' h_mult5
    have := h_wf.1.2.2.1
    rwa [h_c5] at this
  have hc6 : (v.free_in_c_6 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e6' h_mult6
    have := h_wf.1.2.2.1
    rwa [h_c6] at this
  have hc7 : (v.free_in_c_7 r_binary).val < 256 := by
    have h_wf := ZiskFv.Airs.Tables.BinaryTable.bin_table_consumer_wf e7' h_mult7
    have := h_wf.1.2.2.1
    rwa [h_c7] at this
  refine ⟨e0', e1', e2', e3', e4', e5', e6', e7', ?_⟩
  exact
    { chain_0 := ⟨e0', h_mult0, h_op0, h_a0, h_b_0, h_c0, rfl, rfl, rfl⟩
      chain_1 := ⟨e1', h_mult1, h_op1, h_a1, h_b_1, h_c1, rfl, rfl, rfl⟩
      chain_2 := ⟨e2', h_mult2, h_op2, h_a2, h_b_2, h_c2, rfl, rfl, rfl⟩
      chain_3 := ⟨e3', h_mult3, h_op3, h_a3, h_b_3, h_c3, rfl, rfl, rfl⟩
      chain_4 := ⟨e4', h_mult4, h_op4, h_a4, h_b_4, h_c4, rfl, rfl, rfl⟩
      chain_5 := ⟨e5', h_mult5, h_op5, h_a5, h_b_5, h_c5, rfl, rfl, rfl⟩
      chain_6 := ⟨e6', h_mult6, h_op6, h_a6, h_b_6, h_c6, rfl, rfl, rfl⟩
      chain_7 := ⟨e7', h_mult7, h_op7, h_a7, h_b_7, h_c7, rfl, rfl, rfl⟩
      c0_lt := hc0, c1_lt := hc1, c2_lt := hc2, c3_lt := hc3
      c4_lt := hc4, c5_lt := hc5, c6_lt := hc6, c7_lt := hc7
      cin0_eq := h_cin0_eq, cin1_eq := h_cin1_eq, cin2_eq := h_cin2_eq
      cin3_eq := h_cin3_eq, cin4_eq := h_cin4_eq, cin5_eq := h_cin5_eq
      cin6_eq := h_cin6_eq, cin7_eq := h_cin7_eq
      pi0_ne := h_pi0_ne, pi1_ne := h_pi1_ne, pi2_ne := h_pi2_ne
      pi3_ne := h_pi3_ne, pi4_ne := h_pi4_ne, pi5_ne := h_pi5_ne
      pi6_ne := h_pi6_ne, pi7_eq := h_pi7_eq
      flags0 := h_flags0, flags1 := h_flags1, flags2 := h_flags2
      flags3 := h_flags3, flags4 := h_flags4, flags5 := h_flags5
      flags6 := h_flags6, flags7 := h_flags7
      mult0_eq := h_mult0, mult1_eq := h_mult1, mult2_eq := h_mult2
      mult3_eq := h_mult3, mult4_eq := h_mult4, mult5_eq := h_mult5
      mult6_eq := h_mult6, mult7_eq := h_mult7
      op0_eq := h_op0, op1_eq := h_op1, op2_eq := h_op2, op3_eq := h_op3
      op4_eq := h_op4, op5_eq := h_op5, op6_eq := h_op6, op7_eq := h_op7
      c0_eq := h_c0, c1_eq := h_c1, c2_eq := h_c2, c3_eq := h_c3
      c4_eq := h_c4, c5_eq := h_c5, c6_eq := h_c6, c7_eq := h_c7 }

/-! ## Helper 5: Binary chain pin — W-mode destructure bundle

Bundles the W-mode (32-bit-suffix) case of
`binary_consumer_byte_match_chain_pin` (`op_emit ∈ {0x1A, 0x1B}`)
into a `Prop`-valued aggregate analogous to `BinaryChainPinOut64`.
Differences:

* Only the first 4 bytes have meaningful chain-witness ops (pinned
  to `OP_ADD = 0x0A` for ADD_W or `OP_SUB = 0x0B` for SUB_W); bytes
  4..7 are SEXT-byte slots, not exposed as chain entries.
* The position-indicator pin is `pos_ind_3 = 1` (chain ends at byte 3).
* Only 4 cin pins (cin0..cin3) are exposed; higher bytes are not
  consumed by W-mode wrappers.

Consumed by ADDW, SUBW, ADDIW wrappers. -/

/-- Aggregate output for the W-mode chain unpack. Holds 4 chain
    witnesses + 4 byte-flag equations + 4 c-byte ranges + 4 cin
    pins + 3 `pos_ind ≠ 1` pins + `pos_ind_3 = 1`. `op_canon` is
    the canonical W-mode chain opcode (`OP_ADD = 0x0A` for ADD_W,
    `OP_SUB = 0x0B` for SUB_W). -/
structure BinaryChainPinOutW (v : Valid_Binary FGL FGL) (r_binary : ℕ)
    (op_canon : ℕ)
    (e0 e1 e2 e3 : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL) : Prop where
  chain_0 : consumer_byte_match_chain op_canon
              (v.free_in_a_0 r_binary) (v.free_in_b_0 r_binary)
              (v.free_in_c_0 r_binary) e0.cin e0.flags e0.pos_ind
  chain_1 : consumer_byte_match_chain op_canon
              (v.free_in_a_1 r_binary) (v.free_in_b_1 r_binary)
              (v.free_in_c_1 r_binary) e1.cin e1.flags e1.pos_ind
  chain_2 : consumer_byte_match_chain op_canon
              (v.free_in_a_2 r_binary) (v.free_in_b_2 r_binary)
              (v.free_in_c_2 r_binary) e2.cin e2.flags e2.pos_ind
  chain_3 : consumer_byte_match_chain op_canon
              (v.free_in_a_3 r_binary) (v.free_in_b_3 r_binary)
              (v.free_in_c_3 r_binary) e3.cin e3.flags e3.pos_ind
  cin0_eq : e0.cin.val = 0
  cin1_eq : e1.cin.val = e0.flags.val % 2
  cin2_eq : e2.cin.val = e1.flags.val % 2
  cin3_eq : e3.cin.val = e2.flags.val % 2
  pi0_ne : e0.pos_ind.val ≠ 1
  pi1_ne : e1.pos_ind.val ≠ 1
  pi2_ne : e2.pos_ind.val ≠ 1
  pi3_eq : e3.pos_ind.val = 1
  flags0 : e0.flags = v.carry_0 r_binary
  flags1 : e1.flags = v.carry_1 r_binary
  flags2 : e2.flags = v.carry_2 r_binary
  flags3 : e3.flags = v.carry_3 r_binary
  mult3_eq : e3.multiplicity = 1
  op3_eq : e3.op.val = op_canon

/-- Unpack `binary_consumer_byte_match_chain_pin` for W-mode opcodes
    (`op_emit ∈ {0x1A, 0x1B}`, pinning each byte's `e_i.op.val` to
    `op_canon` = `0x0A` for ADD_W or `0x0B` for SUB_W). Returns the
    4 entries as existentials plus a `BinaryChainPinOutW` bundle.

    The `op_emit_to_canon` argument is the W-mode op-pin lookup —
    for ADDW it's `h_byte_op_AW h_branch_addw : e_i.op.val = 0x0A`;
    for SUBW it's `h_byte_op_SW h_branch_subw : e_i.op.val = 0x0B`. -/
lemma binary_chain_pin_obtain_W
    (v : Valid_Binary FGL FGL) (r_binary : ℕ) (op_emit op_canon : ℕ)
    (h_branch_w : op_emit = 0x1A ∨ op_emit = 0x1B)
    (h_canon_match :
      (op_emit = 0x1A → op_canon = 0x0A) ∧
      (op_emit = 0x1B → op_canon = 0x0B))
    (h_emit_op : v.b_op r_binary + 16 * v.mode32 r_binary
        = ((op_emit : ℕ) : FGL)) :
    ∃ e0 e1 e2 e3 : ZiskFv.Airs.Tables.BinaryTable.BinaryTableEntry FGL,
      BinaryChainPinOutW v r_binary op_canon e0 e1 e2 e3 := by
  obtain ⟨e0', e1', e2', e3', _e4', _e5', _e6', _e7',
          h_b0, h_b1, h_b2, h_b3, _h_b4, _h_b5, _h_b6, _h_b7,
          h_cin0_eq, h_cin1_eq, h_cin2_eq, h_cin3_eq,
          _h_cin4_eq, _h_cin5_eq, _h_cin6_eq, _h_cin7_eq,
          h_pi0_ne, h_pi1_ne, h_pi2_ne,
          _h_pi_64, h_pi_W⟩ :=
    binary_consumer_byte_match_chain_pin v r_binary op_emit h_emit_op
  obtain ⟨h_mult0, h_a0, h_b_0, h_c0, h_flags0, _h_op0_64, h_op0_AW, h_op0_SW⟩ := h_b0
  obtain ⟨h_mult1, h_a1, h_b_1, h_c1, h_flags1, _h_op1_64, h_op1_AW, h_op1_SW⟩ := h_b1
  obtain ⟨h_mult2, h_a2, h_b_2, h_c2, h_flags2, _h_op2_64, h_op2_AW, h_op2_SW⟩ := h_b2
  obtain ⟨h_mult3, h_a3, h_b_3, h_c3, h_flags3, _h_op3_64, h_op3_AW, h_op3_SW⟩ := h_b3
  have h_op0 : e0'.op.val = op_canon := by
    rcases h_branch_w with h | h
    · rw [h_canon_match.1 h]; exact h_op0_AW h
    · rw [h_canon_match.2 h]; exact h_op0_SW h
  have h_op1 : e1'.op.val = op_canon := by
    rcases h_branch_w with h | h
    · rw [h_canon_match.1 h]; exact h_op1_AW h
    · rw [h_canon_match.2 h]; exact h_op1_SW h
  have h_op2 : e2'.op.val = op_canon := by
    rcases h_branch_w with h | h
    · rw [h_canon_match.1 h]; exact h_op2_AW h
    · rw [h_canon_match.2 h]; exact h_op2_SW h
  have h_op3 : e3'.op.val = op_canon := by
    rcases h_branch_w with h | h
    · rw [h_canon_match.1 h]; exact h_op3_AW h
    · rw [h_canon_match.2 h]; exact h_op3_SW h
  have h_pi3_eq : e3'.pos_ind.val = 1 := h_pi_W h_branch_w
  refine ⟨e0', e1', e2', e3', ?_⟩
  exact
    { chain_0 := ⟨e0', h_mult0, h_op0, h_a0, h_b_0, h_c0, rfl, rfl, rfl⟩
      chain_1 := ⟨e1', h_mult1, h_op1, h_a1, h_b_1, h_c1, rfl, rfl, rfl⟩
      chain_2 := ⟨e2', h_mult2, h_op2, h_a2, h_b_2, h_c2, rfl, rfl, rfl⟩
      chain_3 := ⟨e3', h_mult3, h_op3, h_a3, h_b_3, h_c3, rfl, rfl, rfl⟩
      cin0_eq := h_cin0_eq, cin1_eq := h_cin1_eq, cin2_eq := h_cin2_eq, cin3_eq := h_cin3_eq
      pi0_ne := h_pi0_ne, pi1_ne := h_pi1_ne, pi2_ne := h_pi2_ne, pi3_eq := h_pi3_eq
      flags0 := h_flags0, flags1 := h_flags1, flags2 := h_flags2, flags3 := h_flags3
      mult3_eq := h_mult3, op3_eq := h_op3 }

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
