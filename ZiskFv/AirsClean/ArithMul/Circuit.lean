import ZiskFv.AirsClean.ArithMul.Constraints
import ZiskFv.AirsClean.ArithMul.Soundness
import ZiskFv.Airs.Arith.CarryChainCompleteness
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# ArithMul Clean Component (Phase C3)

Packages ZisK's Arith AIR (MUL-mode carry-chain view) as a Clean
`Air.Flat.Component`:

* `arithMulElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean`. Its `main`
  emits the 11 `assertZero` carry-chain constraints (named-form `6/7/8`
  + `31..38`) and the operation-bus proves-side `push`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` (plan D-2:
  a Component carries no soundness-assumptions — the ArithMul `soundness`
  proof needs none; the 11-clause carry-chain `Spec` follows from the 11
  definitional `assertZero` constraints alone, by `linear_combination`).
  `soundness` discharges the ArithMul carry-chain relation; completeness is
  proved for unsigned rows built from two 64-bit operands.
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Completeness is a constructibility claim for rows equal to `arithMulRowOf a b free`
with `a < 65536^4` and `b < 65536^4`: the builder sets the unsigned flags, computes
the product chunks, and chooses the unique field carries solving the 65536-base
chain equations. It does not claim that arbitrary input rows are honest ArithMul
executions, and signed/W-mode rows remain a follow-up disjunct.
-/

namespace ZiskFv.AirsClean.ArithMul

open Goldilocks
open ZiskFv.Channels.OperationBus (OpBusChannel)
open Air.Flat
open ZiskFv.Airs.ArithCarryChainCompleteness

/-- Columns not constrained by the unsigned carry-chain completeness slice. -/
structure ArithMulFreeCols where
  sext : FGL
  div_by_zero : FGL
  div_overflow : FGL
  main_div : FGL
  main_mul : FGL
  signed : FGL
  range_ab : FGL
  range_cd : FGL
  op : FGL
  bus_res1 : FGL
  multiplicity : FGL

def arithMulE0 (a b : ℕ) : FGL :=
  (chunk16 a 0 : FGL) * (chunk16 b 0 : FGL) - (chunk16 (a * b) 0 : FGL)

def arithMulE1 (a b : ℕ) : FGL :=
  (chunk16 a 1 : FGL) * (chunk16 b 0 : FGL) +
    (chunk16 a 0 : FGL) * (chunk16 b 1 : FGL) - (chunk16 (a * b) 1 : FGL)

def arithMulE2 (a b : ℕ) : FGL :=
  (chunk16 a 2 : FGL) * (chunk16 b 0 : FGL) +
    (chunk16 a 1 : FGL) * (chunk16 b 1 : FGL) +
    (chunk16 a 0 : FGL) * (chunk16 b 2 : FGL) - (chunk16 (a * b) 2 : FGL)

def arithMulE3 (a b : ℕ) : FGL :=
  (chunk16 a 3 : FGL) * (chunk16 b 0 : FGL) +
    (chunk16 a 2 : FGL) * (chunk16 b 1 : FGL) +
    (chunk16 a 1 : FGL) * (chunk16 b 2 : FGL) +
    (chunk16 a 0 : FGL) * (chunk16 b 3 : FGL) - (chunk16 (a * b) 3 : FGL)

def arithMulE4 (a b : ℕ) : FGL :=
  (chunk16 a 3 : FGL) * (chunk16 b 1 : FGL) +
    (chunk16 a 2 : FGL) * (chunk16 b 2 : FGL) +
    (chunk16 a 1 : FGL) * (chunk16 b 3 : FGL) - (chunk16 (a * b) 4 : FGL)

def arithMulE5 (a b : ℕ) : FGL :=
  (chunk16 a 3 : FGL) * (chunk16 b 2 : FGL) +
    (chunk16 a 2 : FGL) * (chunk16 b 3 : FGL) - (chunk16 (a * b) 5 : FGL)

def arithMulE6 (a b : ℕ) : FGL :=
  (chunk16 a 3 : FGL) * (chunk16 b 3 : FGL) - (chunk16 (a * b) 6 : FGL)

def arithMulE7 (a b : ℕ) : FGL :=
  -(chunk16 (a * b) 7 : FGL)

lemma arithMulProduct_lt (a b : ℕ) (ha : a < 65536 ^ 4) (hb : b < 65536 ^ 4) :
    a * b < 65536 ^ 8 := by
  nlinarith [Nat.mul_lt_mul'' ha hb]

lemma arithMulChainSum_zero (a b : ℕ) (ha : a < 65536 ^ 4) (hb : b < 65536 ^ 4) :
    arithMulE0 a b + arithMulE1 a b * (65536 : FGL) +
      arithMulE2 a b * (65536 : FGL) ^ 2 + arithMulE3 a b * (65536 : FGL) ^ 3 +
      arithMulE4 a b * (65536 : FGL) ^ 4 + arithMulE5 a b * (65536 : FGL) ^ 5 +
      arithMulE6 a b * (65536 : FGL) ^ 6 + arithMulE7 a b * (65536 : FGL) ^ 7 =
        0 := by
  have hab := arithMulProduct_lt a b ha hb
  have ha_decomp := fgl_decomp4 a ha
  have hb_decomp := fgl_decomp4 b hb
  have hp_decomp := fgl_decomp8 (a * b) hab
  have hmul : (a : FGL) * (b : FGL) = ((a * b : ℕ) : FGL) := by norm_num
  rw [ha_decomp, hb_decomp, hp_decomp] at hmul
  unfold arithMulE0 arithMulE1 arithMulE2 arithMulE3 arithMulE4 arithMulE5 arithMulE6 arithMulE7
  linear_combination hmul

/-- Honest unsigned ArithMul row built from two 64-bit natural operands. -/
def arithMulRowOf (a b : ℕ) (free : ArithMulFreeCols) : ArithMulRow FGL :=
  { chunks :=
      { a_0 := (chunk16 a 0 : FGL)
        a_1 := (chunk16 a 1 : FGL)
        a_2 := (chunk16 a 2 : FGL)
        a_3 := (chunk16 a 3 : FGL)
        b_0 := (chunk16 b 0 : FGL)
        b_1 := (chunk16 b 1 : FGL)
        b_2 := (chunk16 b 2 : FGL)
        b_3 := (chunk16 b 3 : FGL)
        c_0 := (chunk16 (a * b) 0 : FGL)
        c_1 := (chunk16 (a * b) 1 : FGL)
        c_2 := (chunk16 (a * b) 2 : FGL)
        c_3 := (chunk16 (a * b) 3 : FGL)
        d_0 := (chunk16 (a * b) 4 : FGL)
        d_1 := (chunk16 (a * b) 5 : FGL)
        d_2 := (chunk16 (a * b) 6 : FGL)
        d_3 := (chunk16 (a * b) 7 : FGL) }
    flags :=
      { na := 0
        nb := 0
        nr := 0
        np := 0
        sext := free.sext
        m32 := 0
        div := 0
        div_by_zero := free.div_by_zero
        div_overflow := free.div_overflow
        main_div := free.main_div
        main_mul := free.main_mul
        signed := free.signed
        range_ab := free.range_ab
        range_cd := free.range_cd
        op := free.op
        bus_res1 := free.bus_res1
        multiplicity := free.multiplicity }
    carries :=
      { carry_0 := cc0 65536 (arithMulE0 a b)
        carry_1 := cc1 65536 (arithMulE0 a b) (arithMulE1 a b)
        carry_2 := cc2 65536 (arithMulE0 a b) (arithMulE1 a b) (arithMulE2 a b)
        carry_3 := cc3 65536 (arithMulE0 a b) (arithMulE1 a b) (arithMulE2 a b)
          (arithMulE3 a b)
        carry_4 := cc4 65536 (arithMulE0 a b) (arithMulE1 a b) (arithMulE2 a b)
          (arithMulE3 a b) (arithMulE4 a b)
        carry_5 := cc5 65536 (arithMulE0 a b) (arithMulE1 a b) (arithMulE2 a b)
          (arithMulE3 a b) (arithMulE4 a b) (arithMulE5 a b)
        carry_6 := cc6 65536 (arithMulE0 a b) (arithMulE1 a b) (arithMulE2 a b)
          (arithMulE3 a b) (arithMulE4 a b) (arithMulE5 a b) (arithMulE6 a b)
        fab := 1
        na_fb := 0
        nb_fa := 0 } }

set_option maxHeartbeats 4000000 in
/-- ArithMul as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the 11-clause carry-chain `Spec` follows from the 11 definitional
    `assertZero` constraints alone (plan D-2 / F-4), and completeness constructs
    unsigned rows from two 64-bit operands.

    The `soundness` field is **adapted from** `ArithMul.soundness`
    (`Soundness.lean`) — same per-clause `linear_combination` discharge,
    reshaped to consume the `circuit_norm`-normalized constraints
    directly. -/
def circuit : GeneralFormalCircuit FGL ArithMulRow unit :=
  { arithMulElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => Spec row
    -- Completeness covers unsigned rows built from two 64-bit operands.
    ProverAssumptions := fun row _ _ =>
      ∃ a b free, a < 65536 ^ 4 ∧ b < 65536 ^ 4 ∧ row = arithMulRowOf a b free
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the ArithMul carry-chain relation: the 11 definitional
        -- constraints imply the 11-clause `Spec`.
        obtain ⟨h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34,
                h_c35, h_c36, h_c37, h_c38⟩ := h_holds
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · linear_combination h_c6
        · linear_combination h_c7
        · linear_combination h_c8
        · linear_combination h_c31
        · linear_combination h_c32
        · linear_combination h_c33
        · linear_combination h_c34
        · linear_combination h_c35
        · linear_combination h_c36
        · linear_combination h_c37
        · linear_combination h_c38
      · -- the op-bus push's requirement: `OpBusChannel.Guarantees` is `True`.
        intro _
        trivial
    completeness := by
      circuit_proof_start_core
      simp only [main, circuit_norm, primaryOpBusMessageExpr, OpBusChannel]
      obtain ⟨a, b, free, ha, hb, hrow⟩ := h_assumptions
      rw [hrow] at h_input
      simp only [circuit_norm] at h_input
      injection h_input with h_chunks h_flags h_carries
      injection h_chunks with h_a_0 h_a_1 h_a_2 h_a_3 h_b_0 h_b_1 h_b_2 h_b_3
        h_c_0 h_c_1 h_c_2 h_c_3 h_d_0 h_d_1 h_d_2 h_d_3
      injection h_flags with h_na h_nb h_nr h_np h_sext h_m32 h_div h_div_by_zero
        h_div_overflow h_main_div h_main_mul h_signed h_range_ab h_range_cd h_op h_bus_res1
        h_multiplicity
      injection h_carries with h_carry_0 h_carry_1 h_carry_2 h_carry_3 h_carry_4
        h_carry_5 h_carry_6 h_fab h_na_fb h_nb_fa
      subst_vars
      simp only [h_a_0, h_a_1, h_a_2, h_a_3, h_b_0, h_b_1, h_b_2, h_b_3,
        h_c_0, h_c_1, h_c_2, h_c_3, h_d_0, h_d_1, h_d_2, h_d_3, h_na, h_nb,
        h_nr, h_np, h_m32, h_div, h_carry_0, h_carry_1, h_carry_2, h_carry_3,
        h_carry_4, h_carry_5, h_carry_6, h_fab, h_na_fb, h_nb_fa]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · ring
      · ring
      · ring
      · simpa [arithMulE0, sub_eq_add_neg] using
          (chain_eq_0 (B := (65536 : FGL)) (e0 := arithMulE0 a b) fgl_65536_ne_zero)
      · simpa [arithMulE1, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_1 (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) fgl_65536_ne_zero)
      · simpa [arithMulE2, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_2 (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) (e2 := arithMulE2 a b) fgl_65536_ne_zero)
      · simpa [arithMulE3, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_3 (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) (e2 := arithMulE2 a b) (e3 := arithMulE3 a b)
            fgl_65536_ne_zero)
      · simpa [arithMulE4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_4 (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) (e2 := arithMulE2 a b) (e3 := arithMulE3 a b)
            (e4 := arithMulE4 a b) fgl_65536_ne_zero)
      · simpa [arithMulE5, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_5 (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) (e2 := arithMulE2 a b) (e3 := arithMulE3 a b)
            (e4 := arithMulE4 a b) (e5 := arithMulE5 a b) fgl_65536_ne_zero)
      · simpa [arithMulE6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_eq_6 (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) (e2 := arithMulE2 a b) (e3 := arithMulE3 a b)
            (e4 := arithMulE4 a b) (e5 := arithMulE5 a b) (e6 := arithMulE6 a b)
            fgl_65536_ne_zero)
      · simpa [arithMulE7, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (chain_last (B := (65536 : FGL)) (e0 := arithMulE0 a b)
            (e1 := arithMulE1 a b) (e2 := arithMulE2 a b) (e3 := arithMulE3 a b)
            (e4 := arithMulE4 a b) (e5 := arithMulE5 a b) (e6 := arithMulE6 a b)
            (e7 := arithMulE7 a b) fgl_65536_ne_zero
            (arithMulChainSum_zero a b ha hb)) }

set_option maxHeartbeats 4000000 in
/-- Lookup-aware ArithMul component circuit. Its soundness exposes the full
    carry-chain plus ArithTable membership contract; completeness is intentionally
    vacuous until an honest lookup-aware row constructor is added. -/
def circuitWithArithTable : GeneralFormalCircuit FGL ArithMulRow unit :=
  { arithMulWithArithTableElaborated with
    exposedChannels row _ :=
      expose OpBusChannel [OpBusChannel.pushed (primaryOpBusMessageExpr row)]
    channelsLawful := by
      simp only [circuit_norm, mainWithArithTable, main, primaryOpBusMessageExpr,
        OpBusChannel]
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => FullSpec row
    ProverAssumptions := fun _ _ _ => False
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · obtain ⟨h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34,
                h_c35, h_c36, h_c37, h_c38, h_c46, h_lookup⟩ := h_holds
        refine ⟨?_, ?_, ?_⟩
        · -- Carry-chain Spec (11 clauses).
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · linear_combination h_c6
          · linear_combination h_c7
          · linear_combination h_c8
          · linear_combination h_c31
          · linear_combination h_c32
          · linear_combination h_c33
          · linear_combination h_c34
          · linear_combination h_c35
          · linear_combination h_c36
          · linear_combination h_c37
          · linear_combination h_c38
        · -- ArithTableSpec: from the ROM lookup.
          obtain ⟨_, h_flags, _⟩ := h_input
          obtain ⟨h_na, h_nb, h_nr, h_np, h_sext, h_m32, h_div, h_div_by_zero,
            h_div_overflow, h_main_div, h_main_mul, h_signed, h_range_ab, h_range_cd,
            h_op, _h_bus_res1, _h_multiplicity⟩ := h_flags
          simpa [ArithTableSpec, arithTableRow, Lookup.Soundness, Table.fromStatic,
            StaticTable.toTable, Table.toRaw, h_op, h_m32, h_div, h_na, h_nb, h_np,
            h_nr, h_sext, h_div_by_zero, h_div_overflow, h_main_mul, h_main_div,
            h_signed, h_range_ab, h_range_cd] using h_lookup
        · -- C46Spec: bus_res1 mux equation (constraint 46, arith.pil:262).
          linear_combination h_c46
      · intro _
        trivial
    completeness := by
      circuit_proof_start_core
      exact False.elim h_assumptions }

/-- ArithMul as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

/-- Lookup-aware ArithMul component exposing `FullSpec`. -/
def componentWithArithTable : Air.Flat.Component FGL := ⟨ circuitWithArithTable ⟩

/-- The lookup-aware ArithMul circuit participates only in the operation bus. -/
theorem circuitWithArithTable_channels :
    circuitWithArithTable.channels = [OpBusChannel.toRaw] := by
  rfl

/-- The lookup-aware ArithMul component participates only in the operation bus. -/
theorem componentWithArithTable_channels :
    componentWithArithTable.circuit.channels = [OpBusChannel.toRaw] := by
  simpa [componentWithArithTable] using circuitWithArithTable_channels

/-- Project the generic Clean component `Spec` to the concrete ArithMul row
    `Spec`. -/
theorem component_spec (env : Environment FGL) :
    component.Spec env = Spec (component.rowInput env) := by
  rfl

/-- Project the lookup-aware generic Clean component `Spec` to `FullSpec`. -/
theorem componentWithArithTable_spec (env : Environment FGL) :
    componentWithArithTable.Spec env =
      FullSpec (componentWithArithTable.rowInput env) := by
  rfl

set_option maxHeartbeats 1000000 in
/-- The ArithMul component exposes exactly its primary operation-bus
    provider interaction. -/
theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (primaryOpBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (primaryOpBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, arithMulElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil,
    primaryOpBusMessageExpr]

set_option maxHeartbeats 1000000 in
/-- The lookup-aware ArithMul component exposes the same primary operation-bus
    provider interaction as the carry-chain-only component. -/
theorem componentWithArithTable_interactionsWith_opBus :
    componentWithArithTable.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed
        (primaryOpBusMessageExpr componentWithArithTable.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed
        (primaryOpBusMessageExpr componentWithArithTable.rowInputVar)).toRaw)]⟩ ∈
    componentWithArithTable.exposedChannels
  simp only [componentWithArithTable, circuitWithArithTable, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil,
    primaryOpBusMessageExpr]

set_option maxHeartbeats 1000000 in
/-- The ArithMul `Spec` for a row, derived **through the Clean Component
    `circuit`** — its proven `soundness` field — rather than through
    `ArithMul.soundness` directly. Any consumer genuinely depends on
    `circuit`; this is the C3 re-root entry point that makes
    `AirsClean/ArithMul/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the `operations`
    `whnf` explodes — plan finding F-3); the working idiom is to normalize
    its type with the `circuit_norm` simp set first, then feed it a
    constant-expression row. Mirrors `BinaryAdd.spec_via_component` and
    `MemAlignByte.spec_via_component`. -/
theorem spec_via_component (row : ArithMulRow FGL)
    (h_c6 : row.carries.fab - ((1 - 2 * row.flags.na) - 2 * row.flags.nb
              + 4 * row.flags.na * row.flags.nb) = 0)
    (h_c7 : row.carries.na_fb - row.flags.na * (1 - 2 * row.flags.nb) = 0)
    (h_c8 : row.carries.nb_fa - row.flags.nb * (1 - 2 * row.flags.na) = 0)
    (h_c31 :
        row.carries.fab * row.chunks.a_0 * row.chunks.b_0
        - row.chunks.c_0
        + 2 * row.flags.np * row.chunks.c_0
        + row.flags.div * row.chunks.d_0
        - 2 * row.flags.nr * row.chunks.d_0
        - row.carries.carry_0 * 65536 = 0)
    (h_c32 :
        row.carries.fab * row.chunks.a_1 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_1
        - row.chunks.c_1
        + 2 * row.flags.np * row.chunks.c_1
        + row.flags.div * row.chunks.d_1
        - 2 * row.flags.nr * row.chunks.d_1
        + row.carries.carry_0
        - row.carries.carry_1 * 65536 = 0)
    (h_c33 :
        row.carries.fab * row.chunks.a_2 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_1 * row.chunks.b_1
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_2
        + row.chunks.a_0 * row.carries.nb_fa * row.flags.m32
        + row.chunks.b_0 * row.carries.na_fb * row.flags.m32
        - row.chunks.c_2
        + 2 * row.flags.np * row.chunks.c_2
        + row.flags.div * row.chunks.d_2
        - 2 * row.flags.nr * row.chunks.d_2
        - row.flags.np * row.flags.div * row.flags.m32
        + row.flags.nr * row.flags.m32
        + row.carries.carry_1
        - row.carries.carry_2 * 65536 = 0)
    (h_c34 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_0
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_1
        + row.carries.fab * row.chunks.a_1 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_0 * row.chunks.b_3
        + row.chunks.a_1 * row.carries.nb_fa * row.flags.m32
        + row.chunks.b_1 * row.carries.na_fb * row.flags.m32
        - row.chunks.c_3
        + 2 * row.flags.np * row.chunks.c_3
        + row.flags.div * row.chunks.d_3
        - 2 * row.flags.nr * row.chunks.d_3
        + row.carries.carry_2
        - row.carries.carry_3 * 65536 = 0)
    (h_c35 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_1
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_1 * row.chunks.b_3
        + row.flags.na * row.flags.nb * row.flags.m32
        + row.chunks.b_0 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_0 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.flags.np * row.flags.m32 * (1 - row.flags.div)
        - row.flags.np * (1 - row.flags.m32) * row.flags.div
        + row.flags.nr * (1 - row.flags.m32)
        - row.chunks.d_0 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_0 * (1 - row.flags.div)
        + row.carries.carry_3
        - row.carries.carry_4 * 65536 = 0)
    (h_c36 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_2
        + row.carries.fab * row.chunks.a_2 * row.chunks.b_3
        + row.chunks.b_1 * row.carries.na_fb * (1 - row.flags.m32)
        + row.chunks.a_1 * row.carries.nb_fa * (1 - row.flags.m32)
        - row.chunks.d_1 * (1 - row.flags.div)
        + row.chunks.d_1 * 2 * row.flags.np * (1 - row.flags.div)
        + row.carries.carry_4
        - row.carries.carry_5 * 65536 = 0)
    (h_c37 :
        row.carries.fab * row.chunks.a_3 * row.chunks.b_3
        + row.chunks.a_2 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_2 * row.carries.na_fb * (1 - row.flags.m32)
        - row.chunks.d_2 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_2 * (1 - row.flags.div)
        + row.carries.carry_5
        - row.carries.carry_6 * 65536 = 0)
    (h_c38 :
        65536 * row.flags.na * row.flags.nb * (1 - row.flags.m32)
        + row.chunks.a_3 * row.carries.nb_fa * (1 - row.flags.m32)
        + row.chunks.b_3 * row.carries.na_fb * (1 - row.flags.m32)
        - 65536 * row.flags.np * (1 - row.flags.div) * (1 - row.flags.m32)
        - row.chunks.d_3 * (1 - row.flags.div)
        + 2 * row.flags.np * row.chunks.d_3 * (1 - row.flags.div)
        + row.carries.carry_6 = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, arithMulElaborated,
    circuit_norm] at hsound
  -- The `circuit_norm`-normalized constraint goals are in `a + -b`
  -- form; re-express the caller's `a - b` hypotheses to match.
  simp only [sub_eq_add_neg] at h_c6 h_c7 h_c8 h_c31 h_c32 h_c33 h_c34 h_c35 h_c36 h_c37 h_c38
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { chunks :=
        { a_0 := .const row.chunks.a_0, a_1 := .const row.chunks.a_1,
          a_2 := .const row.chunks.a_2, a_3 := .const row.chunks.a_3,
          b_0 := .const row.chunks.b_0, b_1 := .const row.chunks.b_1,
          b_2 := .const row.chunks.b_2, b_3 := .const row.chunks.b_3,
          c_0 := .const row.chunks.c_0, c_1 := .const row.chunks.c_1,
          c_2 := .const row.chunks.c_2, c_3 := .const row.chunks.c_3,
          d_0 := .const row.chunks.d_0, d_1 := .const row.chunks.d_1,
          d_2 := .const row.chunks.d_2, d_3 := .const row.chunks.d_3 }
      flags :=
        { na := .const row.flags.na, nb := .const row.flags.nb,
          nr := .const row.flags.nr, np := .const row.flags.np,
          sext := .const row.flags.sext, m32 := .const row.flags.m32,
          div := .const row.flags.div,
          div_by_zero := .const row.flags.div_by_zero,
          div_overflow := .const row.flags.div_overflow,
          main_div := .const row.flags.main_div,
          main_mul := .const row.flags.main_mul, op := .const row.flags.op,
          signed := .const row.flags.signed,
          range_ab := .const row.flags.range_ab,
          range_cd := .const row.flags.range_cd,
          bus_res1 := .const row.flags.bus_res1,
          multiplicity := .const row.flags.multiplicity }
      carries :=
        { carry_0 := .const row.carries.carry_0, carry_1 := .const row.carries.carry_1,
          carry_2 := .const row.carries.carry_2, carry_3 := .const row.carries.carry_3,
          carry_4 := .const row.carries.carry_4, carry_5 := .const row.carries.carry_5,
          carry_6 := .const row.carries.carry_6, fab := .const row.carries.fab,
          na_fb := .const row.carries.na_fb, nb_fa := .const row.carries.nb_fa } }
    row ?_ ?_).1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h_c6, h_c7, h_c8, h_c31, h_c32, h_c33, h_c34, h_c35,
      h_c36, h_c37, h_c38⟩

end ZiskFv.AirsClean.ArithMul
