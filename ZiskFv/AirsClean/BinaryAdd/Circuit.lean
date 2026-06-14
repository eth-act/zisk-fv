import ZiskFv.AirsClean.BinaryAdd.Constraints
import ZiskFv.AirsClean.BinaryAdd.Soundness
import ZiskFv.AirsClean.CompletenessHelpers
import Clean.Air.FlatComponent
import Clean.Utils.Tactics

/-!
# BinaryAdd Clean Component (Phase C0 — de-risk pilot)

Packages ZisK's BinaryAdd AIR as a Clean `Air.Flat.Component`:

* `binaryAddElaborated` — the `ElaboratedCircuit` over `main` — lives in
  `Constraints.lean`.
* `circuit` — the `GeneralFormalCircuit`. `Assumptions := True` for
  soundness; completeness is proved for honest rows built from two 64-bit
  operands.
* `component` — the `Air.Flat.Component`.

## Trust note

`Assumptions := True` is what lets the Component compose into an ensemble
non-vacuously (the `AssumptionsConsistency` obligation becomes trivial).
Completeness is a constructibility claim for rows equal to `binaryAddRowOf a b`
with `a < 2^64` and `b < 2^64`: the builder computes the 32-bit limbs,
16-bit result chunks, and carry bits used by this constraint slice. It does
not claim that arbitrary input rows are honest BinaryAdd executions.
-/

namespace ZiskFv.AirsClean.BinaryAdd

open Goldilocks
open Air.Flat
open ZiskFv.Channels.OperationBus (OpBusChannel)

/-- Low 32-bit limb used by the BinaryAdd honest-row builder. -/
def binaryAddLo32 (x : ℕ) : ℕ := x % 2 ^ 32

/-- High 32-bit limb used by the BinaryAdd honest-row builder. -/
def binaryAddHi32 (x : ℕ) : ℕ := x / 2 ^ 32 % 2 ^ 32

/-- The `k`th 16-bit chunk of a natural number. -/
def binaryAddChunk16 (x k : ℕ) : ℕ := x / (2 ^ 16) ^ k % 2 ^ 16

/-- Honest row for BinaryAdd: 32-bit operand limbs, 16-bit result chunks, and
    the two carry bits are computed from the natural operands. -/
def binaryAddRowOf (a b : ℕ) : BinaryAddRow FGL :=
  let s := (a + b) % 2 ^ 64
  let carry0 : ℕ := (binaryAddLo32 a + binaryAddLo32 b) / 2 ^ 32
  let carry1 : ℕ := (binaryAddHi32 a + binaryAddHi32 b + carry0) / 2 ^ 32
  { a_0 := (binaryAddLo32 a : FGL)
    a_1 := (binaryAddHi32 a : FGL)
    b_0 := (binaryAddLo32 b : FGL)
    b_1 := (binaryAddHi32 b : FGL)
    c_chunks_0 := (binaryAddChunk16 s 0 : FGL)
    c_chunks_1 := (binaryAddChunk16 s 1 : FGL)
    c_chunks_2 := (binaryAddChunk16 s 2 : FGL)
    c_chunks_3 := (binaryAddChunk16 s 3 : FGL)
    cout_0 := (carry0 : FGL)
    cout_1 := (carry1 : FGL) }

lemma binaryAdd_carry0_lt_two (a b : ℕ) :
    (binaryAddLo32 a + binaryAddLo32 b) / 2 ^ 32 < 2 := by
  unfold binaryAddLo32
  omega

lemma binaryAdd_carry1_lt_two (a b : ℕ) (_ha : a < 2 ^ 64) (_hb : b < 2 ^ 64) :
    (binaryAddHi32 a + binaryAddHi32 b +
        (binaryAddLo32 a + binaryAddLo32 b) / 2 ^ 32) / 2 ^ 32 < 2 := by
  unfold binaryAddLo32 binaryAddHi32
  omega

lemma binaryAdd_low_half_eq (a b : ℕ) :
    binaryAddLo32 a + binaryAddLo32 b =
      (binaryAddLo32 a + binaryAddLo32 b) / 2 ^ 32 * 2 ^ 32 +
        binaryAddChunk16 ((a + b) % 2 ^ 64) 1 * 2 ^ 16 +
        binaryAddChunk16 ((a + b) % 2 ^ 64) 0 := by
  unfold binaryAddLo32 binaryAddChunk16
  omega

lemma binaryAdd_high_half_eq (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    binaryAddHi32 a + binaryAddHi32 b +
        (binaryAddLo32 a + binaryAddLo32 b) / 2 ^ 32 =
      (binaryAddHi32 a + binaryAddHi32 b +
          (binaryAddLo32 a + binaryAddLo32 b) / 2 ^ 32) / 2 ^ 32 * 2 ^ 32 +
        binaryAddChunk16 ((a + b) % 2 ^ 64) 3 * 2 ^ 16 +
        binaryAddChunk16 ((a + b) % 2 ^ 64) 2 := by
  unfold binaryAddLo32 binaryAddHi32 binaryAddChunk16
  have ha_hi : a / 2 ^ 32 < 2 ^ 32 := by omega
  have hb_hi : b / 2 ^ 32 < 2 ^ 32 := by omega
  have ha_mod : a / 2 ^ 32 % 2 ^ 32 = a / 2 ^ 32 := Nat.mod_eq_of_lt ha_hi
  have hb_mod : b / 2 ^ 32 % 2 ^ 32 = b / 2 ^ 32 := Nat.mod_eq_of_lt hb_hi
  rw [ha_mod, hb_mod]
  let lo := (a % 2 ^ 32 + b % 2 ^ 32) % 2 ^ 32
  let hi := (a / 2 ^ 32 + b / 2 ^ 32 + (a % 2 ^ 32 + b % 2 ^ 32) / 2 ^ 32) % 2 ^ 32
  let carry := (a / 2 ^ 32 + b / 2 ^ 32 + (a % 2 ^ 32 + b % 2 ^ 32) / 2 ^ 32) / 2 ^ 32
  have hsplit : (a + b) % 2 ^ 64 = lo + hi * 2 ^ 32 := by
    dsimp [lo, hi]
    omega
  have hhi : (a + b) % 2 ^ 64 / 2 ^ 32 = hi := by omega
  have hhi48 : (a + b) % 2 ^ 64 / 2 ^ 48 = hi / 2 ^ 16 := by omega
  have hcarry :
      a / 2 ^ 32 + b / 2 ^ 32 + (a % 2 ^ 32 + b % 2 ^ 32) / 2 ^ 32 =
        carry * 2 ^ 32 + hi := by
    dsimp [carry, hi]
    omega
  norm_num [show ((2 ^ 16 : ℕ) ^ 2) = 2 ^ 32 by norm_num,
    show ((2 ^ 16 : ℕ) ^ 3) = 2 ^ 48 by norm_num]
  norm_num at hhi hhi48
  rw [hhi, hhi48]
  omega

/-- The four BinaryAdd row constraints in Clean-row form. -/
abbrev CoreFacts (row : BinaryAddRow FGL) : Prop :=
  row.cout_0 * (1 - row.cout_0) = 0
  ∧ row.a_0 + row.b_0
      - (row.cout_0 * 4294967296 + row.c_chunks_1 * 65536 + row.c_chunks_0) = 0
  ∧ row.cout_1 * (1 - row.cout_1) = 0
  ∧ row.a_1 + row.b_1 + row.cout_0
      - (row.cout_1 * 4294967296 + row.c_chunks_3 * 65536 + row.c_chunks_2) = 0

/-- The BinaryAdd static-lookup range facts needed by row-native dispatch. -/
abbrev RangeFacts (row : BinaryAddRow FGL) : Prop :=
  row.a_0.val < 2 ^ 32 ∧ row.a_1.val < 2 ^ 32
  ∧ row.b_0.val < 2 ^ 32 ∧ row.b_1.val < 2 ^ 32
  ∧ row.c_chunks_0.val < 2 ^ 16 ∧ row.c_chunks_1.val < 2 ^ 16
  ∧ row.c_chunks_2.val < 2 ^ 16 ∧ row.c_chunks_3.val < 2 ^ 16

/-- Component-facing BinaryAdd spec: semantic packed addition plus the row
    constraints and range facts that the component soundness proof already
    consumes from the Clean constraints/lookups. -/
abbrev ComponentSpecFacts (row : BinaryAddRow FGL) : Prop :=
  Spec row ∧ CoreFacts row ∧ RangeFacts row

set_option maxHeartbeats 800000 in
/-- BinaryAdd as a Clean `GeneralFormalCircuit`. `Assumptions := True` —
    the 8 column range bounds the soundness proof needs are supplied by
    Clean static lookups, not by a caller assumption. -/
def circuit : GeneralFormalCircuit FGL BinaryAddRow unit :=
  { binaryAddElaborated with
    Assumptions := fun _ _ => True
    Spec := fun row _ _ => ComponentSpecFacts row
    -- Completeness covers honest BinaryAdd rows built from two 64-bit operands.
    ProverAssumptions := fun row _ _ =>
      ∃ a b, a < 2 ^ 64 ∧ b < 2 ^ 64 ∧ row = binaryAddRowOf a b
    ProverSpec := fun _ _ _ => True
    soundness := by
      circuit_proof_start
      refine ⟨?_, ?_⟩
      · -- the BinaryAdd algebraic relation: 4 assertZero constraints +
        -- the 8 `bits(N)` column range bounds from Clean static lookups.
        obtain ⟨ha0, ha1, hb0, hb1, hc0r, hc1r, hc2r, hc3r,
          hb0eq, hc0eq, hb1eq, hc1eq⟩ := h_holds
        let row : BinaryAddRow FGL :=
          { a_0 := input_a_0, a_1 := input_a_1, b_0 := input_b_0,
            b_1 := input_b_1, c_chunks_0 := input_c_chunks_0,
            c_chunks_1 := input_c_chunks_1, c_chunks_2 := input_c_chunks_2,
            c_chunks_3 := input_c_chunks_3, cout_0 := input_cout_0,
            cout_1 := input_cout_1 }
        change ComponentSpecFacts row
        have ha0' : row.a_0.val < 2 ^ 32 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable32, RangeTables.rangeStaticTable] using ha0
        have ha1' : row.a_1.val < 2 ^ 32 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable32, RangeTables.rangeStaticTable] using ha1
        have hb0' : row.b_0.val < 2 ^ 32 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable32, RangeTables.rangeStaticTable] using hb0
        have hb1' : row.b_1.val < 2 ^ 32 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable32, RangeTables.rangeStaticTable] using hb1
        have hc0' : row.c_chunks_0.val < 2 ^ 16 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable16, RangeTables.rangeStaticTable] using hc0r
        have hc1' : row.c_chunks_1.val < 2 ^ 16 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable16, RangeTables.rangeStaticTable] using hc1r
        have hc2' : row.c_chunks_2.val < 2 ^ 16 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable16, RangeTables.rangeStaticTable] using hc2r
        have hc3' : row.c_chunks_3.val < 2 ^ 16 := by
          dsimp [row]
          simpa only [RangeTables.rangeTable16, RangeTables.rangeStaticTable] using hc3r
        have h_bool0 : row.cout_0 * (1 + -row.cout_0) = 0 := by
          dsimp [row]
          simpa only using hb0eq
        have h_carry0 :
            row.a_0 + row.b_0
                + -(row.cout_0 * 4294967296 + row.c_chunks_1 * 65536
                  + row.c_chunks_0) = 0 := by
          dsimp [row]
          simpa only using hc0eq
        have h_bool1 : row.cout_1 * (1 + -row.cout_1) = 0 := by
          dsimp [row]
          simpa only using hb1eq
        have h_carry1 :
            row.a_1 + row.b_1 + row.cout_0
                + -(row.cout_1 * 4294967296 + row.c_chunks_3 * 65536
                  + row.c_chunks_2) = 0 := by
          dsimp [row]
          simpa only using hc1eq
        have h_spec := BinaryAdd.soundness_of_ranges row
          ha0' ha1' hb0' hb1' hc0' hc1' hc2' hc3'
          h_bool0 h_carry0 h_bool1 h_carry1
        exact ⟨h_spec,
          ⟨ by simpa [sub_eq_add_neg] using h_bool0
          , by simpa [sub_eq_add_neg] using h_carry0
          , by simpa [sub_eq_add_neg] using h_bool1
          , by simpa [sub_eq_add_neg] using h_carry1 ⟩,
          ⟨ha0', ha1', hb0', hb1', hc0', hc1', hc2', hc3'⟩ ⟩
      · -- the op-bus push's requirement: `OpBusChannel.Guarantees` is `True`
        intro _
        trivial
    completeness := by
      circuit_proof_start [OpBusChannel, Lookup.completeness_def]
      obtain ⟨a, b, ha, hb, hrow⟩ := h_assumptions
      injection hrow with h_a_0 h_a_1 h_b_0 h_b_1 h_c_chunks_0 h_c_chunks_1
        h_c_chunks_2 h_c_chunks_3 h_cout_0 h_cout_1
      subst_vars
      simp [binaryAddLo32, binaryAddHi32, binaryAddChunk16] at h_input ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [RangeTables.rangeTable32, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable32, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable32, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable32, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable16, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable16, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable16, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · simp only [RangeTables.rangeTable16, RangeTables.rangeStaticTable]
        exact fgl_natCast_val_lt_of_lt (by decide) (by omega)
      · have hcarry := binaryAdd_carry0_lt_two a b
        have hcases :
            (a % 4294967296 + b % 4294967296) / 4294967296 = 0 ∨
              (a % 4294967296 + b % 4294967296) / 4294967296 = 1 := by
          unfold binaryAddLo32 at hcarry
          omega
        rcases hcases with hzero | hone
        · left
          simp [hzero]
        · right
          simp [hone]
      · have hnat := binaryAdd_low_half_eq a b
        unfold binaryAddLo32 binaryAddChunk16 at hnat
        norm_num at hnat
        have hcast :
            ((a % 4294967296 + b % 4294967296 : ℕ) : FGL) =
              (((a % 4294967296 + b % 4294967296) / 4294967296 * 4294967296 +
                ((a + b) % 18446744073709551616 / 65536 % 65536) * 65536 +
                ((a + b) % 65536) : ℕ) : FGL) :=
          congrArg (fun n : ℕ => (n : FGL)) hnat
        norm_num at hcast ⊢
        linear_combination hcast
      · have hcarry := binaryAdd_carry1_lt_two a b ha hb
        have hcases :
            (a / 4294967296 % 4294967296 + b / 4294967296 % 4294967296 +
                  (a % 4294967296 + b % 4294967296) / 4294967296) /
                4294967296 =
              0 ∨
            (a / 4294967296 % 4294967296 + b / 4294967296 % 4294967296 +
                  (a % 4294967296 + b % 4294967296) / 4294967296) /
                4294967296 =
              1 := by
          unfold binaryAddLo32 binaryAddHi32 at hcarry
          omega
        rcases hcases with hzero | hone
        · left
          simp [hzero]
        · right
          simp [hone]
      · have hnat := binaryAdd_high_half_eq a b ha hb
        unfold binaryAddLo32 binaryAddHi32 binaryAddChunk16 at hnat
        norm_num at hnat
        have hcast :
            ((a / 4294967296 % 4294967296 + b / 4294967296 % 4294967296 +
                (a % 4294967296 + b % 4294967296) / 4294967296 : ℕ) : FGL) =
              (((a / 4294967296 % 4294967296 + b / 4294967296 % 4294967296 +
                    (a % 4294967296 + b % 4294967296) / 4294967296) /
                    4294967296 * 4294967296 +
                  ((a + b) % 18446744073709551616 / 281474976710656 % 65536) *
                    65536 +
                  ((a + b) % 18446744073709551616 / 4294967296 % 65536) : ℕ) :
                FGL) :=
          congrArg (fun n : ℕ => (n : FGL)) hnat
        norm_num at hcast ⊢
        linear_combination hcast }

/-- BinaryAdd as a Clean `Air.Flat.Component`. -/
def component : Air.Flat.Component FGL := ⟨ circuit ⟩

theorem component_spec (env : Environment FGL) :
    component.Spec env = ComponentSpecFacts (component.rowInput env) := by
  rfl

theorem component_interactionsWith_opBus :
    component.operations.interactionsWith OpBusChannel.toRaw =
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)] := by
  apply Component.interactionsWith_of_exposedChannels
  change ⟨OpBusChannel.toRaw,
      [((OpBusChannel.pushed (opBusMessageExpr component.rowInputVar)).toRaw)]⟩ ∈
    component.exposedChannels
  simp only [component, circuit, binaryAddElaborated, Component.exposedChannels,
    expose, List.mem_singleton, List.map_cons, List.map_nil]

/-- The BinaryAdd `Spec` for a row, derived **through the Clean Component
    `circuit`** — its proven `soundness` field — rather than through
    `BinaryAdd.soundness` directly. Any consumer genuinely depends on
    `circuit`; this is the C0d re-root entry point that makes
    `AirsClean/BinaryAdd/` load-bearing.

    `circuit.soundness` cannot be applied in raw term mode (the `operations`
    `whnf` explodes); the working idiom is to normalize its type with the
    `circuit_norm` simp set first, then feed it a constant-expression row. -/
theorem spec_via_component (row : BinaryAddRow FGL)
    (h_a0 : row.a_0.val < 2 ^ 32) (h_a1 : row.a_1.val < 2 ^ 32)
    (h_b0 : row.b_0.val < 2 ^ 32) (h_b1 : row.b_1.val < 2 ^ 32)
    (h_c0 : row.c_chunks_0.val < 2 ^ 16) (h_c1 : row.c_chunks_1.val < 2 ^ 16)
    (h_c2 : row.c_chunks_2.val < 2 ^ 16) (h_c3 : row.c_chunks_3.val < 2 ^ 16)
    (h0 : row.cout_0 * (1 + -row.cout_0) = 0)
    (h1 : row.a_0 + row.b_0
            + -(row.cout_0 * 4294967296 + row.c_chunks_1 * 65536 + row.c_chunks_0) = 0)
    (h2 : row.cout_1 * (1 + -row.cout_1) = 0)
    (h3 : row.a_1 + row.b_1 + row.cout_0
            + -(row.cout_1 * 4294967296 + row.c_chunks_3 * 65536 + row.c_chunks_2) = 0) :
    Spec row := by
  have hsound := circuit.soundness
  simp only [GeneralFormalCircuit.Soundness, circuit, binaryAddElaborated,
    circuit_norm] at hsound
  refine (hsound (Environment.fromInput row (fun _ n => (#[] : Array (Vector FGL n))))
    { a_0 := .const row.a_0, a_1 := .const row.a_1,
      b_0 := .const row.b_0, b_1 := .const row.b_1,
      c_chunks_0 := .const row.c_chunks_0, c_chunks_1 := .const row.c_chunks_1,
      c_chunks_2 := .const row.c_chunks_2, c_chunks_3 := .const row.c_chunks_3,
      cout_0 := .const row.cout_0, cout_1 := .const row.cout_1 }
    row ?_ ?_).1.1
  · simp [circuit_norm]
  · simp only [circuit_norm]
    exact ⟨h_a0, h_a1, h_b0, h_b1, h_c0, h_c1, h_c2, h_c3,
      h0, h1, h2, h3⟩

end ZiskFv.AirsClean.BinaryAdd
