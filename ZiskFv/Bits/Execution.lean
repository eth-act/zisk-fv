import LeanRV64D
import Mathlib
import ZiskFv.Bits.U64

open PreSail
open LeanRV64D.Functions

attribute [simp]
  bool_to_bits
  mult_to_bits_half
  shift_bits_right_arith
  shift_right_arith
  sign_extend
  zero_extend
  zopz0zI_s
  zopz0zI_u
  Sail.BitVec.extractLsb
  Sail.BitVec.signExtend
  Sail.BitVec.zeroExtend
  Sail.BitVec.toNatInt
  Sail.shift_bits_left
  Sail.shift_bits_right

attribute [local simp]
  BitVec.extractLsb
  BitVec.extractLsb'

section RTYPE

/-- Pure part of 64-bit `execute_RTYPE` (RV64 port of RV32's `execute_RTYPE_pure`). -/
def execute_RTYPE_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : rop) : BitVec 64 :=
  match op with
  | .ADD => op1 + op2
  | .SLT => zero_extend (m := 64) (bool_to_bits (zopz0zI_s op1 op2))
  | .SLTU => zero_extend (m := 64) (bool_to_bits (zopz0zI_u op1 op2))
  | .AND => op1 &&& op2
  | .OR => op1 ||| op2
  | .XOR => op1 ^^^ op2
  | .SLL => Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 5 0)
  | .SRL => Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 5 0)
  | .SUB => op1 - op2
  | .SRA => shift_bits_right_arith op1 (Sail.BitVec.extractLsb op2 5 0)

/-- `execute_RTYPE` with isolated pure part. -/
def execute_RTYPE' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPE_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_RTYPE`s. -/
@[simp]
lemma execute_RTYPE_eq_execute_RTYPE'
    (rs2 rs1 rd : regidx) (op : rop) :
    execute_RTYPE rs2 rs1 rd op = execute_RTYPE' rs2 rs1 rd op := by
  cases op <;>
    simp_all [execute_RTYPE', execute_RTYPE, execute_RTYPE_pure,
              LeanRV64D.Functions.log2_xlen]

end RTYPE

section ITYPE

/-- Conversion from ITYPE opcode to the corresponding RTYPE opcode. -/
@[simp]
def rop_of_iop (op : iop) : rop :=
  match op with
  | .ADDI => .ADD
  | .SLTI => .SLT
  | .SLTIU => .SLTU
  | .XORI => .XOR
  | .ORI => .OR
  | .ANDI => .AND

/-- Pure part of 64-bit `execute_ITYPE`. -/
def execute_ITYPE_pure (imm : BitVec 12) (op1 : BitVec 64) (op : iop) : BitVec 64 :=
  let immext : BitVec 64 := sign_extend (m := 64) imm
  execute_RTYPE_pure op1 immext (rop_of_iop op)

/-- `execute_ITYPE` with isolated pure part. -/
def execute_ITYPE' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_ITYPE_pure imm rs1_bits op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_ITYPE`s. -/
@[simp]
lemma execute_ITYPE_eq_execute_ITYPE'
    (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    execute_ITYPE imm rs1 rd op = execute_ITYPE' imm rs1 rd op := by
  cases op <;>
    simp_all [execute_ITYPE', execute_ITYPE, execute_ITYPE_pure, execute_RTYPE_pure]

end ITYPE

section SHIFTIOP

/-- Conversion from SHIFTIOP opcode to the corresponding RTYPE opcode. -/
@[simp]
def rop_of_sop (op : sop) : rop :=
  match op with
  | .SLLI => .SLL
  | .SRLI => .SRL
  | .SRAI => .SRA

/-- Pure part of 64-bit `execute_SHIFTIOP`.  Uses a 6-bit shift amount (`log2_xlen = 6`). -/
def execute_SHIFTIOP_pure (op1 : BitVec 64) (shamt : BitVec 6) (op : sop) : BitVec 64 :=
  match op with
  | .SLLI => Sail.shift_bits_left op1 shamt
  | .SRLI => Sail.shift_bits_right op1 shamt
  | .SRAI => shift_bits_right_arith op1 shamt

/-- `execute_SHIFTIOP` with isolated pure part. -/
def execute_SHIFTIOP' (shamt : BitVec 6) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_SHIFTIOP_pure rs1_bits shamt op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_SHIFTIOP`s. -/
@[simp]
lemma execute_SHIFTIOP_eq_execute_SHIFTIOP'
    (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) :
    execute_SHIFTIOP shamt rs1 rd op = execute_SHIFTIOP' shamt rs1 rd op := by
  have h_nat : (BitVec.ofNat 6 shamt.toNat).toNat = shamt.toNat := by
    rw [BitVec.toNat_ofNat]; omega
  cases op <;>
    simp_all [execute_SHIFTIOP', execute_SHIFTIOP, execute_SHIFTIOP_pure,
              LeanRV64D.Functions.log2_xlen]
  -- SRAI remaining: `(BitVec.ofNat 6 shamt.toNat).toNat` appears — rewrite with h_nat
  rw [show (BitVec.ofNat 6 shamt.toNat).toNat = shamt.toNat from by
        rw [BitVec.toNat_ofNat]; omega]

end SHIFTIOP

section RTYPEW

/-- Pure part of 64-bit `execute_RTYPEW` (RV64-only word-size variants of
    the RTYPE family: `ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`).

    Matches the Sail-level `execute_RTYPEW` shape at
    `LeanRV64D.InstsEnd.lean:65650-65661`:

    1. take the low 32 bits of each source register
       (`Sail.BitVec.extractLsb _ 31 0`);
    2. apply the opcode-specific 32-bit operation — for shifts the shift
       amount is the low 5 bits of `rs2` (`extractLsb 4 0`);
    3. sign-extend the 32-bit result to 64 via `sign_extend (m := 64)`.

    For ADDW/SUBW this matches modular 32-bit add / sub. For SLLW it is
    a 32-bit shift-left by `rs2[4:0]` followed by sign-extension. -/
def execute_RTYPEW_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : ropw) : BitVec 64 :=
  let a32 : BitVec 32 := Sail.BitVec.extractLsb op1 31 0
  let b32 : BitVec 32 := Sail.BitVec.extractLsb op2 31 0
  let result : BitVec 32 :=
    match op with
    | .ADDW => a32 + b32
    | .SUBW => a32 - b32
    | .SLLW => Sail.shift_bits_left a32 (Sail.BitVec.extractLsb b32 4 0)
    | .SRLW => Sail.shift_bits_right a32 (Sail.BitVec.extractLsb b32 4 0)
    | .SRAW => shift_bits_right_arith a32 (Sail.BitVec.extractLsb b32 4 0)
  sign_extend (m := 64) result

/-- `execute_RTYPEW` with isolated pure part. -/
def execute_RTYPEW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPEW_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_RTYPEW`s.

    Five cases (`ADDW`, `SUBW`, `SLLW`, `SRLW`, `SRAW`). The Sail definition
    takes the low-32 extraction inside an extra monadic binding; after
    `simp_all` unfolds both sides they agree on each opcode by `rfl`
    modulo the implicit `sign_extend (m := 64) result` at the end.
    `log2_xlen` does not appear (shifts use the explicit `extractLsb _ 4 0`
    shape since `ropw` is a 32-bit family). -/
@[simp]
lemma execute_RTYPEW_eq_execute_RTYPEW'
    (rs2 rs1 rd : regidx) (op : ropw) :
    execute_RTYPEW rs2 rs1 rd op = execute_RTYPEW' rs2 rs1 rd op := by
  cases op <;>
    simp_all [execute_RTYPEW', execute_RTYPEW, execute_RTYPEW_pure]
  -- SRAW residual: `BitVec.setWidth 32 y_1.toNat` vs `BitVec.ofNat 32 y_1.toNat`
  -- differ only syntactically; close by `rfl` on setWidth = ofNat for ℕ (both
  -- reduce to `Fin.ofNat' (2^32) y_1.toNat`).
  rfl

end RTYPEW

section SHIFTIWOP

/-- Pure part of 64-bit `execute_SHIFTIWOP` (the W-variant immediate
    shift: `SLLIW`, `SRLIW`, `SRAIW`).

    Matches the Sail-level `execute_SHIFTIWOP` shape at
    `LeanRV64D.InstsEnd.lean:65520-65528`:

    1. extract the low 32 bits of `rs1_val`
       (`Sail.BitVec.extractLsb _ 31 0`);
    2. apply the opcode-specific 32-bit shift (shamt is a `BitVec 5`);
    3. sign-extend the 32-bit result to 64 via `sign_extend (m := 64)`. -/
def execute_SHIFTIWOP_pure (op1 : BitVec 64) (shamt : BitVec 5) (op : sopw) : BitVec 64 :=
  let a32 : BitVec 32 := Sail.BitVec.extractLsb op1 31 0
  let result : BitVec 32 :=
    match op with
    | .SLLIW => Sail.shift_bits_left a32 shamt
    | .SRLIW => Sail.shift_bits_right a32 shamt
    | .SRAIW => shift_bits_right_arith a32 shamt
  sign_extend (m := 64) result

/-- `execute_SHIFTIWOP` with isolated pure part. -/
def execute_SHIFTIWOP' (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_SHIFTIWOP_pure rs1_bits shamt op))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_SHIFTIWOP`s.

    Three cases (`SLLIW`, `SRLIW`, `SRAIW`). The Sail definition takes
    the low-32 extraction inside an extra monadic binding; after
    `simp_all` unfolds both sides they agree on each opcode. -/
@[simp]
lemma execute_SHIFTIWOP_eq_execute_SHIFTIWOP'
    (shamt : BitVec 5) (rs1 rd : regidx) (op : sopw) :
    execute_SHIFTIWOP shamt rs1 rd op = execute_SHIFTIWOP' shamt rs1 rd op := by
  cases op <;>
    simp_all [execute_SHIFTIWOP', execute_SHIFTIWOP, execute_SHIFTIWOP_pure]

end SHIFTIWOP

section MULW

/-- Pure part of 64-bit `execute_MULW` (the 32-bit signed multiply
    W-variant).

    Matches the Sail-level `execute_MULW` shape at
    `LeanRV64D.InstsEnd.lean:66799-66806`:

    1. extract the low 32 bits of both source registers;
    2. interpret as signed 32-bit integers and multiply;
    3. truncate the integer product to 32 bits, then sign-extend to 64. -/
def execute_MULW_pure (op1 : BitVec 64) (op2 : BitVec 64) : BitVec 64 :=
  let a32 : BitVec 32 := Sail.BitVec.extractLsb op1 31 0
  let b32 : BitVec 32 := Sail.BitVec.extractLsb op2 31 0
  let a_int := BitVec.toInt a32
  let b_int := BitVec.toInt b32
  let result32 : BitVec 32 := to_bits_truncate (l := 32) (a_int * b_int)
  sign_extend (m := 64) result32

/-- `execute_MULW` with isolated pure part. -/
def execute_MULW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_MULW_pure rs1_bits rs2_bits))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_MULW`s.

    Single-opcode (no enum branching). The Sail definition performs the
    low-32 extraction inside two separate monadic bindings; after
    `simp_all` unfolds both sides they agree on the signed 32-bit
    multiply — `to_bits_truncate` normalizes the intermediate integer
    product identically on both sides. -/
@[simp]
lemma execute_MULW_eq_execute_MULW'
    (rs2 rs1 rd : regidx) :
    execute_MULW rs2 rs1 rd = execute_MULW' rs2 rs1 rd := by
  simp_all [execute_MULW', execute_MULW, execute_MULW_pure]

end MULW

section MUL

/-- Multiplication opcodes. -/
inductive mop where | MUL | MULH | MULHU | MULHUS | MULHSU
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Conversion from RISC-V spec representation to `mop`. -/
def mop_of_mul_op (m : mul_op) : mop :=
  match m with
  | { result_part := .Low, signed_rs1 := _, signed_rs2 := _ } => .MUL
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned } => .MULHU
  | { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Signed } => .MULHUS
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned } => .MULHSU
  | { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed } => .MULH

/-- Pure part of 64-bit `execute_MUL`.

The two operands are interpreted as signed/unsigned according to `op`, their
128-bit product is computed, and the result extracts either the low 64 bits
(for `.MUL`) or the high 64 bits (for the `MULH*` variants).

The definition mirrors the upstream `mult_to_bits_half` path with `l := 64`.
-/
def execute_MUL_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : mop) : BitVec 64 :=
  match op with
  | .MUL =>
      let wide : BitVec 128 := to_bits_truncate (l := 128)
        ((Sail.BitVec.toNatInt op1 : ℤ) * (Sail.BitVec.toNatInt op2 : ℤ))
      Sail.BitVec.extractLsb wide 63 0
  | .MULH =>
      let wide : BitVec 128 := to_bits_truncate (l := 128)
        ((BitVec.toInt op1 : ℤ) * (BitVec.toInt op2 : ℤ))
      Sail.BitVec.extractLsb wide 127 64
  | .MULHU =>
      let wide : BitVec 128 := to_bits_truncate (l := 128)
        ((Sail.BitVec.toNatInt op1 : ℤ) * (Sail.BitVec.toNatInt op2 : ℤ))
      Sail.BitVec.extractLsb wide 127 64
  | .MULHUS =>
      let wide : BitVec 128 := to_bits_truncate (l := 128)
        ((Sail.BitVec.toNatInt op1 : ℤ) * (BitVec.toInt op2 : ℤ))
      Sail.BitVec.extractLsb wide 127 64
  | .MULHSU =>
      let wide : BitVec 128 := to_bits_truncate (l := 128)
        ((BitVec.toInt op1 : ℤ) * (Sail.BitVec.toNatInt op2 : ℤ))
      Sail.BitVec.extractLsb wide 127 64

/-- `execute_MUL` with isolated pure part. -/
def execute_MUL' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (m : mop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_MUL_pure rs1_bits rs2_bits m))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_MUL`s.

The definition mirrors `mult_to_bits_half` exactly for `MULH`, `MULHU`,
`MULHUS`, `MULHSU`.  The `.MUL` (Low) case is defined as the
unsigned × unsigned product but `mop_of_mul_op` collapses all four sign
combinations into `.MUL`, so four Low-half cases need the modular identity
  `(i1 * i2) % 2^64 = (n1 * n2) % 2^64` when `iₖ ≡ nₖ (mod 2^64)`,
which holds because `BitVec.toInt` and `BitVec.toNat` agree mod `2^w`.
-/
@[simp]
lemma execute_MUL_eq_execute_MUL'
    (rs2 rs1 rd : regidx) (op : mul_op) :
    execute_MUL rs2 rs1 rd op = execute_MUL' rs2 rs1 rd (mop_of_mul_op op) := by
  rcases op with ⟨ high, sgn1, sgn2 ⟩
  -- Split into High (4 cases: close by simp_all) and Low (4 cases below).
  rcases high with high | high
  all_goals
    rcases sgn2 with sgn2 | sgn2 <;> rcases sgn1 with sgn1 | sgn1 <;>
      simp_all [execute_MUL', execute_MUL, execute_MUL_pure, mop_of_mul_op,
                LeanRV64D.Functions.xlen, mult_to_bits_half]
  -- Four Low-half goals remain: modular identity (i*i ≡ n*n mod 2^64).
  -- All goals have the form:
  --   wX_bits rd (BitVec.setWidth 64 (to_bits_truncate (EXPR_I))) =
  --   wX_bits rd (BitVec.setWidth 64 (to_bits_truncate (EXPR_N)))
  -- where EXPR_I is some mix of (toInt, toNat) products, EXPR_N is (toNat * toNat).
  -- Both sides agree because toInt ≡ toNat (mod 2^64) for 64-bit BitVecs.
  all_goals
    refine bind_congr ?_; intro r1
    refine bind_congr ?_; intro r2
    -- Strip the `wX_bits` / `(· <$> ·)` monadic wrapping.
    ext s
    simp_all
    congr 3
    -- Goal: BitVec.setWidth 64 (to_bits_truncate EXPR_I) = BitVec.setWidth 64 (to_bits_truncate EXPR_N)
    -- Strategy: reduce both sides to `BitVec.ofInt 64 EXPR` via explicit width manipulation,
    -- then use `BitVec.ofInt`-is-invariant-under-mod-2^64 reasoning.
    -- Helper: `BitVec.setWidth 64 (to_bits_truncate (l := 128) x) = BitVec.ofInt 64 x`.
    have to_bits_setWidth_64 : ∀ (x : ℤ),
        BitVec.setWidth 64 (to_bits_truncate (l := 128) x) = BitVec.ofInt 64 x := by
      intro x
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, to_bits_truncate, Sail.get_slice_int,
                 BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero,
                 Nat.zero_add]
      -- Goal: (((x % 2^129).toNat) % 2^128) % 2^64 = (x % 2^64).toNat
      -- The mod and extract use ℕ literals, but we need to reduce them and compare.
      -- Change the numeric form to ℤ literals for uniform reasoning.
      show (x % ((2 : ℕ) ^ (128 + 1) : ℤ)).toNat % 2 ^ 128 % 2 ^ 64
           = (x % ((2 : ℕ) ^ 64 : ℤ)).toNat
      have eq1 : (((2 : ℕ) ^ (128 + 1)) : ℤ) = 680564733841876926926749214863536422912 := by
        norm_num
      have eq2 : (((2 : ℕ) ^ 64) : ℤ) = 18446744073709551616 := by norm_num
      rw [eq1, eq2]
      show (x % 680564733841876926926749214863536422912).toNat
             % ((2 : ℕ) ^ 128) % ((2 : ℕ) ^ 64)
           = (x % 18446744073709551616).toNat
      have eq3 : ((2 : ℕ) ^ 128) = 340282366920938463463374607431768211456 := by norm_num
      have eq4 : ((2 : ℕ) ^ 64) = 18446744073709551616 := by norm_num
      rw [eq3, eq4]
      -- Goal: (x % 680564...).toNat % 340282... % 184467... = (x % 184467...).toNat
      have h_bound_big : (0 : ℤ) ≤ x % 680564733841876926926749214863536422912 := by
        apply Int.emod_nonneg; norm_num
      have h_bound_64 : (0 : ℤ) ≤ x % 18446744073709551616 := by
        apply Int.emod_nonneg; norm_num
      -- Convert (.toNat).Nat.mod to coercion arithmetic.
      zify
      rw [Int.toNat_of_nonneg h_bound_big, Int.toNat_of_nonneg h_bound_64]
      have step1 : x % 680564733841876926926749214863536422912 % 340282366920938463463374607431768211456
                   = x % 340282366920938463463374607431768211456 := by
        apply Int.emod_emod_of_dvd; norm_num
      have step2 : x % 340282366920938463463374607431768211456 % 18446744073709551616
                   = x % 18446744073709551616 := by
        apply Int.emod_emod_of_dvd; norm_num
      rw [step1, step2]
    rw [to_bits_setWidth_64, to_bits_setWidth_64]
    -- Goal: BitVec.ofInt 64 EXPR_I = BitVec.ofInt 64 EXPR_N
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    congr 1
    -- Goal: EXPR_I % 2^64 = EXPR_N % 2^64
    have hr1 : (r1.toInt : ℤ) % (2^64 : ℕ) = (r1.toNat : ℤ) % (2^64 : ℕ) := by
      rw [BitVec.toInt_eq_toNat_bmod, Int.bmod]
      split_ifs <;> push_cast <;> omega
    have hr2 : (r2.toInt : ℤ) % (2^64 : ℕ) = (r2.toNat : ℤ) % (2^64 : ℕ) := by
      rw [BitVec.toInt_eq_toNat_bmod, Int.bmod]
      split_ifs <;> push_cast <;> omega
    first
    | (rw [Int.mul_emod, hr1, hr2, ← Int.mul_emod])
    | (rw [Int.mul_emod, hr1, ← Int.mul_emod])
    | (rw [Int.mul_emod, hr2, ← Int.mul_emod])

end MUL

section DIV_REM

/-- Signed/unsigned selector for DIV/REM. -/
inductive drop where | DRS | DRU
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Pure DIV/REM on integers, producing (quotient, remainder).

Mirrors the Sail spec:
* for signed (`DRS`), interprets operands via `toInt`;
* for unsigned (`DRU`), via `toNat` (as an `Int`);
* divide-by-zero produces quotient `-1` (signed) / `2^64 - 1` (unsigned)
  and remainder = op1;
* signed-overflow `-2^63 / -1` produces quotient `-2^63` and remainder `0`
  (the remainder is handled implicitly by `Int.tmod`).
-/
def execute_DIV_REM_pure_int (op1 : BitVec 64) (op2 : BitVec 64) (op : drop) : ℤ × ℤ :=
  match op with
  | .DRS =>
      let nop1 := BitVec.toInt op1
      let nop2 := BitVec.toInt op2
      let q := if nop2 = 0 then -1 else
                 if nop1 = -2^63 && nop2 = -1 then -2^63 else
                   Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩
  | .DRU =>
      let nop1 : ℤ := BitVec.toNat op1
      let nop2 : ℤ := BitVec.toNat op2
      let q := if nop2 = 0 then 2^64 - 1 else Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩

/-- Pure DIV/REM producing 64-bit BitVec pairs. -/
def execute_DIV_REM_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : drop) : BitVec 64 × BitVec 64 :=
  let ⟨ q, r ⟩ := execute_DIV_REM_pure_int op1 op2 op
  match op with
  | .DRS => ⟨ BitVec.ofInt 64 q, BitVec.ofInt 64 r ⟩
  | .DRU => ⟨ BitVec.ofNat 64 q.toNat, BitVec.ofNat 64 r.toNat ⟩

/-- `execute_DIV` with isolated pure part. -/
def execute_DIV' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ result, _ ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

/-- `execute_REM` with isolated pure part. -/
def execute_REM' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ _, result ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

set_option maxHeartbeats 10000000 in
/-- Equivalence of `execute_DIV`s.

Structural port of openvm-fv's DIV equivalence lemma, widened to 64-bit
operands.
-/
@[simp]
lemma execute_DIV_eq_execute_DIV'
    (rs2 rs1 rd : regidx) (usgn : Bool) :
    execute_DIV rs2 rs1 rd usgn = execute_DIV' rs2 rs1 rd usgn := by
  simp_all [execute_DIV, execute_DIV']
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp; congr
  have range_int_r1 : -9223372036854775808 ≤ r1.toInt ∧ r1.toInt < 9223372036854775808 := by
    constructor
    · have := @BitVec.le_toInt 64 r1; norm_num at this ⊢; exact_mod_cast this
    · have := @BitVec.toInt_lt 64 r1; norm_num at this ⊢; exact_mod_cast this
  have range_int_r2 : -9223372036854775808 ≤ r2.toInt ∧ r2.toInt < 9223372036854775808 := by
    constructor
    · have := @BitVec.le_toInt 64 r2; norm_num at this ⊢; exact_mod_cast this
    · have := @BitVec.toInt_lt 64 r2; norm_num at this ⊢; exact_mod_cast this
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 18446744073709551616 := by
    constructor
    · omega
    · have := r1.isLt; omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 18446744073709551616 := by
    constructor
    · omega
    · have := r2.isLt; omega
  by_cases husgn : usgn <;>
    simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int,
              LeanRV64D.Functions.not, LeanRV64D.Functions.xlen, instHPowInt_leanRV64D] <;>
    by_cases r2z : r2 = 0 <;> simp_all
  · -- Unsigned, r2 = 0 → quotient is 2^64 - 1
    simp [to_bits_truncate, Sail.get_slice_int]
  · -- Unsigned, r2 ≠ 0 → use plain tdiv
    repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    rw [← BitVec.toNat_inj]
    simp [to_bits_truncate, Sail.get_slice_int]
    congr
    rw [Int.emod_eq_of_lt]
    · apply Int.zero_le_ofNat
    · have := @Int.ediv_le_self r1.toNat r2.toNat (by omega)
      omega
  · -- Signed, r2 = 0 → quotient is -1
    simp [to_bits_truncate, Sail.get_slice_int]
  · -- Signed, r2 ≠ 0: may overflow at -2^63 / -1, else tdiv
    by_cases of : 9223372036854775808 ≤ r1.toInt.tdiv r2.toInt <;>
    have of' := ZiskFv.U64.div_overflow_64 range_int_r1 range_int_r2 <;>
    simp_all [to_bits_truncate, Sail.get_slice_int]
    simp [BitVec.ofNat, BitVec.ofInt]
    congr
    simp [Fin.ext_iff]
    omega

set_option maxHeartbeats 10000000 in
/-- Equivalence of `execute_REM`s.

Structural port of openvm-fv's REM equivalence lemma, widened to 64-bit.
-/
@[simp]
lemma execute_REM_eq_execute_REM'
    (rs2 rs1 rd : regidx) (usgn : Bool) :
    execute_REM rs2 rs1 rd usgn = execute_REM' rs2 rs1 rd usgn := by
  simp_all [execute_REM, execute_REM']
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp_all; congr
  have range_int_r1 : -9223372036854775808 ≤ r1.toInt ∧ r1.toInt < 9223372036854775808 := by
    constructor
    · have := @BitVec.le_toInt 64 r1; norm_num at this ⊢; exact_mod_cast this
    · have := @BitVec.toInt_lt 64 r1; norm_num at this ⊢; exact_mod_cast this
  have range_int_r2 : -9223372036854775808 ≤ r2.toInt ∧ r2.toInt < 9223372036854775808 := by
    constructor
    · have := @BitVec.le_toInt 64 r2; norm_num at this ⊢; exact_mod_cast this
    · have := @BitVec.toInt_lt 64 r2; norm_num at this ⊢; exact_mod_cast this
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 18446744073709551616 := by
    constructor
    · omega
    · have := r1.isLt; omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 18446744073709551616 := by
    constructor
    · omega
    · have := r2.isLt; omega
  by_cases husgn : usgn <;>
    simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int] <;>
    by_cases r2z : r2 = 0 <;> simp_all
  · -- Unsigned, r2 = 0
    simp [to_bits_truncate, Sail.get_slice_int]
    rw [Nat.mod_eq_of_lt (by omega)]; simp
  · -- Unsigned, r2 ≠ 0
    repeat rw [ if_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    rw [← BitVec.toNat_inj]
    simp [to_bits_truncate, Sail.get_slice_int]
    congr
    rw [Int.emod_eq_of_lt]
    · apply Int.zero_le_ofNat
    · rw [Int.tmod_eq_emod_of_nonneg (by omega)]
      trans (r2.toNat : ℤ)
      · simp [← BitVec.toNat_inj] at r2z
        apply Int.emod_lt_of_pos r1.toNat (by omega)
      · omega
  · -- Signed, r2 = 0 → remainder = r1
    simp [to_bits_truncate, Sail.get_slice_int]
    simp [← BitVec.toNat_inj]
    have mod_65_to_64 : ∀ (a : ℤ),
        (a % 36893488147419103232).toNat % 18446744073709551616
          = (a % 18446744073709551616).toNat := by omega
    simp [mod_65_to_64, BitVec.toInt]
    split_ifs with hneg <;> [ skip; simp ] <;>
      rw [Int.emod_eq_of_lt (by omega)] <;> simp <;> omega
  · -- Signed, r2 ≠ 0
    repeat rw [ if_neg (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
    simp_all [to_bits_truncate, Sail.get_slice_int]
    simp [BitVec.ofNat, BitVec.ofInt]
    congr
    simp [Fin.ext_iff]
    omega

end DIV_REM

section DIVW_REMW

/-- `execute_DIVW` with isolated pure part (mirrors the Sail body
    structure but factored).

    Sail body (`InstsEnd.lean:69371-69391`):
    1. extract low 32 bits of each operand;
    2. interpret as `ℤ` (signed via `toInt`, unsigned via `toNatInt`);
    3. quotient = `if rs2 == 0 then -1 else Int.tdiv rs1 rs2`;
    4. signed-overflow patch: if `!is_unsigned ∧ quotient ≥ 2^31` then
       `quotient := -2^31`;
    5. write `sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)`. -/
def execute_DIVW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool)
    : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (Sail.BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (Sail.BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let quotient :=
    if ((rs2_int == 0) : Bool)
    then (Neg.neg 1)
    else (Int.tdiv rs1_int rs2_int)
  let quotient :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
    then (Neg.neg (2 ^i 31))
    else quotient
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)))
  (pure RETIRE_SUCCESS)

/-- `execute_REMW` with isolated pure part. -/
def execute_REMW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool)
    : SailM ExecutionResult := do
  let rs1_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_bits ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let rs1_int :=
    if (is_unsigned : Bool)
    then (Sail.BitVec.toNatInt rs1_bits)
    else (BitVec.toInt rs1_bits)
  let rs2_int :=
    if (is_unsigned : Bool)
    then (Sail.BitVec.toNatInt rs2_bits)
    else (BitVec.toInt rs2_bits)
  let remainder :=
    if ((rs2_int == 0) : Bool)
    then rs1_int
    else (Int.tmod rs1_int rs2_int)
  (wX_bits rd (sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_DIVW_eq_execute_DIVW'
    (rs2 rs1 rd : regidx) (usgn : Bool) :
    execute_DIVW rs2 rs1 rd usgn = execute_DIVW' rs2 rs1 rd usgn := by
  rfl

@[simp]
lemma execute_REMW_eq_execute_REMW'
    (rs2 rs1 rd : regidx) (usgn : Bool) :
    execute_REMW rs2 rs1 rd usgn = execute_REMW' rs2 rs1 rd usgn := by
  rfl

end DIVW_REMW

section ADDIW

/-- Pure part of 64-bit `execute_ADDIW` (add-immediate-word).

    Matches the Sail-level `execute_ADDIW` shape at
    `LeanRV64D.InstsEnd.lean:69927-69930`:

    1. add `rs1_val + sign_extend(m := 64) imm`;
    2. extract the low 32 bits of the sum;
    3. sign-extend the 32-bit result to 64.

    Equivalent to `execute_RTYPEW_pure rs1_bits (sign_extend (m := 64) imm) ropw.ADDW`,
    since `extractLsb (a + b) 31 0 = extractLsb a 31 0 + extractLsb b 31 0`. -/
def execute_ADDIW_pure (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.setWidth 32 (rs1_val + BitVec.signExtend 64 imm))

/-- `execute_ADDIW` with isolated pure part. -/
def execute_ADDIW' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_ADDIW_pure imm rs1_bits))
  (pure RETIRE_SUCCESS)

/-- Equivalence of `execute_ADDIW`s. -/
@[simp]
lemma execute_ADDIW_eq_execute_ADDIW'
    (imm : BitVec 12) (rs1 rd : regidx) :
    execute_ADDIW imm rs1 rd = execute_ADDIW' imm rs1 rd := by
  simp [execute_ADDIW', execute_ADDIW, execute_ADDIW_pure]

end ADDIW
