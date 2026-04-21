import LeanRV64D
import Mathlib

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

The structural port is complete: the definition mirrors `mult_to_bits_half`
exactly for `MULH`, `MULHU`, `MULHUS`, `MULHSU`. The `.MUL` (Low) case is
defined as the unsigned*unsigned product but `mop_of_mul_op` collapses
all four sign combinations into `.MUL`, so four Low-half cases need the
modular identity
  `(i1 * i2) % 2^64 = (n1 * n2) % 2^64` when `iₖ ≡ nₖ (mod 2^64)`,
which holds because `BitVec.toInt` and `BitVec.toNat` agree mod `2^w`.
The closure of these four cases needs the RV64 analogues of openvm-fv's
`toInt_toInt_as_toNat_64`, `toInt_toNat_as_toNat_64`, etc. — left as a
targeted `sorry` below per the Phase 1.5 time-box.
-/
@[simp]
lemma execute_MUL_eq_execute_MUL'
    (rs2 rs1 rd : regidx) (op : mul_op) :
    execute_MUL rs2 rs1 rd op = execute_MUL' rs2 rs1 rd (mop_of_mul_op op) := by
  rcases op with ⟨ high, sgn1, sgn2 ⟩
  -- Split into High (4 cases: close by simp_all) and Low (4 cases: sorry).
  rcases high with high | high
  all_goals
    rcases sgn2 with sgn2 | sgn2 <;> rcases sgn1 with sgn1 | sgn1 <;>
      simp_all [execute_MUL', execute_MUL, execute_MUL_pure, mop_of_mul_op,
                LeanRV64D.Functions.xlen, mult_to_bits_half]
  -- Four Low-half goals remain: modular identity (i*i ≡ n*n mod 2^64).
  -- TODO Phase 1.5 E4: close via RV64 analogues of openvm-fv's
  -- toInt_toInt_as_toNat_64 / toInt_toNat_as_toNat_64 / toNat_toInt_as_toNat_64.
  all_goals sorry

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

/-- Equivalence of `execute_DIV`s.

Structural port of openvm-fv's DIV equivalence lemma, widened to 64-bit
operands. The proof body is left as a targeted `sorry` — it needs RV64
analogues of the arithmetic helper lemmas (`div_overflow` at `-2^63`,
`to_bits_truncate` over 64-bit operands) that live in openvm-fv's Core.
-/
@[simp]
lemma execute_DIV_eq_execute_DIV'
    (rs2 rs1 rd : regidx) (usgn : Bool) :
    execute_DIV rs2 rs1 rd usgn = execute_DIV' rs2 rs1 rd usgn := by
  -- TODO Phase 1.5 E5: four-way case analysis (signed×zero, signed×overflow,
  -- unsigned×zero, generic) with widened arithmetic bounds. Full RV32 proof
  -- available in openvm-fv Execution.lean lines 354-382.
  sorry

/-- Equivalence of `execute_REM`s.

Structural port of openvm-fv's REM equivalence lemma, widened to 64-bit.
Left as a targeted `sorry` for the same reasons as DIV.
-/
@[simp]
lemma execute_REM_eq_execute_REM'
    (rs2 rs1 rd : regidx) (usgn : Bool) :
    execute_REM rs2 rs1 rd usgn = execute_REM' rs2 rs1 rd usgn := by
  -- TODO Phase 1.5 E5: parallel to DIV — see openvm-fv Execution.lean lines 384-418.
  sorry

end DIV_REM
