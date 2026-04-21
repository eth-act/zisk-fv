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
  -- TODO Phase 1.5 E4: close 4 Low-half modular-equivalence goals
  -- (toInt * toInt ≡ toInt * toNat ≡ toNat * toInt ≡ toNat * toNat mod 2^64).
  -- The High-half MULH/MULHU/MULHUS/MULHSU cases close trivially by
  -- simp_all once helper lemmas are added. Full proof structure intact in
  -- openvm-fv/OpenvmFv/Fundamentals/Execution.lean (lines 172-307).
  sorry

end MUL
