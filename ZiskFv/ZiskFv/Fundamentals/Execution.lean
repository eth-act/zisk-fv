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
