import ZiskFv.Transpiler.Static

open ZiskFv.Transpiler.Static

def parseOp : String → Option Rv64Op
  | "add" => some .add
  | "sub" => some .sub
  | "sll" => some .sll
  | "slt" => some .slt
  | "sltu" => some .sltu
  | "xor" => some .xor
  | "srl" => some .srl
  | "sra" => some .sra
  | "or" => some .or
  | "and" => some .and
  | "addw" => some .addw
  | "subw" => some .subw
  | "sllw" => some .sllw
  | "srlw" => some .srlw
  | "sraw" => some .sraw
  | "addi" => some .addi
  | "slli" => some .slli
  | "slti" => some .slti
  | "sltiu" => some .sltiu
  | "xori" => some .xori
  | "srli" => some .srli
  | "srai" => some .srai
  | "ori" => some .ori
  | "andi" => some .andi
  | "addiw" => some .addiw
  | "slliw" => some .slliw
  | "srliw" => some .srliw
  | "sraiw" => some .sraiw
  | "beq" => some .beq
  | "bne" => some .bne
  | "blt" => some .blt
  | "bge" => some .bge
  | "bltu" => some .bltu
  | "bgeu" => some .bgeu
  | "lb" => some .lb
  | "lbu" => some .lbu
  | "lh" => some .lh
  | "lhu" => some .lhu
  | "lw" => some .lw
  | "lwu" => some .lwu
  | "ld" => some .ld
  | "sb" => some .sb
  | "sh" => some .sh
  | "sw" => some .sw
  | "sd" => some .sd
  | "lui" => some .lui
  | "auipc" => some .auipc
  | "jal" => some .jal
  | "jalr" => some .jalr
  | "fence" => some .fence
  | "mul" => some .mul
  | "mulh" => some .mulh
  | "mulhsu" => some .mulhsu
  | "mulhu" => some .mulhu
  | "mulw" => some .mulw
  | "div" => some .div
  | "divu" => some .divu
  | "divw" => some .divw
  | "divuw" => some .divuw
  | "rem" => some .rem
  | "remu" => some .remu
  | "remw" => some .remw
  | "remuw" => some .remuw
  | _ => none

def boolNat (b : Bool) : Nat :=
  if b then 1 else 0

def u64Int (x : Int) : UInt64 :=
  UInt64.ofNat (u64OfInt x)

def mix (h x : UInt64) : UInt64 :=
  (h ^^^ x) * (1099511628211 : UInt64)

def mixNat (h : UInt64) (x : Nat) : UInt64 :=
  mix h (UInt64.ofNat x)

def mixInt (h : UInt64) (x : Int) : UInt64 :=
  mix h (u64Int x)

def mixBool (h : UInt64) (x : Bool) : UInt64 :=
  mixNat h (boolNat x)

def rowHash (h : UInt64) (r : ZiskStaticRow) : UInt64 :=
  let h := mixNat h r.paddr
  let h := mixNat h r.op
  let h := mixNat h r.aSrc
  let h := mixNat h r.aUseSpImm1
  let h := mixNat h r.aOffsetImm0
  let h := mixNat h r.bSrc
  let h := mixNat h r.bUseSpImm1
  let h := mixNat h r.bOffsetImm0
  let h := mixNat h r.store
  let h := mixInt h r.storeOffset
  let h := mixBool h r.storePc
  let h := mixBool h r.setPc
  let h := mixNat h r.indWidth
  let h := mixInt h r.jmpOffset1
  let h := mixInt h r.jmpOffset2
  let h := mixBool h r.isExternalOp
  mixBool h r.m32

def rowsHash (rows : List ZiskStaticRow) : UInt64 :=
  rows.foldl rowHash (14695981039346656037 : UInt64)

def rowText (r : ZiskStaticRow) : String :=
  ",".intercalate
    [ toString r.paddr
    , toString r.op
    , toString r.aSrc
    , toString r.aUseSpImm1
    , toString r.aOffsetImm0
    , toString r.bSrc
    , toString r.bUseSpImm1
    , toString r.bOffsetImm0
    , toString r.store
    , toString r.storeOffset
    , toString (boolNat r.storePc)
    , toString (boolNat r.setPc)
    , toString r.indWidth
    , toString r.jmpOffset1
    , toString r.jmpOffset2
    , toString (boolNat r.isExternalOp)
    , toString (boolNat r.m32) ]

def requireSome (msg : String) : Option α → Except String α
  | some x => .ok x
  | none => .error msg

def parseLine (line : String) : Except String (Nat × Rv64Inst) := do
  let fields := line.trimAscii.toString.splitOn "\t"
  match fields with
  | [id, op, paddr, rd, rs1, rs2, imm] =>
      let id ← requireSome s!"bad case id: {id}" id.toNat?
      let op ← requireSome s!"bad op: {op}" (parseOp op)
      let paddr ← requireSome s!"bad paddr: {paddr}" paddr.toNat?
      let rd ← requireSome s!"bad rd: {rd}" rd.toNat?
      let rs1 ← requireSome s!"bad rs1: {rs1}" rs1.toNat?
      let rs2 ← requireSome s!"bad rs2: {rs2}" rs2.toNat?
      let imm ← requireSome s!"bad imm: {imm}" imm.toInt?
      pure (id, { paddr, op, rd, rs1, rs2, imm })
  | _ => throw s!"bad line: {line}"

def emitLine (withRows : Bool) (line : String) : IO Unit := do
  if line.trimAscii.toString.isEmpty then
    pure ()
  else
    match parseLine line with
    | .error err => throw <| IO.userError err
    | .ok (id, inst) =>
        let rows := transpile inst
        let base := s!"{id}\t{rows.length}\t{rowsHash rows}"
        if withRows then
          let rowsText := ";".intercalate (rows.map rowText)
          IO.println s!"{base}\t{rowsText}"
        else
          IO.println base

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let withRows := (← IO.getEnv "ZISK_DIFF_LEAN_ROWS").isSome
  for line in input.splitOn "\n" do
    emitLine withRows line
