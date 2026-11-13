import ZiskFv.AirsClean.ArithRangeSlice

/-!
# Actual Arith source-payload streamer

Evaluate the same logical source functions used by the packed-provider fixed
columns, including all carry rows and the ROM's first-row padding. Serialization
matches the production observer: centered Goldilocks representatives, tab-separated
source tuple slots, and a newline after every row. No row-building rules are copied.
-/

open Goldilocks ZiskFv.AirsClean

private def cell (value : FGL) : Int :=
  if value.val > GL_prime / 2 then (value.val : Int) - GL_prime else value.val

private def rangeLine (index : Fin RangeTables.arithRangeTableLength) : String :=
  let row := ArithRangeSlice.sourceRow index
  s!"{cell row[0]}\t{cell row[1]}"

private def romLine (index : Fin ArithTableSlice.sourceTableLength) : String :=
  let row := ArithTableSlice.sourcePackedRow index
  s!"{cell row[0]}\t{cell row[1]}\t{cell row[2]}\t{cell row[3]}"

/-- Bounded buffers; do not materialize the multi-million-row source domain. -/
private def stream (size : Nat) (line : Fin size → String) : IO Unit := do
  let out ← IO.getStdout
  let mut index := 0
  while index < size do
    let stop := min (index + 8192) size
    let mut buffer := ""
    while h : index < stop do
      let entry := line ⟨index, Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)⟩
      buffer := buffer ++ entry ++ "\n"
      index := index + 1
    out.putStr buffer
  out.flush

def main (args : List String) : IO UInt32 := do
  match args with
  | ["ArithRangeTable"] =>
      stream RangeTables.arithRangeTableLength rangeLine
      return 0
  | ["ArithTable"] =>
      stream ArithTableSlice.sourceTableLength romLine
      return 0
  | _ =>
      (← IO.getStderr).putStrLn
        "usage: lake env lean --run bin/ArithTableStream/Main.lean (ArithRangeTable|ArithTable)"
      return 2
