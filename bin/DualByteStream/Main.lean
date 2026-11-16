import ZiskFv.AirsClean.DualBytePackedSource

/-! Stream the actual source component's materialized fixed tuple, not a second
copy of the DualRange row algorithm. The production packed-table observer hashes
the same A,B tab-separated encoding, one physical source row per line. -/
open Goldilocks
open Air.Flat
open ZiskFv.AirsClean

private def rowLine (index : Nat) : String :=
  let raw := DualByteSlice.sourceFixedColumns.materialize index #[(0 : FGL)]
  let env := Environment.fromArray raw
    (fun _ n => (#[] : Array (Vector FGL n)))
  let row := DualByteSlice.sourceComponent.rowInput env
  s!"{row.byte_a.val}\t{row.byte_b.val}\n"

def main : IO Unit := do
  let out ← IO.getStdout
  for index in [:DualByteSlice.sourceFixedColumns.capacity] do
    out.putStr (rowLine index)
  out.flush
