import ZiskFv.AirsClean.BinaryTable
import ZiskFv.AirsClean.BinaryExtensionTable

/-!
# Byte-table row streamer

Streams the model's own byte-table definitions so an external gate can compare
them with the rows ZisK's PIL builder produces.

This evaluates `rowOfIndex` itself. It deliberately contains no second copy of
the row-building rules: a re-transcription checked against another
re-transcription would establish nothing about ZisK. The only logic here is the
canonical encoding — the columns in each table's `lookup_proves` tuple order,
tab-separated, one row per line — which is what
`tools/virtual-tables/export-byte-tables.cjs` hashes on the other side.
-/

open ZiskFv.AirsClean

/-- One row, tab-separated, in `lookup_proves` column order
    (`binary_table.pil:336`). -/
private def binaryRowLine (i : Nat) : String :=
  let r := BinaryTable.rowOfIndex i
  s!"{r.pos_ind.val}\t{r.op.val}\t{r.a_byte.val}\t{r.b_byte.val}\t{r.cin.val}\t{r.c_byte.val}\t{r.flags.val}"

/-- One row, tab-separated, in `lookup_proves` column order
    (`binary_extension_table.pil:205`). -/
private def binaryExtensionRowLine (i : Nat) : String :=
  let r := BinaryExtensionTable.rowOfIndex i
  s!"{r.op.val}\t{r.byte_index.val}\t{r.a_byte.val}\t{r.shift_amount.val}\t{r.c_lo_byte.val}\t{r.c_hi_byte.val}\t{r.op_is_shift.val}"

/-- Stream in chunks so a multi-million-row table never materialises. -/
private def stream (size : Nat) (line : Nat → String) : IO Unit := do
  let out ← IO.getStdout
  let chunk := 8192
  let mut i := 0
  while i < size do
    let stop := min (i + chunk) size
    let mut buf := ""
    for j in [i:stop] do
      buf := buf ++ line j ++ "\n"
    out.putStr buf
    i := stop
  out.flush

def main (args : List String) : IO UInt32 := do
  match args with
  | ["BinaryTable"] =>
      stream BinaryTable.tableSize binaryRowLine
      return 0
  | ["BinaryExtensionTable"] =>
      stream BinaryExtensionTable.tableSize binaryExtensionRowLine
      return 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: byte-table-stream (BinaryTable|BinaryExtensionTable)"
      return 2
