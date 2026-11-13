import ZiskFv.AirsClean.MemAlignRomTable

/-!
Stream the actual static provider in physical-index order. No builder logic is
repeated here. Column order is the bus-133 lookup tuple order.
-/

open ZiskFv.AirsClean.MemAlignRomTable

def main : IO Unit := do
  let out ← IO.getStdout
  for i in List.finRange memAlignRomTable.length do
    let row := memAlignRomTable.row i
    out.putStrLn s!"{row.pc.val}\t{row.deltaPc.val}\t{row.deltaAddr.val}\t{row.offset.val}\t{row.width.val}\t{row.flags.val}"
  out.flush
