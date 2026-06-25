import ZiskFv.Compliance.TraceLevelExport.RowDataAluShift
import ZiskFv.Compliance.TraceLevelExport.RowDataArithMem
import ZiskFv.Compliance.TraceLevelExport.RowDataControl

/-!
# Per-op claim / decode / inputs split (root_soundness 3-way refactor)

For each RV64IM op, the per-row residual is declared ONCE as a 3-way split —
`Claim_<op>` (ziskStep claim), `Decode_<op>` (rowDecodes), `Inputs_<op>`
(inputsAgree) — and `RowData_<op>` is the thin bundle of the three.
`toRowData_<op>` reassembles the bundle from the three parts. These now live
beside their flat-bundle definitions in the per-family files
`RowData{AluShift,ArithMem,Control}.lean`; this module re-exports them for the
dispatcher. The 63 `stepStrong_<op>` proofs reference the split parts directly.
-/
