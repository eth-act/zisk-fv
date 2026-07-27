import Clean.Circuit.Lookup
import ZiskFv.Field.Goldilocks

/-!
# ArithTable — Clean `StaticTable` for ZisK's 74-row Arith ROM

ZisK's Arith state machine validates every Arith AIR row against a
74-row ROM, the `arith_table`. Its data is parsed by
`pil-extract arith-table` from
`zisk/state-machines/arith/src/arith_table_data.rs::ARITH_TABLE`
(the Rust constant PIL emits with `generate_table = 1` —
`zisk/state-machines/arith/pil/arith_table.pil:228-253`); the
extracted form lives at `build/extraction/Extraction/ArithTable.lean`.

This module repackages those 74 rows as a Clean `Circuit.StaticTable`
over `fields 15` rows — the proven Clean mechanism for static ROM
tables. The 15 slots, in PIL
column order (`arith_table.pil:228-253` / the FLAGS decode at
`arith_table.pil:209-211`), are:

```
0  op            8  div_by_zero
1  m32           9  div_overflow
2  div          10  main_mul
3  na           11  main_div
4  nb           12  signed
5  np           13  range_ab
6  nr           14  range_cd
7  sext
```

## `Spec` (faithful, non-vacuous)

For an arbitrary ROM (the 74 rows have no arithmetic decode), the
faithful membership predicate IS the row set: `Spec t` holds iff `t`
is one of the 74 explicit rows.
This is **not vacuous** (`True` would be) — it pins `t` to exactly
the ROM content — and it makes `contains_iff` definitional (`Spec`
is, by construction, the `StaticTable.Contains` predicate). A
consumer would read structured column facts off `Spec` by
enumerating the 74 literal rows.

## Status — the `arith_table_op_*` axioms are gone (eth-act/zisk-fv#281)

This module is the proven `StaticTable` mechanism for the Arith ROM
(plan D-ROM). The ArithMul/ArithDiv Clean row views expose the full
15-column tuple and provide lookup-aware circuit entry points.

Earlier revisions of this docstring described a live set of 19
`arith_table_op_*` trust-ledger assumptions in `Airs/Arith/Ranges.lean`
and two findings gating their retirement. **That state is retired.**
No `arith_table_op_*` declaration survives anywhere under `ZiskFv/`,
and the project carries **zero** project-level trust assumptions
repo-wide (V1 gate check "shrinkage floor"). The surviving mentions of
those names are prose in comments, kept as historical pointers.

What replaced them is worth knowing before consuming this table:

1. **Membership comes from the ensemble, not from a bundled premise.**
   Faithful column projections need ROM membership *and* the data half.
   This `StaticTable` plus `contains_iff` supplies the data half; the
   membership half is supplied by the live lookup emitted by the
   lookup-aware ArithMul/ArithDiv entry points (`arith.pil:286-287`),
   on the same recognizer/static-provider route used for
   `BinaryTableSlice` and `SpecifiedRangesSlice`.

2. **Some column facts are genuinely refuted by the ROM data, and
   `AirsClean/ArithTableProjections.lean` proves it.** That module
   carries five *negative* results — `mulh_np_xor_not_static`,
   `mulhsu_np_xor_not_static`, `mulw_sext_zero_not_static`,
   `divuw_sext_zero_not_static`, `divw_sext_zero_not_static` — showing
   that MULH/MULHSU `np = na XOR nb` and W-mode `sext = 0` are **not**
   static ROM-column facts. They are counterexamples, not claims: they
   exist so nobody re-derives an over-strong projection from this
   table. Its positive lemmas expose only the true ROM-data subsets.
   Anything needing the refuted shapes must get it from dynamic
   constraints or sign-agnostic arithmetic instead.

## Trust note

The 74-row enumeration is extracted data; the `StaticTable` and its
`contains_iff` are pure definitional / structural content. This module
introduces no trust of its own.

It is, however, **no longer off the dependency graph** — an earlier
version of this note said it was. `ZiskFv.AirsClean.ArithTable` is
imported by `AirsClean/Arith{Mul,Div}/{Spec,Constraints}.lean`, and
`ArithTableProjections` is imported across `AirsClean/FullEnsemble/
Balance/`, so both are inside the live ensemble's import closure.
Treat changes here as proof-bearing.
-/

namespace ZiskFv.AirsClean.ArithTable

open Goldilocks

/-- The 74 rows of ZisK's `arith_table`, each a `fields 15` tuple in
    PIL column order `[op, m32, div, na, nb, np, nr, sext,
    div_by_zero, div_overflow, main_mul, main_div, signed, range_ab,
    range_cd]`. Verbatim from `build/extraction/Extraction/ArithTable.lean`
    (74 rows, `arith_table_data.rs::ARITH_TABLE`). -/
def rows : Vector (fields 15 FGL) 74 :=
  #v[#v[(176:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL)],
    #v[(177:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL)],
    #v[(179:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (3:FGL), (1:FGL)],
    #v[(179:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (6:FGL), (1:FGL)],
    #v[(179:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (6:FGL), (2:FGL)],
    #v[(180:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (4:FGL), (1:FGL)],
    #v[(180:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (7:FGL), (1:FGL)],
    #v[(180:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (5:FGL), (1:FGL)],
    #v[(180:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (8:FGL), (1:FGL)],
    #v[(180:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (7:FGL), (2:FGL)],
    #v[(180:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (5:FGL), (2:FGL)],
    #v[(181:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (4:FGL), (1:FGL)],
    #v[(181:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (7:FGL), (1:FGL)],
    #v[(181:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (5:FGL), (1:FGL)],
    #v[(181:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (8:FGL), (1:FGL)],
    #v[(181:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (7:FGL), (2:FGL)],
    #v[(181:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (5:FGL), (2:FGL)],
    #v[(182:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (11:FGL)],
    #v[(182:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (14:FGL)],
    #v[(184:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL)],
    #v[(184:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL)],
    #v[(185:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL)],
    #v[(185:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (4:FGL), (4:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (5:FGL), (4:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (8:FGL), (4:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (7:FGL), (7:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (5:FGL), (7:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (4:FGL), (8:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (7:FGL), (8:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (5:FGL), (8:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (7:FGL), (4:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (7:FGL), (8:FGL)],
    #v[(186:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (8:FGL), (7:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (4:FGL), (4:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (5:FGL), (4:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (8:FGL), (4:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (7:FGL), (7:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (5:FGL), (7:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (4:FGL), (8:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (7:FGL), (8:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (5:FGL), (8:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (7:FGL), (4:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (7:FGL), (8:FGL)],
    #v[(187:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (8:FGL), (7:FGL)],
    #v[(188:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (11:FGL), (0:FGL)],
    #v[(188:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (14:FGL), (0:FGL)],
    #v[(188:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (14:FGL), (0:FGL)],
    #v[(189:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (9:FGL)],
    #v[(189:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (10:FGL)],
    #v[(189:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (9:FGL)],
    #v[(189:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (10:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (12:FGL), (12:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (13:FGL), (12:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (13:FGL), (15:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (12:FGL), (16:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (13:FGL), (16:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (16:FGL), (12:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (15:FGL), (15:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (15:FGL), (16:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (15:FGL), (12:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (15:FGL), (16:FGL)],
    #v[(190:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (16:FGL), (15:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (12:FGL), (12:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (13:FGL), (12:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (16:FGL), (12:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (15:FGL), (15:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (13:FGL), (15:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (12:FGL), (16:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (15:FGL), (16:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (13:FGL), (16:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (15:FGL), (12:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (15:FGL), (16:FGL)],
    #v[(191:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (1:FGL), (0:FGL), (0:FGL), (0:FGL), (1:FGL), (0:FGL), (0:FGL), (1:FGL), (16:FGL), (15:FGL)]]

/-- ZisK's `arith_table` as a Clean `StaticTable` over `fields 15`
    rows. `row` indexes the 74-row enumeration; `index` decodes the
    `op` slot; `Spec` is exact ROM membership (faithful — see the
    module docstring); `contains_iff` is definitional. -/
def arithTable : StaticTable FGL (fields 15) where
  name := "arith_table"
  length := 74
  row i := rows[i]
  index t := t[0].val
  Spec t := ∃ i : Fin 74, t = rows[i]
  contains_iff := by intro t; rfl

/-- `arithTable.Spec` is exactly membership in the 74-row enumeration —
    a restatement that makes the faithful content explicit (the
    `StaticTable.Spec` field is sugar-equal to this). -/
theorem spec_iff (t : fields 15 FGL) :
    arithTable.Spec t ↔ ∃ i : Fin 74, t = rows[i] := Iff.rfl

end ZiskFv.AirsClean.ArithTable
