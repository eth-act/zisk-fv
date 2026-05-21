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
tables (plan decision D-ROM; the C0e Z-ROM spike
`AirsClean/ZRomSpike.lean` is the reference). The 15 slots, in PIL
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

For an arbitrary ROM (the 74 rows have no arithmetic decode — unlike
the `ZRomSpike` range table), the faithful membership predicate IS
the row set: `Spec t` holds iff `t` is one of the 74 explicit rows.
This is **not vacuous** (`True` would be) — it pins `t` to exactly
the ROM content — and it makes `contains_iff` definitional (`Spec`
is, by construction, the `StaticTable.Contains` predicate). A
consumer would read structured column facts off `Spec` by
enumerating the 74 literal rows.

## Status — mechanism only; `arith_table_op_*` retirement is BLOCKED

This module is the proven `StaticTable` *mechanism* for the Arith
ROM (plan D-ROM). It is **not** wired into any Component or the
global theorem, and it retires **zero** axioms. Two findings block
the `arith_table_op_*` retirement that the C3+C4 batch set out to do
— both surfaced by building this faithful table; both are reported
in full to the project owner (decisions D-ROM / D-STOP):

1. **Missing lookup-soundness premise (D-STOP).** The 19
   `arith_table_op_*` axioms of `Airs/Arith/Ranges.lean` each bundle
   *two* facts: (a) the AIR row's 15-tuple is a member of this ROM
   (the `arith_table_assumes` channel-balance / lookup-soundness
   fact — `arith.pil:286-287`), and (b) every ROM row with a given
   `op` has certain column values. This `StaticTable` + `contains_iff`
   delivers only **(b)**, the data half. Half **(a)** can come only
   from a *new* shared lookup-soundness axiom (the established
   `bin_table_consumer_wf` pattern — `Airs/Tables/BinaryTable.lean`)
   or from a Component whose `main` emits the ROM lookup. The C3/C4
   carry-chain Components emit only `assertZero`s — no lookup — so
   they cannot supply (a). Retiring the `arith_table_op_*` axioms
   therefore needs a new soundness axiom, which the batch's brief
   forbids; per D-STOP the work stops here and is reported.

2. **`arith_table_op_mul_mode_pin` over-claims (faithfulness bug).**
   That axiom asserts every `Valid_ArithMul` row with `op = 180`
   (MUL) has `na = nb = np = 0`. But ZisK's ROM (`ARITH_TABLE` rows
   5–10, op = 180) contains rows with `na`/`nb`/`np ∈ {0,1}` — the
   operand-sign MSBs (`arith_table.pil:13`, legend `na = a3,
   nb = b3, np = d3`). A faithful projection lemma off this table's
   `Spec` would *contradict* the axiom. The axiom is over-strong;
   `equiv_MUL` consuming it is vacuous for negative-operand MUL
   traces. This is a pre-existing C3 defect, separate from (1), and
   needs owner adjudication before any ArithTable rewiring.

## Trust note

No axioms. The 74-row enumeration is extracted data; the
`StaticTable` and its `contains_iff` are pure definitional /
structural content. This module retires nothing and is not on the
global theorem's dependency graph.
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
