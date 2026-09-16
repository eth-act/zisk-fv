`(1 - is_external_op) * (1 - op) * c[index] === 0` forces the result `c` to zero
on an internal operation with `op = 0`. Replacing the `is_external_op` selector by
`1` makes the whole product vanish, so the identity holds on every row and
constrains nothing — the classic "ungated constraint" defect, where a rule stays
in the file but stops applying.
