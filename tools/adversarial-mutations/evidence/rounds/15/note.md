`sel_high_b` is one of the three bits that reconstruct the byte offset of a
sub-doubleword access (`offset = 4*sel_high_4b + 2*sel_high_2b + sel_high_b`).
Breaking its booleanity to `{0, p-1}` lets the offset — and therefore the address
the access is charged to — take values outside `0..7`.
