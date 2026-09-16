Not a test. The swap turns `prove_val[rc_index] += sel[_offset] * _tmp` into an
assignment to `sel`, which pil2-compiler rejects.
