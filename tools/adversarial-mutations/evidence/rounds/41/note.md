On a signed-division overflow row ZisK pins the divisor `b` to `0xFFFF…` limb by
limb; this identity pins limb 2 (with the 32-bit-mode adjustment). Deleting it
frees that limb, so the overflow branch can be taken with a divisor that is not
the overflow divisor.
