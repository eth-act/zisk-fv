`div_overflow * (1 - div) === 0` confines the signed-division overflow flag to
rows that are actually divisions. Deleting it lets a prover raise `div_overflow`
on a multiplication row and take the overflow branch of the Arith equations there.
This is in the neighbourhood of the already-documented signed DIV/REM defect, so
it is exactly the region where the proof should be most sensitive.
