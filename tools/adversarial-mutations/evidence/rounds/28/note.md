This identity is the memory timeline's monotonicity witness: the increment
`l_increment + 2**22 * h_increment + 1` must equal the address delta on a row
where the address changes, and the step delta otherwise. Deleting it removes the
constraint that makes memory accesses ordered, which is the backbone of the
read-after-write argument.
