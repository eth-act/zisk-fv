`(1 - is_external_op) * op * flag === 0` is half of the internal-operation flag
rule: for an internal op with `op = 1` the `flag` output must be 0. Deleting it
lets an internal operation report the opposite boolean result, which feeds
straight into the branch/`set_pc` logic below it.
