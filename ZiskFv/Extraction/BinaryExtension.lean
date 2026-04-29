import Mathlib

import LeanZKCircuit.OpenVM.Circuit

set_option linter.all false

register_simp_attr BinaryExtension_air_simplification
register_simp_attr BinaryExtension_constraint_and_interaction_simplification

namespace BinaryExtension.extraction

-- airgroup: Zisk (id 0)  air: BinaryExtension (id 12)
-- witness column names:
--   stage 1 col 0: op
--   stage 1 col 1: free_in_a[0]
--   stage 1 col 2: free_in_a[1]
--   stage 1 col 3: free_in_a[2]
--   stage 1 col 4: free_in_a[3]
--   stage 1 col 5: free_in_a[4]
--   stage 1 col 6: free_in_a[5]
--   stage 1 col 7: free_in_a[6]
--   stage 1 col 8: free_in_a[7]
--   stage 1 col 9: free_in_b
--   stage 1 col 10: free_in_c[0]
--   stage 1 col 11: free_in_c[1]
--   stage 1 col 12: free_in_c[2]
--   stage 1 col 13: free_in_c[3]
--   stage 1 col 14: free_in_c[4]
--   stage 1 col 15: free_in_c[5]
--   stage 1 col 16: free_in_c[6]
--   stage 1 col 17: free_in_c[7]
--   stage 1 col 18: free_in_c[8]
--   stage 1 col 19: free_in_c[9]
--   stage 1 col 20: free_in_c[10]
--   stage 1 col 21: free_in_c[11]
--   stage 1 col 22: free_in_c[12]
--   stage 1 col 23: free_in_c[13]
--   stage 1 col 24: free_in_c[14]
--   stage 1 col 25: free_in_c[15]
--   stage 1 col 26: op_is_shift
--   stage 1 col 27: b[0]
--   stage 1 col 28: b[1]
--   stage 2 col 0: gsum
--   stage 2 col 1: im[0]
--   stage 2 col 2: im[1]
--   stage 2 col 3: im[2]
--   stage 2 col 4: im[3]
--   stage 2 col 5: im_high_degree[0]

  -- constraint_0_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_1_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_2_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_3_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_4_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_5_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_6_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

  -- constraint_7_every_row skipped: constraint mixes F (witness cells) with ExtF (challenges/exposed values); cannot typecheck without coercion. The named-constraint layer should rebind it via OperationBusEntry

end BinaryExtension.extraction
