`proves_operation(op: OP_ADD, …)` is BinaryAdd's advertisement on the 5000
operation bus: "I am the provider of 64-bit ADD". Re-tagging it `OP_SUB` makes a
row that computes `a + b` answer requests for subtraction, so `SUB` could be
discharged with an addition result. There is a second, correct `SUB` provider
(the Binary AIR), so this is not merely an unsatisfiable circuit — it is an extra
wrong provider for a live opcode.
