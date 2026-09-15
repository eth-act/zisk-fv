`b_op + 0x10 * mode32` is how the Binary AIR names the operation it proves on the
5000 bus: the 32-bit variant of an operation is its 64-bit opcode plus `0x10`.
With `0x0f` every 32-bit operation advertises the opcode of a *different*
operation (`MINU_W` 0x12 becomes 0x11, and so on), so Main's request for one
operation can be discharged by a Binary row computing another. This is the
operand-bus analogue of a mislabelled function pointer.
