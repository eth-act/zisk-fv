`wr` is the read/write selector of a MemAlign row; the memory-bus tuple uses it to
choose `MEMORY_STORE_OP` or `MEMORY_LOAD_OP`. Breaking its booleanity to
`{0, p-1}` lets a row be neither a load nor a store on the bus.
